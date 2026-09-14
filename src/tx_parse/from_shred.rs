//! 从 shred 流解析。
//!
//! 输入是从 UDP shred 包里解出的 `VersionedTransaction` + slot。
//! 与另外两个来源的本质差异：
//!
//! - **没有 meta**：shred 是出块前的原始数据，交易还没执行，
//!   因此拿不到 `inner_instructions` / `log_messages` / 余额变化。
//!   这些信息要么等交易上链后从 grpc/rpc 补，要么在本地执行器里自行推导。
//! - **v0 的 ALT 需要查链**：消息里只有 ALT 的 pubkey 和索引，
//!   真实地址得去链上取（走 [`crate::get_or_fetch_alt`]，有缓存）。
//! - **V1 不需要查链**：V1 不支持 ALT，账户全内联在消息里。
//!
//! ## 能产出什么
//!
//! 只产出 `instructions`（无内部指令、无 logevent）和 `account_keys`。
//! 下游若要余额变化，需要自行根据指令语义推导，或等交易落块后二次拉取。

use solana_sdk::transaction::VersionedTransaction;

use super::common::{ParseError, ParsedTx};
use crate::flatten_main_instructions;

/// 从 shred 交易解析出统一结果。
///
/// `slot` 来自 shred 包头（前 8 字节小端 u64），由调用方一并传入。
///
/// 由于没有 meta，返回的 `ParsedTx` 中：
/// - `instructions` 只含主指令（索引为 `"0"`、`"1"`…，沿用既有行为）
/// - 不含 inner / logevent
pub async fn parse_shred_tx(tx: &VersionedTransaction, slot: u64) -> Result<ParsedTx, ParseError> {
    // 复用既有实现：它已处理 Legacy / V0 / V1 三种消息，
    // 并在 v0 时按需查链解析 ALT。
    let instructions = flatten_main_instructions(tx, slot)
        .await
        .map_err(|_| ParseError::Unsupported("failed to flatten shred transaction"))?;

    // account_keys 单独取一份，供下游按索引查账户。
    // 注意：v0 的 ALT 地址在 `flatten_main_instructions` 内部解析，
    // 这里为了不重复查链，仅返回静态账户 + （若有）已缓存结果。
    let account_keys = static_and_cached_keys(tx).await;

    // config 提取不需要 meta——V1 从消息 config 读，V0/Legacy 扫指令。
    // 这正是 shred 路径能拿到 compute budget 的原因。
    let config = super::common::tx_config_of(&tx.message, tx.message.instructions(), &account_keys);

    // shred 是出块前的原始数据，交易尚未执行，因此拿不到余额变化。
    // None 表示"来源不提供"，区别于 Some(vec![]) 的"执行了但没变化"。
    let balance_changes = None;

    // V1 的 config 不在指令里，伪装成指令塞回去，让基于指令匹配的下游零改动。
    let mut parsed = ParsedTx {
        slot,
        account_keys,
        instructions,
        config,
        balance_changes,
    };
    super::common::inject_v1_config_as_instructions(&mut parsed);

    Ok(parsed)
}

/// 取 shred 交易的完整账户列表。
///
/// - Legacy / V1：直接返回全部账户（V1 不支持 ALT，全部内联）。
/// - V0：静态账户 + 逐个 ALT 查链解析出的 writable/readonly。
///   ALT 有缓存，重复调用不会放大 RPC 压力。
async fn static_and_cached_keys(tx: &VersionedTransaction) -> Vec<solana_sdk::pubkey::Pubkey> {
    use solana_sdk::message::VersionedMessage;
    use solana_sdk::pubkey::Pubkey;

    match &tx.message {
        VersionedMessage::Legacy(m) => m.account_keys.clone(),
        VersionedMessage::V1(m) => m.account_keys.clone(),
        VersionedMessage::V0(m) => {
            let mut keys = m.account_keys.clone();
            let (mut writable, mut readonly) = (Vec::new(), Vec::new());
            for lookup in &m.address_table_lookups {
                let Ok(onchain) = crate::get_or_fetch_alt(lookup.account_key).await else {
                    writable.extend(lookup.writable_indexes.iter().map(|_| Pubkey::default()));
                    readonly.extend(lookup.readonly_indexes.iter().map(|_| Pubkey::default()));
                    continue;
                };
                for i in &lookup.writable_indexes {
                    writable.push(*onchain.get(*i as usize).unwrap_or(&Pubkey::default()));
                }
                for i in &lookup.readonly_indexes {
                    readonly.push(*onchain.get(*i as usize).unwrap_or(&Pubkey::default()));
                }
            }
            keys.extend(writable);
            keys.extend(readonly);
            keys
        }
    }
}
