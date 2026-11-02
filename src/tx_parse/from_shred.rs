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
use crate::flatten_main_instructions_with_keys;

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
    //
    // ⚠️ 用 `_with_keys` 版本：展平本来就顺手算出了完整账户列表（v0 的 ALT
    // 也在里面解析过了）。旧写法先展平、再 `static_and_cached_keys` 克隆一遍
    // 静态账户并重新遍历 ALT——同一份 key 列表算两遍，还要多拷一整份 Vec。
    let (instructions, account_keys) = flatten_main_instructions_with_keys(tx, slot)
        .await
        .map_err(|_| ParseError::Unsupported("failed to flatten shred transaction"))?;

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

