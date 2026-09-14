//! 从 geyser gRPC 交易解析。
//!
//! 输入是 `grpc_client::TransactionFormat`，它已经做过一次搬运：
//! - `transaction`: 组装好的 solana 原生 `VersionedTransaction`
//! - `meta`: 官方 `solana_transaction_status::TransactionStatusMeta`
//!
//! 因此这条路径信息最全：**ALT 加载的地址可以直接从 meta 拿**，
//! 不需要额外查链。

use grpc_client::TransactionFormat;
use solana_sdk::message::compiled_instruction::CompiledInstruction;
use solana_sdk::pubkey::Pubkey;

use super::common::{
    account_keys_of, balance_changes_of, flatten_instructions_with_keys, inject_v1_config_as_instructions, tx_config_of,
    ParseError, ParsedTx,
};

/// 从 gRPC 交易解析出统一结果。
///
/// 相比其它两个来源，这条路径不需要额外 IO：ALT 地址直接来自
/// `meta.loaded_addresses`。
pub fn parse_grpc_tx(tx: &TransactionFormat) -> Result<ParsedTx, ParseError> {
    let loaded = tx.meta.as_ref().map(|m| &m.loaded_addresses).cloned().unwrap_or_default();

    let account_keys = account_keys_of(&tx.transaction.message, &loaded.writable, &loaded.readonly);

    let inner: Vec<(usize, Vec<CompiledInstruction>)> = tx
        .meta
        .as_ref()
        .and_then(|m| m.inner_instructions.as_ref())
        .map(|groups| {
            groups
                .iter()
                .map(|g| {
                    let ixs = g
                        .instructions
                        .iter()
                        .map(|i| CompiledInstruction {
                            program_id_index: i.instruction.program_id_index,
                            accounts: i.instruction.accounts.clone(),
                            data: i.instruction.data.clone(),
                        })
                        .collect();
                    (g.index as usize, ixs)
                })
                .collect()
        })
        .unwrap_or_default();

    let logs = tx.meta.as_ref().and_then(|m| m.log_messages.as_deref());

    let main_ixs = tx.transaction.message.instructions();
    let instructions = flatten_instructions_with_keys(main_ixs, &inner, logs, &account_keys, tx.slot);

    // V1 的 compute budget 在消息 config 里，不在指令里；
    // V0/Legacy 则要扫 ComputeBudgetProgram 指令。
    let config = tx_config_of(&tx.transaction.message, main_ixs, &account_keys);

    // 余额变化：gRPC 的 meta 已是官方类型，直接算。
    let balance_changes = tx.meta.as_ref().map(|m| balance_changes_of(m, &account_keys));

    // V1 的 config 不在指令里，伪装成指令塞回去，让基于指令匹配的下游零改动。
    let mut parsed = ParsedTx {
        slot: tx.slot,
        account_keys,
        instructions,
        config,
        balance_changes,
    };
    inject_v1_config_as_instructions(&mut parsed);

    Ok(parsed)
}

/// 从 gRPC 交易的 meta 取 ALT 加载的地址（供需要单独使用的场景）。
pub fn loaded_addresses_of(tx: &TransactionFormat) -> (Vec<Pubkey>, Vec<Pubkey>) {
    match tx.meta.as_ref() {
        Some(m) => (m.loaded_addresses.writable.clone(), m.loaded_addresses.readonly.clone()),
        None => (Vec::new(), Vec::new()),
    }
}
