//! 从 geyser gRPC 交易解析。
//!
//! 输入是 `grpc_client::TransactionFormat`，它已经做过一次搬运：
//! - `transaction`: 组装好的 solana 原生 `VersionedTransaction`
//! - `meta`: 官方 `solana_transaction_status::TransactionStatusMeta`
//!
//! 因此这条路径信息最全：**ALT 加载的地址可以直接从 meta 拿**，
//! 不需要额外查链。

use grpc_client::TransactionFormat;
use solana_sdk::pubkey::Pubkey;

use super::common::{
    account_keys_of, balance_changes_of, flatten_with_inner, inject_v1_config_as_instructions, tx_config_of, ParseError,
    ParseOptions, ParsedTx,
};

/// 从 gRPC 交易解析出统一结果（全量：含余额变化）。
///
/// 相比其它两个来源，这条路径不需要额外 IO：ALT 地址直接来自
/// `meta.loaded_addresses`。
pub fn parse_grpc_tx(tx: &TransactionFormat) -> Result<ParsedTx, ParseError> {
    parse_grpc_tx_with(tx, ParseOptions::default())
}

/// 同 [`parse_grpc_tx`]，但可以关掉可选产物。
///
/// 热路径（[`crate::flatten_instructions`]）用
/// [`ParseOptions::instructions_only`]：**不**算余额变化。
pub fn parse_grpc_tx_with(tx: &TransactionFormat, opts: ParseOptions) -> Result<ParsedTx, ParseError> {
    let meta = tx.meta.as_ref();

    // ALT 地址只是拿来拼账户列表：借引用即可，别 clone 两个 Vec。
    let (loaded_writable, loaded_readonly) = match meta {
        Some(m) => (m.loaded_addresses.writable.as_slice(), m.loaded_addresses.readonly.as_slice()),
        None => (&[][..], &[][..]),
    };
    let account_keys = account_keys_of(&tx.transaction.message, loaded_writable, loaded_readonly);

    let main_ixs = tx.transaction.message.instructions();
    let logs = meta.and_then(|m| m.log_messages.as_deref());

    // 内部指令直接借用 meta 里的那份：旧实现会先深拷贝成 `Vec<CompiledInstruction>`
    // （每条内部指令复制一遍 accounts + data），只为统一类型。
    let inner_groups = meta.and_then(|m| m.inner_instructions.as_deref()).unwrap_or(&[]);
    let instructions = flatten_with_inner(
        main_ixs,
        |parent| {
            inner_groups
                .iter()
                .find(|g| g.index as usize == parent)
                .map(|g| g.instructions.as_slice())
        },
        logs,
        &account_keys,
        tx.slot,
    );

    // V1 的 compute budget 在消息 config 里，不在指令里；
    // V0/Legacy 则要扫 ComputeBudgetProgram 指令。
    let config = tx_config_of(&tx.transaction.message, main_ixs, &account_keys);

    // 余额变化：gRPC 的 meta 已是官方类型，直接算——但本仓库没人读这个字段，
    // 热路径可以跳过（`ParseOptions::instructions_only`）。
    let balance_changes = if opts.balance_changes {
        meta.map(|m| balance_changes_of(m, &account_keys))
    } else {
        None
    };

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
