//! 从 RPC `getTransaction` 的 JSON 解析。
//!
//! 输入是 `EncodedConfirmedTransactionWithStatusMeta`（base58 编码的 JSON）。
//! 与 gRPC 路径的关键差异：
//!
//! - **消息体是 JSON 文本**，公钥/指令数据都是字符串，需要解码。
//! - **ALT 地址不在 meta 里**，需要按 `address_table_lookups` 去链上取
//!   （走 [`crate::get_or_fetch_alt`]，有缓存）。
//!   因此这个入口是 `async` 的，而 gRPC 入口是同步的。
//!
//! 索引规则沿用 `parse_rpc_fetched_json` 的既有行为（从 `0` 开始），
//! 保证已有下游不受影响。

use bs58;
use log::warn;
use solana_client::rpc_response::OptionSerializer;
use solana_sdk::message::compiled_instruction::CompiledInstruction;
use solana_sdk::pubkey::Pubkey;
use solana_transaction_status_client_types::{
    EncodedConfirmedTransactionWithStatusMeta, EncodedTransaction, EncodedTransactionWithStatusMeta, UiCompiledInstruction,
    UiInstruction, UiMessage, UiRawMessage, UiTransaction,
};
use std::str::FromStr;

use super::common::{ParseError, ParsedTx, TxConfig, scan_compute_budget};
use crate::{IndexedInstruction, ParsedInstruction, get_or_fetch_alt};

/// RPC 消息里 ALT 的解析结果：`(writable, readonly)`。
async fn resolve_alts(message: &UiRawMessage) -> (Vec<Pubkey>, Vec<Pubkey>) {
    let mut readonly_out: Vec<Pubkey> = Vec::new();
    let mut writable_out: Vec<Pubkey> = Vec::new();

    if let Some(lookups) = &message.address_table_lookups {
        for lookup in lookups {
            let Ok(alt_pubkey) = Pubkey::from_str(&lookup.account_key) else {
                continue;
            };
            let Ok(onchain) = get_or_fetch_alt(alt_pubkey).await else {
                // 取不到时用 default 占位，保持索引不错位。
                readonly_out.extend(lookup.readonly_indexes.iter().map(|_| Pubkey::default()));
                writable_out.extend(lookup.writable_indexes.iter().map(|_| Pubkey::default()));
                continue;
            };
            for i in &lookup.readonly_indexes {
                readonly_out.push(*onchain.get(*i as usize).unwrap_or(&Pubkey::default()));
            }
            for i in &lookup.writable_indexes {
                writable_out.push(*onchain.get(*i as usize).unwrap_or(&Pubkey::default()));
            }
        }
    }
    (writable_out, readonly_out)
}

/// 从 RPC 交易解析出统一结果。
///
/// 需要访问链上 ALT，所以是 `async`。
pub async fn parse_rpc_tx(tx: impl Into<EncodedConfirmedTransactionWithStatusMeta>) -> Result<ParsedTx, ParseError> {
    let EncodedConfirmedTransactionWithStatusMeta { slot, transaction, .. } = tx.into();
    let EncodedTransactionWithStatusMeta { transaction, meta, .. } = transaction;

    let EncodedTransaction::Json(UiTransaction { message, .. }) = transaction else {
        return Err(ParseError::Unsupported("non-json transaction encoding"));
    };
    let UiMessage::Raw(message) = message else {
        return Err(ParseError::Unsupported("parsed (non-raw) message"));
    };

    // 静态账户 + ALT 解析出的地址（顺序：静态 -> writable -> readonly）。
    let mut account_keys: Vec<Pubkey> = message
        .account_keys
        .iter()
        .map(|k| Pubkey::from_str(k).unwrap_or_default())
        .collect();
    let (alt_writable, alt_readonly) = resolve_alts(&message).await;
    let static_len = account_keys.len();
    account_keys.extend(alt_writable);
    account_keys.extend(alt_readonly);

    // 内部指令按父下标分组。
    let inner_map: std::collections::HashMap<u8, Vec<UiCompiledInstruction>> = match meta.as_ref().map(|m| &m.inner_instructions) {
        Some(OptionSerializer::Some(inner)) => inner
            .iter()
            .map(|item| {
                let ixs = item
                    .instructions
                    .iter()
                    .filter_map(|i| match i {
                        UiInstruction::Compiled(c) => Some(c.clone()),
                        _ => None,
                    })
                    .collect();
                (item.index, ixs)
            })
            .collect(),
        _ => Default::default(),
    };

    let log_msgs: Option<Vec<String>> = meta.as_ref().and_then(|m| match &m.log_messages {
        OptionSerializer::Some(v) => Some(v.clone()),
        _ => None,
    });

    let mut instructions = Vec::new();

    for (index, ix) in message.instructions.iter().enumerate() {
        instructions.push(IndexedInstruction {
            index: index.to_string(),
            instruction: ParsedInstruction {
                program: account_keys.get(ix.program_id_index as usize).copied().unwrap_or_default(),
                accounts: ix
                    .accounts
                    .iter()
                    .map(|i| account_keys.get(*i as usize).copied().unwrap_or_default())
                    .collect(),
                data: bs58::decode(&ix.data).into_vec().unwrap_or_default(),
                slot,
            },
            slot,
        });

        if let Some(inner) = inner_map.get(&(index as u8)) {
            for (inner_index, ix) in inner.iter().enumerate() {
                instructions.push(IndexedInstruction {
                    index: format!("{index}.{inner_index}"),
                    instruction: ParsedInstruction {
                        program: account_keys
                            .get(ix.program_id_index as usize)
                            .copied()
                            .unwrap_or_default(),
                        accounts: ix
                            .accounts
                            .iter()
                            .map(|i| account_keys.get(*i as usize).copied().unwrap_or_default())
                            .collect(),
                        data: bs58::decode(&ix.data).into_vec().unwrap_or_default(),
                        slot,
                    },
                    slot,
                });
            }
        }
    }

    // 追加日志重建的假 CPI。
    if let Some(logs) = log_msgs.as_deref() {
        for (k, inst) in crate::log_events::parse_log_events(logs, slot).into_iter().enumerate() {
            instructions.push(IndexedInstruction {
                index: format!("logevent.{}", k + 1),
                instruction: inst,
                slot,
            });
        }
    }

    let _ = static_len; // 静态账户边界，后续需要区分时可展开使用。

    // config：RPC JSON 没有 V1 config 字段（V1 交易经 RPC 取回时
    // 会走 UiTransaction 的其他分支），这里按 V0/Legacy 处理——
    // 扫主指令里的 ComputeBudgetProgram。
    let compiled_main: Vec<CompiledInstruction> = message
        .instructions
        .iter()
        .map(|ix| CompiledInstruction {
            program_id_index: ix.program_id_index,
            accounts: ix.accounts.clone(),
            data: bs58::decode(&ix.data).into_vec().unwrap_or_default(),
        })
        .collect();
    let config = TxConfig {
        v1: None,
        compute_budget: scan_compute_budget(&compiled_main, &account_keys, &const_accounts::COMPUTE_BUDGET_PROGRAM),
    };

    // 余额变化：RPC 的 meta 是 UI 版，先还原成官方类型，
    // 再复用与 gRPC 路径同一套计算逻辑（见 ui_meta 模块的说明）。
    let balance_changes = match meta.as_ref() {
        Some(ui_meta) => match super::ui_meta::ui_meta_to_official(ui_meta) {
            Ok((official, _notes)) => Some(super::common::balance_changes_of(&official, &account_keys)),
            Err(e) => {
                warn!("ui_meta 转换失败，余额变化不可用: {e}");
                None
            }
        },
        None => None,
    };

    // V1 的 config 不在指令里，伪装成指令塞回去，让基于指令匹配的下游零改动。
    // （RPC 走 V1 交易时同样会命中这条路径。）
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
