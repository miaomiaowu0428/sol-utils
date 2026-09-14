//! `UiTransactionStatusMeta` → 官方 `TransactionStatusMeta` 的转型。
//!
//! # 为什么需要这个
//!
//! RPC 路径拿到的是 `UiTransactionStatusMeta`（JSON 友好版，用 `String`
//! 存公钥、`OptionSerializer` 表达"无值"），而 gRPC 路径拿到的直接是官方
//! `TransactionStatusMeta`。为了让两条路径能共用同一套余额变化计算，
//! 需要把 UI 版还原成官方版。
//!
//! # 官方只提供单向转换
//!
//! `solana-transaction-status` 里有 `TransactionStatusMeta → UiTransactionStatusMeta`
//! （用于 RPC 序列化），但**没有反向**。所以这里手写反向。
//!
//! 唯一的例外是错误类型：[`UiTransactionError`] 内部就是
//! `TransactionError` 的 newtype 包装，官方提供了 `From<UiTransactionError>`
//! 反向转换，所以那一步是无损的。
//!
//! # 性能
//!
//! 这个转换涉及字符串解析（`Pubkey::from_str`）和 base64 解码，
//! 比直接读 gRPC 的官方 meta 慢。但调用场景（交易已落块、事后分析）
//! 对性能不敏感，换来的是"两条路径共用一套逻辑"的简洁性。
//!
//! # 可能丢失的信息
//!
//! - `UiInstruction::Parsed`（已解析的指令）**无法还原**成 `CompiledInstruction`
//!   （原始字节已丢失）。这里只能跳过这类内部指令，并在返回值里标记。
//! - `return_data` 的编码假定为 base64（`UiReturnDataEncoding` 目前
//!   只有这一个变体）。

use solana_sdk::message::compiled_instruction::CompiledInstruction;
use solana_sdk::pubkey::Pubkey;
use solana_transaction_context::transaction::TransactionReturnData;
use solana_transaction_error::TransactionError;
use solana_transaction_status::{
    InnerInstruction, InnerInstructions, Reward, TransactionStatusMeta, TransactionTokenBalance, UiInnerInstructions,
    UiInstruction, UiTransactionStatusMeta, UiTransactionTokenBalance,
};
use std::str::FromStr;

use super::common::ParseError;

/// 转型过程中的非致命问题（信息无法完整还原）。
#[derive(Debug, Default)]
pub struct UiMetaConversionNotes {
    /// 有多少条内部指令因为处于 `UiInstruction::Parsed` 形态而无法还原。
    ///
    /// 这不是错误——`Parsed` 形态的原始指令字节在 JSON 里就不存在，
    /// 属于数据本身的信息缺失。多数 RPC 返回的是 `Compiled` 形态。
    pub skipped_parsed_inner_instructions: usize,
}

/// 把 RPC 的 `UiTransactionStatusMeta` 转成官方 `TransactionStatusMeta`。
///
/// 返回 `(官方 meta, 转换备注)`。备注用于让调用方知道是否有信息损失
/// （便于排查"为什么内部指令少了"这类问题）。
pub fn ui_meta_to_official(ui: &UiTransactionStatusMeta) -> Result<(TransactionStatusMeta, UiMetaConversionNotes), ParseError> {
    let mut notes = UiMetaConversionNotes::default();

    let status = match &ui.err {
        None => Ok(()),
        Some(e) => Err(TransactionError::from(e.clone())),
    };

    // OptionSerializer<T> → Option<T> 的取值惯例：
    // - Some(v)     → 有值
    // - None        → 序列化时被跳过（等同于"没这个字段"）
    // - Skip        → 调用方明确表示不要这个字段
    // 后两者对"无值"的语义等价，统一当作 None 处理。

    let inner_instructions = match &ui.inner_instructions {
        solana_client::rpc_response::OptionSerializer::Some(groups) => {
            let mut out = Vec::with_capacity(groups.len());
            for g in groups {
                let ixs = convert_inner_instructions(g, &mut notes);
                out.push(InnerInstructions {
                    index: g.index,
                    instructions: ixs,
                });
            }
            Some(out)
        }
        _ => None,
    };

    let log_messages = match &ui.log_messages {
        solana_client::rpc_response::OptionSerializer::Some(v) => Some(v.clone()),
        _ => None,
    };

    let pre_token_balances = match &ui.pre_token_balances {
        solana_client::rpc_response::OptionSerializer::Some(v) => Some(convert_token_balances(v)?),
        _ => None,
    };

    let post_token_balances = match &ui.post_token_balances {
        solana_client::rpc_response::OptionSerializer::Some(v) => Some(convert_token_balances(v)?),
        _ => None,
    };

    let rewards = match &ui.rewards {
        solana_client::rpc_response::OptionSerializer::Some(v) => {
            Some(v.iter().map(convert_reward).collect::<Vec<_>>())
        }
        _ => None,
    };

    let loaded_addresses = match &ui.loaded_addresses {
        solana_client::rpc_response::OptionSerializer::Some(la) => {
            let mut writable = Vec::with_capacity(la.writable.len());
            for s in &la.writable {
                writable.push(Pubkey::from_str(s).map_err(|_| ParseError::BadBytes("loaded writable address"))?);
            }
            let mut readonly = Vec::with_capacity(la.readonly.len());
            for s in &la.readonly {
                readonly.push(Pubkey::from_str(s).map_err(|_| ParseError::BadBytes("loaded readonly address"))?);
            }
            solana_sdk::message::v0::LoadedAddresses { writable, readonly }
        }
        _ => Default::default(),
    };

    let return_data = match &ui.return_data {
        solana_client::rpc_response::OptionSerializer::Some(rd) => {
            use base64::Engine;
            let program_id = Pubkey::from_str(&rd.program_id).map_err(|_| ParseError::BadBytes("return data program id"))?;
            let (encoded, _enc) = &rd.data;
            let data = base64::prelude::BASE64_STANDARD
                .decode(encoded)
                .map_err(|_| ParseError::BadBytes("return data base64"))?;
            Some(TransactionReturnData { program_id, data })
        }
        _ => None,
    };

    let compute_units_consumed = match &ui.compute_units_consumed {
        solana_client::rpc_response::OptionSerializer::Some(v) => Some(*v),
        _ => None,
    };

    let cost_units = match &ui.cost_units {
        solana_client::rpc_response::OptionSerializer::Some(v) => Some(*v),
        _ => None,
    };

    Ok((
        TransactionStatusMeta {
            status,
            fee: ui.fee,
            pre_balances: ui.pre_balances.clone(),
            post_balances: ui.post_balances.clone(),
            inner_instructions,
            log_messages,
            pre_token_balances,
            post_token_balances,
            rewards,
            loaded_addresses,
            return_data,
            compute_units_consumed,
            cost_units,
        },
        notes,
    ))
}

/// 转换一组内部指令，跳过无法还原的 `Parsed` 形态。
fn convert_inner_instructions(
    g: &UiInnerInstructions,
    notes: &mut UiMetaConversionNotes,
) -> Vec<InnerInstruction> {
    let mut out = Vec::with_capacity(g.instructions.len());
    for ix in &g.instructions {
        match ix {
            UiInstruction::Compiled(c) => {
                use base64::Engine as _;
                // UiCompiledInstruction.data 是 base58 编码（不是 base64）。
                let data = bs58::decode(&c.data).into_vec().unwrap_or_default();
                out.push(InnerInstruction {
                    instruction: CompiledInstruction {
                        program_id_index: c.program_id_index,
                        accounts: c.accounts.clone(),
                        data,
                    },
                    stack_height: c.stack_height,
                });
            }
            UiInstruction::Parsed(_) => {
                // 原始字节在 JSON 里已丢失，无法还原。
                notes.skipped_parsed_inner_instructions += 1;
            }
        }
    }
    out
}

/// 转换 token 余额列表。
///
/// 主要工作是把 `mint`/`owner` 字符串解析成 `Pubkey`。
fn convert_token_balances(v: &[UiTransactionTokenBalance]) -> Result<Vec<TransactionTokenBalance>, ParseError> {
    let mut out = Vec::with_capacity(v.len());
    for b in v {
        let owner = match &b.owner {
            solana_client::rpc_response::OptionSerializer::Some(s) => s.clone(),
            _ => String::new(),
        };
        let program_id = match &b.program_id {
            solana_client::rpc_response::OptionSerializer::Some(s) => s.clone(),
            _ => String::new(),
        };
        out.push(TransactionTokenBalance {
            account_index: b.account_index,
            mint: b.mint.clone(),
            ui_token_amount: b.ui_token_amount.clone(),
            owner,
            program_id,
        });
    }
    Ok(out)
}

/// 转换 reward。
fn convert_reward(r: &solana_transaction_status::Reward) -> Reward {
    Reward {
        pubkey: r.pubkey.clone(),
        lamports: r.lamports,
        post_balance: r.post_balance,
        reward_type: r.reward_type,
        commission: r.commission,
        commission_bps: r.commission_bps,
    }
}
