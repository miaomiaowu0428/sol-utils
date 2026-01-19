use bs58;
use solana_client::rpc_response::OptionSerializer;
use solana_sdk::pubkey::Pubkey;
use solana_transaction_status_client_types::{
    EncodedConfirmedTransactionWithStatusMeta, EncodedTransaction,
    EncodedTransactionWithStatusMeta, UiAddressTableLookup, UiCompiledInstruction, UiInstruction,
    UiMessage, UiRawMessage, UiTransaction, UiTransactionStatusMeta, UiTransactionTokenBalance,
};
use std::{collections::HashMap, str::FromStr};

use crate::{IndexedInstruction, get_or_fetch_alt};

pub async fn accounts_of(message: &UiRawMessage) -> Vec<Pubkey> {
    let mut account_keys: Vec<_> = message
        .account_keys
        .iter()
        .map(|k_s| Pubkey::from_str(&k_s).unwrap())
        .collect();

    if let Some(address_table_lookups) = &message.address_table_lookups {
        let mut alt_realonly: Vec<Pubkey> = vec![];
        let mut alt_writable: Vec<Pubkey> = vec![];
        for UiAddressTableLookup {
            account_key,
            writable_indexes,
            readonly_indexes,
        } in address_table_lookups
        {
            let Ok(alt_onchain) = get_or_fetch_alt(Pubkey::from_str(&account_key).unwrap()).await
            else {
                for _ in readonly_indexes {
                    alt_realonly.push(Pubkey::default())
                }
                for _ in writable_indexes {
                    alt_writable.push(Pubkey::default())
                }
                continue;
            };
            for i in readonly_indexes {
                alt_realonly.push(*alt_onchain.get(*i as usize).unwrap_or(&Pubkey::default()))
            }
            for i in writable_indexes {
                alt_writable.push(*alt_onchain.get(*i as usize).unwrap_or(&Pubkey::default()))
            }
        }
        account_keys.extend(alt_writable);
        account_keys.extend(alt_realonly);
    }
    account_keys
}

pub async fn parse_fetched_json(
    EncodedConfirmedTransactionWithStatusMeta {
        slot,
        transaction,
        block_time: _block_time,
    }: EncodedConfirmedTransactionWithStatusMeta,
) -> Vec<IndexedInstruction> {
    // println!("{transaction:#?}");
    let EncodedTransactionWithStatusMeta {
        transaction, meta, ..
    } = transaction;
    let EncodedTransaction::Json(UiTransaction { message, .. }) = transaction else {
        return vec![];
    };
    let UiMessage::Raw(message) = message else {
        return vec![];
    };

    let Some(OptionSerializer::Some(inner_ixs)) = meta.map(|meta| meta.inner_instructions) else {
        return vec![];
    };
    let inner_ixs: HashMap<_, _> = inner_ixs
        .into_iter()
        .map(|item| (item.index, item.instructions))
        .collect();

    let mut account_keys: Vec<_> = accounts_of(&message).await;

    let mut res = vec![];
    for (index, ix) in message.instructions.into_iter().enumerate() {
        res.push(IndexedInstruction {
            index: index.to_string(),
            instruction: crate::ParsedInstruction {
                program: account_keys[ix.program_id_index as usize],
                accounts: ix
                    .accounts
                    .iter()
                    .map(|index| account_keys[*index as usize])
                    .collect(),
                data: bs58::decode(ix.data).into_vec().unwrap(),
                slot,
            },
            slot,
        });
        if let Some(inner_ixs) = inner_ixs.get(&(index as u8)) {
            for (inner_index, ix) in inner_ixs.iter().enumerate() {
                let UiInstruction::Compiled(UiCompiledInstruction {
                    program_id_index,
                    accounts,
                    data,
                    ..
                }) = ix
                else {
                    continue;
                };
                res.push(IndexedInstruction {
                    index: format!("{index}.{inner_index}"),
                    instruction: crate::ParsedInstruction {
                        program: account_keys[*program_id_index as usize],
                        accounts: accounts
                            .iter()
                            .map(|index| account_keys[*index as usize])
                            .collect(),
                        data: bs58::decode(data).into_vec().unwrap(),
                        slot,
                    },
                    slot,
                });
            }
        }
    }
    res
}

#[derive(Debug, Clone)]
pub struct BalanceChange {
    owner: Pubkey,
    mint: Pubkey,
    pre_balance: u64,
    after_balance: u64,
    change: i128,
    decimal: u8,
}




pub async fn balance_change_of(
    EncodedConfirmedTransactionWithStatusMeta {
        slot: _slot,
        transaction,
        block_time: _block_time,
    }: EncodedConfirmedTransactionWithStatusMeta,
) -> Result<Vec<BalanceChange>, String> {
    let EncodedTransactionWithStatusMeta {
        transaction,
        meta:
            Some(UiTransactionStatusMeta {
                pre_balances,
                post_balances,
                pre_token_balances,
                post_token_balances,
                ..
            }),
        ..
    } = transaction
    else {
        return Err("meta not found".into());
    };

    let mut changes = Vec::new();

    // ===============================
    // 解析 account keys
    // ===============================

    let EncodedTransaction::Json(UiTransaction { message, .. }) = transaction else {
        return Err("UiTransactionNotFound".into());
    };

    let UiMessage::Raw(message) = message else {
        return Err("UiRawMessageNotFound".into());
    };

    let account_keys = accounts_of(&message).await;

    // ===============================
    // 1️⃣ SOL balance changes
    // ===============================

    for (i, pre) in pre_balances.iter().enumerate() {
        let post = post_balances[i];

        if pre != &post {
            let change = post as i128 - *pre as i128;

            changes.push(BalanceChange {
                owner: account_keys[i],
                mint: Pubkey::default(), // SOL
                pre_balance: *pre,
                after_balance: post,
                change,
                decimal: 9,
            });
        }
    }

    // ===============================
    // 2️⃣ SPL Token balance changes
    // ===============================

    let mut pre_map: HashMap<(Pubkey, Pubkey), &UiTransactionTokenBalance> = HashMap::new();
    let mut post_map: HashMap<(Pubkey, Pubkey), &UiTransactionTokenBalance> = HashMap::new();

    if let OptionSerializer::Some(pre_tokens) = &pre_token_balances {
        for tb in pre_tokens {
            let owner = tb
                .owner
                .as_ref()
                .ok_or("token owner missing")?
                .parse::<Pubkey>()
                .map_err(|e| e.to_string())?;

            let mint = tb.mint.parse::<Pubkey>().map_err(|e| e.to_string())?;
            pre_map.insert((owner, mint), tb);
        }
    }

    if let OptionSerializer::Some(post_tokens) = &post_token_balances {
        for tb in post_tokens {
            let owner = tb
                .owner
                .as_ref()
                .ok_or("token owner missing")?
                .parse::<Pubkey>()
                .map_err(|e| e.to_string())?;

            let mint = tb.mint.parse::<Pubkey>().map_err(|e| e.to_string())?;
            post_map.insert((owner, mint), tb);
        }
    }

    for ((owner, mint), post) in post_map {
        let pre_amount: u64 = pre_map
            .get(&(owner, mint))
            .and_then(|tb| tb.ui_token_amount.amount.parse::<u64>().ok())
            .unwrap_or(0);

        let post_amount: u64 = post
            .ui_token_amount
            .amount
            .parse::<u64>()
            .map_err(|e| e.to_string())?;

        if pre_amount != post_amount {
            let change = post_amount as i128 - pre_amount as i128;

            changes.push(BalanceChange {
                owner,
                mint,
                pre_balance: pre_amount,
                after_balance: post_amount,
                change,
                decimal: post.ui_token_amount.decimals,
            });
        }
    }

    Ok(changes)
}
