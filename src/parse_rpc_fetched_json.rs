use bs58;
use solana_client::rpc_response::OptionSerializer;
use solana_sdk::pubkey::Pubkey;
use solana_transaction_status_client_types::{
    EncodedConfirmedTransactionWithStatusMeta, EncodedTransaction,
    EncodedTransactionWithStatusMeta, UiAddressTableLookup, UiCompiledInstruction, UiInstruction,
    UiMessage, UiRawMessage, UiTransaction, UiTransactionStatusMeta, UiTransactionTokenBalance,
};
use std::{collections::{HashMap, HashSet}, str::FromStr};

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
    tx: impl Into<EncodedConfirmedTransactionWithStatusMeta>,
) -> Vec<IndexedInstruction> {
    let EncodedConfirmedTransactionWithStatusMeta {
        slot,
        transaction,
        block_time: _,
    } = tx.into();

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

#[derive(Debug, Clone, Default)]
pub struct BalanceChange {
    pub owner: Pubkey,
    pub mint: Pubkey,
    pub pre_balance: u64,
    pub after_balance: u64,
    pub change: i128,
    pub decimal: u8,
}

impl BalanceChange {
    pub fn combine(&self, other: &BalanceChange) -> BalanceChange {
        assert_eq!(self.owner, other.owner);
        assert_eq!(self.decimal, other.decimal);
        BalanceChange {
            owner: self.owner,
            mint: self.mint,
            pre_balance: self.pre_balance + other.pre_balance,
            after_balance: self.after_balance + other.after_balance,
            change: self.change + other.change,
            decimal: self.decimal,
        }
    }
}

pub async fn balance_change_of(
    tx: impl Into<EncodedConfirmedTransactionWithStatusMeta>,
) -> Result<Vec<BalanceChange>, String> {
    let EncodedConfirmedTransactionWithStatusMeta {
        slot,
        transaction,
        block_time: _,
    } = tx.into();
    // ===============================
    // 1 拿 meta
    // ===============================
    let EncodedTransactionWithStatusMeta {
        transaction,
        meta: Some(meta),
        ..
    } = transaction
    else {
        return Err("meta not found".into());
    };

    // ===============================
    // 2 解析 account keys
    // ===============================
    let EncodedTransaction::Json(UiTransaction { message, .. }) = transaction else {
        return Err("UiTransactionNotFound".into());
    };

    let UiMessage::Raw(message) = message else {
        return Err("UiRawMessageNotFound".into());
    };

    let account_keys = accounts_of(&message).await;

    // ===============================
    // 3 SOL balance diff
    // ===============================
    let sol_changes = diff_sol_balances(SolBalanceInput {
        owners: &account_keys,
        pre_balances: &meta.pre_balances,
        post_balances: &meta.post_balances,
    });

    // ===============================
    // 4 Token balance diff
    // ===============================
    let token_changes = if let (OptionSerializer::Some(pre), OptionSerializer::Some(post)) =
        (&meta.pre_token_balances, &meta.post_token_balances)
    {
        diff_token_balances(pre, post)?
    } else {
        Vec::new()
    };

    // ===============================
    // 5 合并结果
    // ===============================
    let changes = merge_balance_changes([sol_changes, token_changes]);

    Ok(changes)
}

pub struct SolBalanceInput<'a> {
    pub owners: &'a [Pubkey],
    pub pre_balances: &'a [u64],
    pub post_balances: &'a [u64],
}

pub fn diff_sol_balances(input: SolBalanceInput) -> Vec<BalanceChange> {
    let mut changes = Vec::new();

    for (i, owner) in input.owners.iter().enumerate() {
        let pre = *input.pre_balances.get(i).unwrap_or(&0);
        let post = *input.post_balances.get(i).unwrap_or(&0);

        if pre != post {
            changes.push(BalanceChange {
                owner: *owner,
                mint: Pubkey::default(),
                pre_balance: pre,
                after_balance: post,
                change: post as i128 - pre as i128,
                decimal: 9,
            });
        }
    }

    changes
}

pub fn diff_token_balances(
    pre_tokens: &[UiTransactionTokenBalance],
    post_tokens: &[UiTransactionTokenBalance],
) -> Result<Vec<BalanceChange>, String> {
    let mut changes = Vec::new();

    let mut all_keys = HashSet::new();
    let mut pre_map: HashMap<(Pubkey, Pubkey), u64> = HashMap::new();
    let mut post_map: HashMap<(Pubkey, Pubkey), u64> = HashMap::new();
    let mut decimals_map: HashMap<(Pubkey, Pubkey), u8> = HashMap::new();

    for tb in pre_tokens {
        let owner = tb.owner.as_ref().ok_or("token owner missing")?.parse::<Pubkey>().map_err(|e| e.to_string())?;
        let mint = tb.mint.parse::<Pubkey>().map_err(|e| e.to_string())?;
        let amount = tb.ui_token_amount.amount.parse::<u64>().unwrap_or(0);
        pre_map.insert((owner, mint), amount);
        decimals_map.insert((owner, mint), tb.ui_token_amount.decimals);
        all_keys.insert((owner, mint));
    }

    for tb in post_tokens {
        let owner = tb.owner.as_ref().ok_or("token owner missing")?.parse::<Pubkey>().map_err(|e| e.to_string())?;
        let mint = tb.mint.parse::<Pubkey>().map_err(|e| e.to_string())?;
        let amount = tb.ui_token_amount.amount.parse::<u64>().unwrap_or(0);
        post_map.insert((owner, mint), amount);
        decimals_map.insert((owner, mint), tb.ui_token_amount.decimals);
        all_keys.insert((owner, mint));
    }

    for key in all_keys {
        let pre = *pre_map.get(&key).unwrap_or(&0);
        let post = *post_map.get(&key).unwrap_or(&0);
        let decimal = *decimals_map.get(&key).unwrap_or(&0);

        if pre != post {
            changes.push(BalanceChange {
                owner: key.0,
                mint: key.1,
                pre_balance: pre,
                after_balance: post,
                change: post as i128 - pre as i128,
                decimal,
            });
        }
    }

    Ok(changes)
}


pub fn merge_balance_changes<I>(parts: I) -> Vec<BalanceChange>
where
    I: IntoIterator<Item = Vec<BalanceChange>>,
{
    let mut result = Vec::new();

    for mut part in parts {
        result.append(&mut part);
    }

    result
}

pub fn collect_balance_changes(
    sol: Vec<BalanceChange>,
    token: Vec<BalanceChange>,
) -> Vec<BalanceChange> {
    merge_balance_changes([sol, token])
}
