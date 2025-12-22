use bs58;
use solana_client::rpc_response::OptionSerializer;
use solana_sdk::pubkey::Pubkey;
use solana_transaction_status_client_types::{
    EncodedConfirmedTransactionWithStatusMeta, EncodedTransaction,
    EncodedTransactionWithStatusMeta, UiAddressTableLookup, UiCompiledInstruction, UiInstruction,
    UiMessage, UiTransaction,
};
use std::{collections::HashMap, str::FromStr};

use crate::{IndexedInstruction, get_or_fetch_alt};

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

    let mut account_keys: Vec<_> = message
        .account_keys
        .iter()
        .map(|k_s| Pubkey::from_str(&k_s).unwrap())
        .collect();

    if let Some(address_table_lookups) = message.address_table_lookups {
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
                alt_realonly.push(*alt_onchain.get(i as usize).unwrap_or(&Pubkey::default()))
            }
            for i in writable_indexes {
                alt_writable.push(*alt_onchain.get(i as usize).unwrap_or(&Pubkey::default()))
            }
        }
        account_keys.extend(alt_writable);
        account_keys.extend(alt_realonly);
    }
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
