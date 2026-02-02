use std::collections::HashMap;

use solana_sdk::pubkey::Pubkey;

use crate::parse_rpc_fetched_json::BalanceChange;

/// 从 TransactionFormat 提取余额变化
/// 参考 utils::parse_rpc_fetched_json 的实现，但直接使用 TransactionFormat 的字段
pub fn balance_changes_of_grpc(
    tx: &grpc_client::TransactionFormat,
) -> Result<Vec<BalanceChange>, anyhow::Error> {
    use std::collections::HashSet;

    let Some(meta) = &tx.meta else {
        return Err(anyhow::anyhow!("meta not found"));
    };

    let account_keys = &tx.account_keys;

    // ===============================
    // 1 SOL balance diff
    // ===============================
    let mut sol_changes = Vec::new();
    for (i, owner) in account_keys.iter().enumerate() {
        let pre = *meta.pre_balances.get(i).unwrap_or(&0);
        let post = *meta.post_balances.get(i).unwrap_or(&0);

        if pre != post {
            sol_changes.push(BalanceChange {
                owner: *owner,
                mint: Pubkey::default(),
                token_account: Pubkey::default(),
                pre_balance: pre,
                after_balance: post,
                change: post as i128 - pre as i128,
                decimal: 9,
            });
        }
    }

    // ===============================
    // 2 Token balance diff
    // ===============================
    let mut token_changes = Vec::new();
    if let (Some(pre_tokens), Some(post_tokens)) =
        (&meta.pre_token_balances, &meta.post_token_balances)
    {
        let mut all_keys = HashSet::new();
        let mut pre_map: HashMap<(Pubkey, Pubkey), u64> = HashMap::new();
        let mut post_map: HashMap<(Pubkey, Pubkey), u64> = HashMap::new();
        let mut decimals_map: HashMap<(Pubkey, Pubkey), u8> = HashMap::new();
        let mut token_account_map: HashMap<(Pubkey, Pubkey), Pubkey> = HashMap::new();

        for tb in pre_tokens {
            let owner = tb.owner.parse::<Pubkey>()?;
            let mint = tb.mint.parse::<Pubkey>()?;
            let amount = tb.ui_token_amount.amount.parse::<u64>().unwrap_or(0);
            // try to resolve token account from account_index in TransactionFormat.account_keys
            let token_account = account_keys
                .get(tb.account_index as usize)
                .cloned()
                .unwrap_or_default();

            pre_map.insert((owner, mint), amount);
            decimals_map.insert((owner, mint), tb.ui_token_amount.decimals);
            token_account_map.insert((owner, mint), token_account);
            all_keys.insert((owner, mint));
        }

        for tb in post_tokens {
            let owner = tb.owner.parse::<Pubkey>()?;
            let mint = tb.mint.parse::<Pubkey>()?;
            let amount = tb.ui_token_amount.amount.parse::<u64>().unwrap_or(0);
            let token_account = account_keys
                .get(tb.account_index as usize)
                .cloned()
                .unwrap_or_default();

            post_map.insert((owner, mint), amount);
            decimals_map.insert((owner, mint), tb.ui_token_amount.decimals);
            token_account_map.insert((owner, mint), token_account);
            all_keys.insert((owner, mint));
        }

        for key in all_keys {
            let pre = *pre_map.get(&key).unwrap_or(&0);
            let post = *post_map.get(&key).unwrap_or(&0);
            let decimal = *decimals_map.get(&key).unwrap_or(&0);
            let token_account = token_account_map.get(&key).cloned().unwrap_or_default();

            if pre != post {
                token_changes.push(BalanceChange {
                    owner: key.0,
                    mint: key.1,
                    token_account,
                    pre_balance: pre,
                    after_balance: post,
                    change: post as i128 - pre as i128,
                    decimal,
                });
            }
        }
    }

    // ===============================
    // 3 合并结果
    // ===============================
    let mut changes = sol_changes;
    changes.extend(token_changes);

    Ok(changes)
}
