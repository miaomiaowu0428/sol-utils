use dotenvy::dotenv;
use solana_client::rpc_config::RpcTransactionConfig;
use solana_sdk::signature::Signature;
use solana_transaction_status_client_types::UiTransactionEncoding;
use std::str::FromStr;
use utils::{JSON_RPC_CLIENT, parse_rpc_fetched_json::parse_fetched_json};

#[tokio::main]
async fn main() {
    dotenv().ok();
    let sig = Signature::from_str(
        "3xrvumh3qqi9bibCdtB6HSubbyEw7BcRJ36qqksaRWY2G2rZtKnfZbzjmBg8LBDWS9TvKPsQi4LbkH5FKcgjoQuK",
    )
    .unwrap();
    println!("fetching tx: {}", sig.to_string());

    let tx_input = JSON_RPC_CLIENT
        .get_transaction_with_config(
            &sig,
            RpcTransactionConfig {
                encoding: Some(UiTransactionEncoding::Json),
                commitment: None,
                max_supported_transaction_version: Some(0),
            },
        )
        .await
        .unwrap();

    // 2. 调用待测试的函数
    let result = parse_fetched_json(tx_input).await;

    println!("{:#?}", result)
}
