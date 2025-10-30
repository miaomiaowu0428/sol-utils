use anyhow::anyhow;
// use borsh::BorshDeserialize;
use log::error;
use log::info;
use log::warn;
use serde::Deserialize;
use serde::Serialize;
// use sol_trade_sdk::trading::bonk::pool::Pool as BonkPool;
use solana_sdk::bs58;
use solana_sdk::hash::Hash;
use solana_sdk::message::compiled_instruction::CompiledInstruction;
use solana_sdk::pubkey;
use solana_sdk::pubkey::Pubkey;
use solana_sdk::signature::Signature;
use spl_associated_token_account::get_associated_token_address;
use ta::Close;
use ta::High;
use ta::Low;
use tokio::sync::RwLock;
use std::sync::LazyLock;
use std::time::{Duration, Instant};
use grpc_client::TransactionFormat;

pub mod macros;

pub trait SolToLamport {
    fn to_lamport(self) -> u64;
}

impl SolToLamport for f64 {
    fn to_lamport(self) -> u64 {
        (self * 1_000_000_000.0) as u64
    }
}

impl SolToLamport for f32 {
    fn to_lamport(self) -> u64 {
        (self * 1_000_000_000.0) as u64
    }
}

impl SolToLamport for u64 {
    fn to_lamport(self) -> u64 {
        self * 1_000_000_000
    }
}

impl SolToLamport for u32 {
    fn to_lamport(self) -> u64 {
        (self as u64) * 1_000_000_000
    }
}

impl SolToLamport for u16 {
    fn to_lamport(self) -> u64 {
        (self as u64) * 1_000_000_000
    }
}

impl SolToLamport for u8 {
    fn to_lamport(self) -> u64 {
        (self as u64) * 1_000_000_000
    }
}

impl SolToLamport for i64 {
    fn to_lamport(self) -> u64 {
        (self as u64).saturating_mul(1_000_000_000)
    }
}

impl SolToLamport for i32 {
    fn to_lamport(self) -> u64 {
        (self as u64).saturating_mul(1_000_000_000)
    }
}

/// USD1单位转换：1 USD1 = 1_000_000 单位
pub trait Usd1ToUsd1Unit {
    fn to_usd1_unit(self) -> u64;
}

impl Usd1ToUsd1Unit for f64 {
    fn to_usd1_unit(self) -> u64 {
        (self * 1_000_000.0) as u64
    }
}

impl Usd1ToUsd1Unit for f32 {
    fn to_usd1_unit(self) -> u64 {
        (self * 1_000_000.0) as u64
    }
}

impl Usd1ToUsd1Unit for u64 {
    fn to_usd1_unit(self) -> u64 {
        self * 1_000_000
    }
}

impl Usd1ToUsd1Unit for u32 {
    fn to_usd1_unit(self) -> u64 {
        (self as u64) * 1_000_000
    }
}

impl Usd1ToUsd1Unit for u16 {
    fn to_usd1_unit(self) -> u64 {
        (self as u64) * 1_000_000
    }
}

impl Usd1ToUsd1Unit for u8 {
    fn to_usd1_unit(self) -> u64 {
        (self as u64) * 1_000_000
    }
}

impl Usd1ToUsd1Unit for i64 {
    fn to_usd1_unit(self) -> u64 {
        (self as u64).saturating_mul(1_000_000)
    }
}

impl Usd1ToUsd1Unit for i32 {
    fn to_usd1_unit(self) -> u64 {
        (self as u64).saturating_mul(1_000_000)
    }
}

/// 全局缓存的 blockhash 及其获取时间
static BLOCKHASH_CACHE: LazyLock<RwLock<Option<(Hash, Instant)>>> =
    LazyLock::new(|| RwLock::new(None));

/// 获取（并自动缓存）最新 blockhash，30秒内重复调用直接返回缓存，失败自动重试3次
pub async fn get_cached_blockhash(
    json_rpc_client: &solana_client::nonblocking::rpc_client::RpcClient,
) -> Option<Hash> {
    {
        let cache = BLOCKHASH_CACHE.read().await;
        if let Some((hash, ts)) = &*cache {
            if ts.elapsed() < Duration::from_secs(30) {
                return Some(*hash);
            }
        }
    }
    // 超时或未缓存，重试获取
    let mut _last_err = None;
    for _ in 0..5 {
        match json_rpc_client.get_latest_blockhash().await {
            Ok(hash) => {
                let mut cache = BLOCKHASH_CACHE.write().await;
                *cache = Some((hash, Instant::now()));
                return Some(hash);
            }
            Err(e) => {
                _last_err = Some(e);
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }
    None
}

/// 获取指定 ATA 地址的 token 余额，如果账户不存在返回 None
pub async fn get_ata_balance(
    ata: &Pubkey,
    json_rpc_client: &solana_client::nonblocking::rpc_client::RpcClient,
) -> Option<u64> {
    let res = json_rpc_client.get_token_account_balance(ata);
    match res.await {
        Ok(balance) => Some(balance.amount.parse::<u64>().unwrap_or(0)),
        Err(e) => {
            // 如果是账户不存在，返回 None，否则可根据需要打印日志
            if let solana_client::client_error::ClientErrorKind::RpcError(
                solana_client::rpc_request::RpcError::ForUser(msg),
            ) = &*e.kind
            {
                if msg.contains("could not find account") || msg.contains("AccountNotFound") {
                    return None;
                }
            }
            None
        }
    }
}

/// 获取指定 ATA 地址的 token 余额和decimals，如果账户不存在返回 None
pub async fn get_ata_balance_with_decimal(
    ata: &Pubkey,
    json_rpc_client: &solana_client::nonblocking::rpc_client::RpcClient,
) -> Option<(u64, u8)> {
    let res = json_rpc_client.get_token_account_balance(ata);
    match res.await {
        Ok(balance) => {
            // 直接用返回的decimals字段
            Some((balance.amount.parse::<u64>().unwrap_or(0), balance.decimals))
        }
        Err(e) => {
            // 如果是账户不存在，返回 None，否则可根据需要打印日志
            if let solana_client::client_error::ClientErrorKind::RpcError(
                solana_client::rpc_request::RpcError::ForUser(msg),
            ) = &*e.kind
            {
                if msg.contains("could not find account") || msg.contains("AccountNotFound") {
                    return None;
                }
            }
            None
        }
    }
}

/// 获取 owner 的 mint 的 ATA 余额，如果 ATA 不存在返回 None
pub async fn get_token_balance(
    owner: &Pubkey,
    mint: &Pubkey,
    json_rpc_client: &solana_client::nonblocking::rpc_client::RpcClient,
) -> Option<(Pubkey, u64)> {
    let ata = get_associated_token_address(owner, mint);
    let balance = get_ata_balance(&ata, json_rpc_client).await;
    balance.map(|b| (ata, b))
}

pub async fn poll_transaction_confirmation(
    signature: solana_sdk::signature::Signature,
    json_rpc_client: &solana_client::nonblocking::rpc_client::RpcClient,
) -> Option<solana_sdk::signature::Signature> {
    const MAX_RETRIES: u32 = 30; // 最多轮询30次
    const POLL_INTERVAL_MS: u64 = 1000; // 每次间隔1秒

    for attempt in 1..=MAX_RETRIES {
        match json_rpc_client.get_signature_status(&signature).await {
            Ok(Some(status)) => match status {
                Ok(_) => {
                    return Some(signature);
                }
                Err(e) => {
                    error!("❌ Transaction {} failed with error: {}", signature, e);
                    return None;
                }
            },
            Ok(None) => {
                // 交易未找到，可能还在传播
                if attempt % 10 == 0 {
                    info!(
                        "🔍 Transaction {} not found yet (attempt {})",
                        signature, attempt
                    );
                }
            }
            Err(e) => {
                warn!(
                    "⚠️ Error checking transaction status: {} (attempt {})",
                    e, attempt
                );
            }
        }

        // 等待下次轮询
        tokio::time::sleep(tokio::time::Duration::from_millis(POLL_INTERVAL_MS)).await;
    }

    error!(
        "⏰ Transaction {} confirmation timed out after {} attempts",
        signature, MAX_RETRIES
    );
    None
}

pub trait ToSolscan {
    fn to_solscan(&self) -> String;
}

impl ToSolscan for Pubkey {
    fn to_solscan(&self) -> String {
        format!("https://solscan.io/account/{}", self)
    }
}

impl ToSolscan for Signature {
    fn to_solscan(&self) -> String {
        format!("https://solscan.io/tx/{}", self)
    }
}

pub enum GmgnType {
    Token,
    Address,
}

pub trait ToGmgn {
    fn to_gmgn(&self, ty: GmgnType) -> String;
}

impl ToGmgn for Pubkey {
    fn to_gmgn(&self, ty: GmgnType) -> String {
        match ty {
            GmgnType::Token => format!("https://gmgn.ai/sol/token/{}", self),
            GmgnType::Address => format!("https://gmgn.ai/sol/address/{}", self),
        }
    }
}

impl ToGmgn for str {
    fn to_gmgn(&self, ty: GmgnType) -> String {
        match ty {
            GmgnType::Token => format!("https://gmgn.ai/sol/token/{}", self),
            GmgnType::Address => format!("https://gmgn.ai/sol/address/{}", self),
        }
    }
}

impl ToGmgn for String {
    fn to_gmgn(&self, ty: GmgnType) -> String {
        self.as_str().to_gmgn(ty)
    }
}

#[test]
fn decode_sk() {
    decode_sk_file("../test-wallet.json");
}

/// 读取 base58 钱包文件，解码为 u8 数组并覆盖写回为 JSON 格式
pub fn decode_sk_file(path: &str) {
    use std::fs;
    use std::io::Write;
    let s = fs::read_to_string(path)
        .expect("read file")
        .trim()
        .to_string();
    let decoded = bs58::decode(s).into_vec().expect("base58 decode");
    let json = serde_json::to_string(&decoded).expect("to json");
    let mut file = fs::File::create(path).expect("create file");
    file.write_all(json.as_bytes()).expect("write file");
    println!("Decoded and wrote to {}: {} bytes", path, decoded.len());
}



#[derive(Debug, Clone)]
pub struct ParsedInstruction {
    pub program: solana_sdk::pubkey::Pubkey,
    pub accounts: Vec<solana_sdk::pubkey::Pubkey>,
    pub data: Vec<u8>,
    pub slot: u64,
}

#[derive(Debug, Clone)]
pub struct IndexedInstruction {
    pub index: String, // 如 "1", "1.1"
    pub instruction: ParsedInstruction,
    pub slot: u64,
}

pub fn flatten_instructions(tx: &TransactionFormat) -> Vec<IndexedInstruction> {
    use solana_sdk::pubkey::Pubkey;
    let mut result = Vec::new();

    // 获取主指令
    let main_instructions = tx.transation.message.instructions();
    let account_keys: Vec<Pubkey> = tx.account_keys.iter().cloned().collect();
    let mut inner_map = std::collections::HashMap::new();

    // 获取 slot 号
    let slot = tx.slot;

    // 收集内部指令
    if let Some(meta) = &tx.meta {
        if let Some(inner_instructions) = &meta.inner_instructions {
            for group in inner_instructions {
                inner_map.insert(group.index as usize, &group.instructions);
            }
        }
    }

    let parse_ix = |ix: &CompiledInstruction| {
        let program = account_keys
            .get(ix.program_id_index as usize)
            .cloned()
            .unwrap_or_default();
        let accounts = ix
            .accounts
            .iter()
            .filter_map(|&i| account_keys.get(i as usize).cloned())
            .collect();
        ParsedInstruction {
            program,
            accounts,
            data: ix.data.clone(),
            slot,
        }
    };

    for (i, main_ix) in main_instructions.iter().enumerate() {
        let idx = (i + 1).to_string();
        result.push(IndexedInstruction {
            index: idx.clone(),
            instruction: parse_ix(main_ix),
            slot,
        });

        if let Some(inner_vec) = inner_map.get(&i) {
            for (j, inner_ix) in inner_vec.iter().enumerate() {
                let sub_idx = format!("{}.{}", i + 1, j + 1);
                result.push(IndexedInstruction {
                    index: sub_idx,
                    instruction: parse_ix(&inner_ix.instruction),
                    slot,
                });
            }
        }
    }

    result
}

use chrono::{Datelike, FixedOffset, TimeZone};

#[derive(Debug, Clone, Copy)]
pub struct PoolPriceInfo {
    pub pool_address: Pubkey,
    pub base_mint: Pubkey,         // base币种mint
    pub quote_mint: Pubkey,        // quote币种mint
    pub base_reserve: u64,         // base币种池子余额
    pub quote_reserve: u64,        // quote币种池子余额
    pub base_price_in_quote: f64,  // 1个base币等于多少quote币
    pub last_updated: PoolTimeStr, // UTC、无年份、精确到0.xx秒
}

impl Low for PoolPriceInfo {
    fn low(&self) -> f64 {
        self.base_price_in_quote
    }
}

impl High for PoolPriceInfo {
    fn high(&self) -> f64 {
        self.base_price_in_quote
    }
}

impl Close for PoolPriceInfo {
    fn close(&self) -> f64 {
        self.base_price_in_quote
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoolTimeStr(pub u64); // 只存时间戳（秒）

impl PoolTimeStr {
    /// 生成当前 UTC 时间戳（秒）
    pub fn now_utc() -> Self {
        let now = chrono::Utc::now().timestamp() as u64;
        PoolTimeStr(now)
    }

    pub fn as_secs(&self) -> u64 {
        self.0
    }
}

use serde::{Deserializer, Serializer};

// Serialize/Deserialize trait 由 derive 自动实现

impl Serialize for PoolPriceInfo {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut s = serializer.serialize_struct("PoolPriceInfo", 7)?;
        s.serialize_field("pool_address", &self.pool_address.to_string())?;
        s.serialize_field("base_mint", &self.base_mint.to_string())?;
        s.serialize_field("quote_mint", &self.quote_mint.to_string())?;
        s.serialize_field("base_reserve", &self.base_reserve)?;
        s.serialize_field("quote_reserve", &self.quote_reserve)?;
        s.serialize_field("base_price_in_quote", &self.base_price_in_quote)?;
        s.serialize_field("last_updated", &self.last_updated)?;
        s.end()
    }
}

impl<'de> Deserialize<'de> for PoolPriceInfo {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use serde::de::{self, MapAccess, Visitor};
        use std::fmt;
        struct PoolPriceInfoVisitor;
        impl<'de> Visitor<'de> for PoolPriceInfoVisitor {
            type Value = PoolPriceInfo;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct PoolPriceInfo")
            }
            fn visit_map<V>(self, mut map: V) -> Result<PoolPriceInfo, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut pool_address = None;
                let mut base_mint = None;
                let mut quote_mint = None;
                let mut base_reserve = None;
                let mut quote_reserve = None;
                let mut base_price_in_quote = None;
                let mut last_updated = None;
                while let Some(key) = map.next_key::<&str>()? {
                    match key {
                        "pool_address" => {
                            let s: String = map.next_value()?;
                            pool_address = Some(s.parse::<Pubkey>().map_err(de::Error::custom)?);
                        }
                        "base_mint" => {
                            let s: String = map.next_value()?;
                            base_mint = Some(s.parse::<Pubkey>().map_err(de::Error::custom)?);
                        }
                        "quote_mint" => {
                            let s: String = map.next_value()?;
                            quote_mint = Some(s.parse::<Pubkey>().map_err(de::Error::custom)?);
                        }
                        "base_reserve" => base_reserve = Some(map.next_value()?),
                        "quote_reserve" => quote_reserve = Some(map.next_value()?),
                        "base_price_in_quote" => base_price_in_quote = Some(map.next_value()?),
                        "last_updated" => last_updated = Some(map.next_value()?),
                        _ => {
                            let _: serde::de::IgnoredAny = map.next_value()?;
                        }
                    }
                }
                Ok(PoolPriceInfo {
                    pool_address: pool_address
                        .ok_or_else(|| de::Error::missing_field("pool_address"))?,
                    base_mint: base_mint.ok_or_else(|| de::Error::missing_field("base_mint"))?,
                    quote_mint: quote_mint.ok_or_else(|| de::Error::missing_field("quote_mint"))?,
                    base_reserve: base_reserve
                        .ok_or_else(|| de::Error::missing_field("base_reserve"))?,
                    quote_reserve: quote_reserve
                        .ok_or_else(|| de::Error::missing_field("quote_reserve"))?,
                    base_price_in_quote: base_price_in_quote
                        .ok_or_else(|| de::Error::missing_field("base_price_in_quote"))?,
                    last_updated: last_updated
                        .ok_or_else(|| de::Error::missing_field("last_updated"))?,
                })
            }
        }
        deserializer.deserialize_struct(
            "PoolPriceInfo",
            &[
                "pool_address",
                "base_mint",
                "quote_mint",
                "base_reserve",
                "quote_reserve",
                "base_price_in_quote",
                "last_updated",
            ],
            PoolPriceInfoVisitor,
        )
    }
}

impl PoolPriceInfo {
    /// 模拟买入指定quote后的新状态（固定乘积公式）
    pub fn simulate_buy_quote(&self, quote_in: u64, fee: f64) -> PoolPriceInfo {
        let quote_in_after_fee = quote_in as f64 * (1.0 - fee);
        let new_quote_reserve = self.quote_reserve as f64 + quote_in_after_fee;
        let base_out = (quote_in_after_fee * self.base_reserve as f64)
            / (self.quote_reserve as f64 + quote_in_after_fee);
        let new_base_reserve = self.base_reserve as f64 - base_out;
        let new_base_price_in_quote = new_quote_reserve / new_base_reserve;
        PoolPriceInfo {
            base_reserve: new_base_reserve as u64,
            quote_reserve: new_quote_reserve as u64,
            base_price_in_quote: new_base_price_in_quote,
            last_updated: self.last_updated.clone(),
            pool_address: self.pool_address,
            base_mint: self.base_mint,
            quote_mint: self.quote_mint,
        }
    }

    /// 模拟卖出指定base后的新状态（固定乘积公式）
    pub fn simulate_sell_base(&self, base_in: u64, fee: f64) -> PoolPriceInfo {
        let base_in_f = base_in as f64;
        let new_base_reserve = self.base_reserve as f64 + base_in_f;
        let quote_out =
            (base_in_f * self.quote_reserve as f64) / (self.base_reserve as f64 + base_in_f);
        let quote_out_after_fee = quote_out * (1.0 - fee);
        let new_quote_reserve = self.quote_reserve as f64 - quote_out_after_fee;
        let new_base_price_in_quote = new_quote_reserve / new_base_reserve;
        PoolPriceInfo {
            base_reserve: new_base_reserve as u64,
            quote_reserve: new_quote_reserve as u64,
            base_price_in_quote: new_base_price_in_quote,
            last_updated: self.last_updated.clone(),
            pool_address: self.pool_address,
            base_mint: self.base_mint,
            quote_mint: self.quote_mint,
        }
    }

    /// 买入：投入指定数量的quote，能买到多少base
    /// quote_in: 投入的quote数量
    /// fee: 手续费率 (例如 0.01 = 1%)
    /// 返回：能买到的base数量
    pub fn buy_base_with_quote(&self, quote_in: u64, fee: f64) -> u64 {
        let quote_in_after_fee = quote_in as f64 * (1.0 - fee);
        // AMM公式: base_out = (quote_in * base_reserve) / (quote_reserve + quote_in)
        let numerator = quote_in_after_fee * self.base_reserve as f64;
        let denominator = self.quote_reserve as f64 + quote_in_after_fee;
        (numerator / denominator) as u64
    }

    /// 买入：想买指定数量的base，需要投入多少quote
    /// base_out: 想买的base数量
    /// fee: 手续费率
    /// 返回：需要投入的quote数量
    pub fn quote_needed_for_base(&self, base_out: u64, fee: f64) -> u64 {
        // 反推公式: quote_in = (base_out * quote_reserve) / ((base_reserve - base_out) * (1 - fee))
        let numerator = base_out as f64 * self.quote_reserve as f64;
        let denominator = (self.base_reserve as f64 - base_out as f64) * (1.0 - fee);
        (numerator / denominator).ceil() as u64
    }

    /// 卖出：卖出指定数量的base，能得到多少quote
    /// base_in: 卖出的base数量  
    /// fee: 手续费率
    /// 返回：能得到的quote数量
    pub fn quote_from_selling_base(&self, base_in: u64, fee: f64) -> u64 {
        // 先用AMM公式算出quote_out，再对quote_out扣除fee
        let base_in_f = base_in as f64;
        let numerator = base_in_f * self.quote_reserve as f64;
        let denominator = self.base_reserve as f64 + base_in_f;
        let quote_out = numerator / denominator;
        let quote_out_after_fee = quote_out * (1.0 - fee);
        quote_out_after_fee as u64
    }

    /// 卖出：想得到指定数量的quote，需要卖出多少base
    /// quote_out: 想得到的quote数量
    /// fee: 手续费率
    /// 返回：需要卖出的base数量
    pub fn base_needed_for_quote(&self, quote_out: u64, fee: f64) -> u64 {
        // 反推公式: base_in = (quote_out * base_reserve) / ((quote_reserve - quote_out) * (1.0 - fee))
        let numerator = quote_out as f64 * self.base_reserve as f64;
        let denominator = (self.quote_reserve as f64 - quote_out as f64) * (1.0 - fee);
        (numerator / denominator).ceil() as u64
    }
}

pub trait MintDecimal {
    fn decimal(&self) -> u8;
}

impl MintDecimal for Pubkey {
    fn decimal(&self) -> u8 {
        if self == &pubkey!("USD1ttGY1N17NEEHLmELoaybftRBUSErhqYiQzvEmuB") {
            6
        } else {
            9
        }
    }
}
