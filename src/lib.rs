use grpc_client::TransactionFormat;
use log::error;
use log::info;
use log::warn;
use serde::Deserialize;
use serde::Serialize;
use solana_address_lookup_table_interface::state::AddressLookupTable;
use solana_client::nonblocking::rpc_client::RpcClient;
use solana_client::rpc_config::CommitmentConfig;
use solana_sdk::bs58;
use solana_sdk::hash::Hash;
use solana_sdk::message::Instruction;
use solana_sdk::message::compiled_instruction::CompiledInstruction;
use solana_sdk::message::v0::MessageAddressTableLookup;
use solana_sdk::program_error::ProgramError;
use solana_sdk::pubkey;
use solana_sdk::pubkey::Pubkey;
use solana_sdk::signature::Signature;
use solana_sdk::transaction::VersionedTransaction;
use spl_associated_token_account::get_associated_token_address_with_program_id;
use std::env;
use std::str::FromStr;
use std::sync::Arc;
use std::sync::LazyLock;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;
use std::time::{Duration, Instant};
use ta::Close;
use ta::High;
use ta::Low;
use tokio::sync::RwLock;
use whirlwind::ShardMap;

pub mod parse_rpc_fetched_json;
pub mod macros;
pub mod pool_calculation;
pub mod time;

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

use std::fmt;

/// 为小数类型（f64/f32）提供“0.{n}xxxx”格式化能力的Trait
pub trait SmallDecimalFormat
where
    Self: fmt::Display,
{
    /// 格式化小正数为 0.{n}xxxx 形式
    /// - significant_digits：保留的有效数字位数（建议 ≥1）
    /// - 返回：成功则为格式化字符串，失败（如数值不在 (0,1) 范围）则为 None
    fn format_small_decimal(&self, significant_digits: usize) -> Option<String>;

    /// （可选）带兜底的格式化：失败时返回原始数字的字符串（避免处理 None）
    fn format_small_decimal_or_default(&self, significant_digits: usize) -> String {
        self.format_small_decimal(significant_digits)
            .unwrap_or_else(|| self.to_string())
    }
}

// ------------------------------ f64 实现 ------------------------------
impl SmallDecimalFormat for f64 {
    fn format_small_decimal(&self, significant_digits: usize) -> Option<String> {
        // 额外校验：有效数字位数不能为 0（避免空字符串）
        if significant_digits == 0 {
            return None;
        }

        let num = *self;
        if num == 0.0 || num.abs() >= 1.0 {
            return None;
        }

        let sign = if num < 0.0 { "-" } else { "" };
        let abs_num = num.abs();

        // 优化：科学计数法保留位数适配有效数字需求（避免多余计算）
        // f64 有效精度上限约15位，取 "需要的有效数字+1" 和 15 的最小值
        let sci_precision = std::cmp::min(significant_digits + 1, 15);
        // 关键修正：用 sci_precision 控制科学计数法的保留精度（之前没用到这里）
        let sci_str = fmt::format(format_args!("{:.1$e}", abs_num, sci_precision));

        let parts: Vec<&str> = sci_str.split('e').collect();
        if parts.len() != 2 {
            return None;
        }
        let (sig_part, exp_part) = (parts[0], parts[1]);

        let exponent: i32 = match exp_part.parse() {
            Ok(exp) if exp < 0 => exp,
            _ => return None,
        };

        let n = (-exponent) - 1;
        if n < 0 {
            return None;
        }

        let sig_digits = sig_part
            .chars()
            .filter(|&c| c != '.')
            .take(significant_digits)
            .collect::<String>();

        Some(format!("{sign}0.{{{n}}}{sig_digits}"))
    }
}

// ------------------------------ f32 实现 ------------------------------
impl SmallDecimalFormat for f32 {
    fn format_small_decimal(&self, significant_digits: usize) -> Option<String> {
        if significant_digits == 0 {
            return None;
        }

        let num = *self;
        if num == 0.0 || num.abs() >= 1.0 {
            return None;
        }

        let sign = if num < 0.0 { "-" } else { "" };
        let abs_num = num.abs();

        // f32 有效精度上限约9位，同样适配有效数字需求
        let sci_precision = std::cmp::min(significant_digits + 1, 9);
        // 关键修正：用 sci_precision 控制保留精度
        let sci_str = fmt::format(format_args!("{:.1$e}", abs_num, sci_precision));

        let parts: Vec<&str> = sci_str.split('e').collect();
        if parts.len() != 2 {
            return None;
        }
        let (sig_part, exp_part) = (parts[0], parts[1]);

        let exponent: i32 = match exp_part.parse() {
            Ok(exp) if exp < 0 => exp,
            _ => return None,
        };

        let n = (-exponent) - 1;
        if n < 0 {
            return None;
        }

        let sig_digits = sig_part
            .chars()
            .filter(|&c| c != '.')
            .take(significant_digits)
            .collect::<String>();

        Some(format!("{sign}0.{{{n}}}{sig_digits}"))
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
    token_program: &Pubkey,
    json_rpc_client: &solana_client::nonblocking::rpc_client::RpcClient,
) -> Option<(Pubkey, u64)> {
    let ata = get_associated_token_address_with_program_id(owner, mint, token_program);
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
impl PartialEq for PoolPriceInfo {
    fn eq(&self, other: &Self) -> bool {
        self.base_reserve == other.base_reserve && self.quote_reserve == other.quote_reserve
    }
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

pub static JSON_RPC_CLIENT: LazyLock<Arc<RpcClient>> = LazyLock::new(|| {
    let url = env::var("JSON_RPC_URL").expect("JSON_RPC_URL not set");
    Arc::new(RpcClient::new_with_commitment(
        url,
        CommitmentConfig::processed(),
    ))
});

pub static ALTS: LazyLock<ShardMap<Pubkey, Vec<Pubkey>>> =
    LazyLock::new(|| ShardMap::with_shards(16));

#[async_trait::async_trait]
pub trait FetchAlt {
    async fn fetch_alt(&self, address: &Pubkey) -> Result<Vec<Pubkey>, ()>;
}

#[async_trait::async_trait]
impl FetchAlt for RpcClient {
    async fn fetch_alt(&self, address: &Pubkey) -> Result<Vec<Pubkey>, ()> {
        if let Ok(alt_account_data) = self.get_account_data(&address).await {
            if let Ok(alt_addresses) = AddressLookupTable::deserialize(&alt_account_data) {
                return Ok(alt_addresses.addresses.to_vec());
            }
        }
        Err(())
    }
}

async fn get_or_fetch_alt(alt_address: Pubkey) -> Result<Vec<Pubkey>, ()> {
    // info!("fetching alt: {alt_address}");
    match ALTS.get(&alt_address).await {
        Some(alt) => {
            let res: Vec<Pubkey> = alt.value().clone();
            // info!("found alt cache for {alt_address}");
            Ok(res)
        }
        None => {
            // info!("didn't found alt cache for {alt_address}; fetching...");
            let alt_accounts = JSON_RPC_CLIENT.fetch_alt(&alt_address).await?;
            ALTS.insert(alt_address, alt_accounts.clone()).await;
            Ok(alt_accounts)
        }
    }
}

pub async fn flatten_main_instructions(
    tx: &VersionedTransaction,
    slot: u64,
) -> Result<Vec<IndexedInstruction>, ()> {
    match &tx.message {
        solana_sdk::message::VersionedMessage::Legacy(message) => {
            Ok(flatten_main_ix_from_legasy_msg(message, slot))
        }
        solana_sdk::message::VersionedMessage::V0(message) => {
            Ok(flatten_main_ix_from_v0_msg(message, slot).await)
        }
    }
}

pub async fn flatten_main_ix_from_v0_msg(
    solana_sdk::message::v0::Message {
        account_keys: accounts,
        instructions: ixs,
        address_table_lookups,
        ..
    }: &solana_sdk::message::v0::Message,
    slot: u64,
) -> Vec<IndexedInstruction> {
    let mut alt_realonly: Vec<Pubkey> = vec![];
    let mut alt_writable: Vec<Pubkey> = vec![];
    for MessageAddressTableLookup {
        account_key,
        writable_indexes,
        readonly_indexes,
    } in address_table_lookups
    {
        let Ok(alt_onchain) = get_or_fetch_alt(*account_key).await else {
            continue;
        };
        for i in readonly_indexes {
            alt_realonly.push(*alt_onchain.get(*i as usize).unwrap_or(&Pubkey::default()))
        }
        for i in writable_indexes {
            alt_writable.push(*alt_onchain.get(*i as usize).unwrap_or(&Pubkey::default()))
        }
    }
    let mut accounts = accounts.clone();
    accounts.extend(alt_writable);
    accounts.extend(alt_realonly);
    ixs.iter() // 遍历指令引用，不消耗原 ixs
        .enumerate()
        .map(|(index, ix)| {
            // ix 是 &Instruction（共享引用）
            let ix_accounts: Vec<Pubkey> = ix
                .accounts
                .iter() // 关键：用 iter() 遍历引用，不消耗 ix.accounts
                .map(|&acc_idx| {
                    // 解构 &u8 → u8（因为 ix.accounts 是 Vec<u8>）
                    // 1. 索引转 usize；2. 取账户引用；3. 克隆成所有权类型（&Pubkey → Pubkey）
                    accounts
                        .get(acc_idx as usize)
                        .unwrap_or(&Pubkey::default())
                        .clone()
                })
                .collect(); // 现在元素是 Pubkey，可正常收集

            IndexedInstruction {
                index: index.to_string(),
                instruction: ParsedInstruction {
                    // 关键：accounts 是 Vec<Pubkey>，索引访问返回 &Pubkey，需 clone 转所有权
                    program: accounts[ix.program_id_index as usize].clone(),
                    accounts: ix_accounts,
                    data: ix.data.clone(), // data 是 Vec<u8>，clone 得到所有权
                    slot,
                },
                slot,
            }
        })
        .collect()
}

pub fn flatten_main_ix_from_legasy_msg(
    solana_sdk::message::Message {
        account_keys: accounts,
        instructions: ixs,
        ..
    }: &solana_sdk::message::Message,
    slot: u64,
) -> Vec<IndexedInstruction> {
    ixs.iter()
        .enumerate()
        .map(|(index, ix)| {
            let ix_accounts = ix
                .accounts
                .iter()
                .map(|index| accounts[*index as usize])
                .collect();
            IndexedInstruction {
                index: index.to_string(),
                instruction: ParsedInstruction {
                    program: accounts[ix.program_id_index as usize],
                    accounts: ix_accounts,
                    data: ix.data.clone(),
                    slot,
                },
                slot,
            }
        })
        .collect()
}

#[derive(Debug, Clone, Copy)]
pub struct TokenBalanceChange {
    pub mint: Pubkey,
    pub mint_decimals: u8,
    pub change: i128,     // 变化量
    pub pre_amount: u64,  // 交易前余额
    pub post_amount: u64, // 交易后余额
    pub token_account: Pubkey,
    pub owner: Pubkey,
}

// 按 token_account 排序
impl Ord for TokenBalanceChange {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.token_account.cmp(&other.token_account)
    }
}

impl PartialOrd for TokenBalanceChange {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for TokenBalanceChange {
    fn eq(&self, other: &Self) -> bool {
        self.token_account == other.token_account
    }
}

impl Eq for TokenBalanceChange {}

impl TokenBalanceChange {
    pub fn from_tx(tx: &TransactionFormat) -> Result<Vec<Self>, ()> {
        let Some(ref meta) = tx.meta else {
            return Err(());
        };
        let Some(ref pre_token_balances) = meta.pre_token_balances else {
            return Err(());
        };
        let Some(ref post_token_balances) = meta.post_token_balances else {
            return Err(());
        };

        // 使用 HashMap 来匹配 pre 和 post 余额
        use std::collections::HashMap;

        let mut pre_map: HashMap<Pubkey, (Pubkey, Pubkey, u8, u64)> = HashMap::new();
        for tb in pre_token_balances {
            let mint = Pubkey::from_str(&tb.mint).unwrap_or_default();
            let owner = Pubkey::from_str(&tb.owner).unwrap_or_default();
            let token_account = tx
                .account_keys
                .get(tb.account_index as usize)
                .cloned()
                .unwrap_or_default();
            let amt = tb.ui_token_amount.amount.parse().unwrap_or(0u64);
            pre_map.insert(
                token_account,
                (mint, owner, tb.ui_token_amount.decimals, amt),
            );
        }

        let mut changes = Vec::new();
        for tb in post_token_balances {
            let mint = Pubkey::from_str(&tb.mint).unwrap_or_default();
            let owner = Pubkey::from_str(&tb.owner).unwrap_or_default();
            let token_account = tx
                .account_keys
                .get(tb.account_index as usize)
                .cloned()
                .unwrap_or_default();
            let post_amt = tb.ui_token_amount.amount.parse().unwrap_or(0u64);

            // 查找对应的 pre 余额
            let pre_amt = pre_map
                .get(&token_account)
                .map(|(_, _, _, amt)| *amt)
                .unwrap_or(0u64);

            let delta = post_amt as i128 - pre_amt as i128;
            if delta != 0 {
                changes.push(TokenBalanceChange {
                    mint,
                    mint_decimals: tb.ui_token_amount.decimals,
                    change: delta,
                    pre_amount: pre_amt,
                    post_amount: post_amt,
                    token_account,
                    owner,
                });
            }
        }
        Ok(changes)
    }
}

pub trait TokenName {
    fn name(&self) -> String;
}

impl TokenName for Pubkey {
    fn name(&self) -> String {
        if *self == pubkey!("So11111111111111111111111111111111111111112") {
            "Wsol".to_string()
        } else if *self == pubkey!("USD1ttGY1N17NEEHLmELoaybftRBUSErhqYiQzvEmuB") {
            "USD1".to_string()
        } else {
            self.to_string()
        }
    }
}

/// USD1单位转换：1 USD1 = 1_000_000 单位
pub trait ToUnit {
    fn to_unit(self, decimal: Self) -> u64;
}

impl ToUnit for f64 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).powf(decimal)) as u64
    }
}

impl ToUnit for f32 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).powf(decimal)) as u64
    }
}

impl ToUnit for u64 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).pow(decimal.try_into().unwrap())) as u64
    }
}

impl ToUnit for u32 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).pow(decimal.try_into().unwrap())) as u64
    }
}

impl ToUnit for u16 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).pow(decimal.try_into().unwrap())) as u64
    }
}

impl ToUnit for u8 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).pow(decimal.try_into().unwrap())) as u64
    }
}

impl ToUnit for i64 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).pow(decimal.try_into().unwrap())) as u64
    }
}

impl ToUnit for i32 {
    fn to_unit(self, decimal: Self) -> u64 {
        (self * (10 as Self).pow(decimal.try_into().unwrap())) as u64
    }
}

pub fn build_close_ata_ix(
    token_program_id: &Pubkey,
    account_pubkey: &Pubkey,
    destination_pubkey: &Pubkey,
    owner_pubkey: &Pubkey,
    signer_pubkeys: &[&Pubkey],
) -> Result<Instruction, ProgramError> {
    if token_program_id == &spl_token::ID {
        spl_token::instruction::close_account(
            &token_program_id,   // token_program_id
            &account_pubkey,     // account_to_close (ATA)
            &destination_pubkey, // destination (接收剩余 SOL)
            &owner_pubkey,       // owner
            &signer_pubkeys,     // multisigners
        )
    } else if token_program_id == &spl_token_2022::ID {
        spl_token_2022::instruction::close_account(
            &token_program_id,   // token_program_id
            &account_pubkey,     // account_to_close (ATA)
            &destination_pubkey, // destination (接收剩余 SOL)
            &owner_pubkey,       // owner
            &signer_pubkeys,     // multisigners
        )
    } else {
        Err(ProgramError::InvalidAccountData)
    }
}

impl Default for PoolPriceInfo {
    fn default() -> Self {
        Self {
            pool_address: Pubkey::default(),
            base_mint: Pubkey::default(),
            quote_mint: Pubkey::default(),
            base_reserve: 0,
            quote_reserve: 0,
            base_price_in_quote: 0.0,
            last_updated: PoolTimeStr::now_utc(),
        }
    }
}

pub fn now() -> u64 {
    // 1. 获取当前系统时间与 UNIX 纪元的时间差（处理可能的错误）
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("系统时间早于 UNIX 纪元（极少发生）");

    // 2. 不同精度的时间戳
    duration.as_secs()
}

#[test]
fn test_pool() {
    let pool = PoolPriceInfo {
        base_reserve: 1_073_000_000_000_000,
        quote_reserve: 30_000_000_000,
        ..Default::default()
    };
    println!(
        "buy 20 sol: {}",
        pool.buy_base_with_quote(20.to_lamport(), 0.0)
    );
    println!(
        "buy 50 sol: {}",
        pool.buy_base_with_quote(50.to_lamport(), 0.0)
    );
    println!(
        "buy 80 sol: {}",
        pool.buy_base_with_quote(80.to_lamport(), 0.0)
    );
    println!(
        "buy 85 sol: {}; total supply - buy: {}",
        pool.buy_base_with_quote(85.to_lamport(), 0.0),
        1_000_000_000_000_000 - pool.buy_base_with_quote(85.to_lamport(), 0.0)
    );
}
