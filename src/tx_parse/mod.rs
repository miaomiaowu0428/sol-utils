//! 多来源交易的统一解析层。
//!
//! 交易可能来自三个入口，它们的原始数据形态完全不同，但下游只想要
//! 一套统一的结果：`IndexedInstruction` 序列 + 余额变化 + 周边信息。
//!
//! - [`from_grpc`]：geyser 订阅（`grpc_client::TransactionFormat`），
//!   消息体已被 proto 解析成字段，meta 是官方 `TransactionStatusMeta`。
//! - [`from_rpc`]：RPC `getTransaction` 拉到的 JSON（base64/base58 编码交易）。
//! - [`from_shred`]：shred 流解析出的原始字节，没有 meta（余额变化需要自行推导）。
//!
//! ## 统一契约
//!
//! 三个来源最终都产出 [`ParsedTx`]，其中：
//!
//! - `instructions`：`IndexedInstruction` 序列，索引规则与旧 API 完全一致
//!   （主指令 `"1"`、`"2"`…，内部指令 `"1.1"`、`"1.2"`…，日志重建的
//!   "假 CPI" 为 `"logevent.N"`）。
//! - `account_keys`：**完整**账户列表，已按顺序拼接
//!   `static_account_keys` + `loaded_addresses.writable` + `loaded_addresses.readonly`。
//!   指令里的 `program_id_index` / `accounts` 都按下标索引这个列表。
//! - `token_balance_changes`：按 token account 归属的余额变化。
//!
//! ## 为什么不把三者写成一个函数
//!
//! 三个来源的差异是**本质性**的，不是分支能掩盖的：
//!
//! | 维度 | from_grpc | from_rpc | from_shred |
//! |---|---|---|---|
//! | 消息体 | proto 已解析字段 | 需要反序列化 | 原始字节 |
//! | meta | 官方类型，直接可用 | JSON，需要转换 | **没有** |
//! | 余额变化 | 从 meta 读 | 从 meta 读 | 需自行推导 |
//! | ALT 地址 | meta 里有 | 需要从链上取 | 消息里自带 |
//!
//! 三者共享的是 [`common`] 里的 key 拼接、指令展开、日志事件重建逻辑。

pub mod common;
pub mod from_grpc;
pub mod from_rpc;
pub mod from_shred;
pub mod ui_meta;

pub use common::{
    account_keys_of, flatten_instructions_with_keys, inject_v1_config_as_instructions, synthetic_index, tx_config_of,
    ComputeBudgetValues, ParseError, ParsedTx, TxConfig, V1Config,
};

// 三个来源的入口，统一命名便于下游按需引入。
pub use from_grpc::parse_grpc_tx;
pub use from_rpc::parse_rpc_tx;
pub use from_shred::parse_shred_tx;
