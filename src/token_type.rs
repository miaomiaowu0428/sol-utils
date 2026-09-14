//! 跨协议共享的 SPL Token 常量与 [`TokenType`]。
//!
//! 放在 `utils` 里是为了让**所有**构件库（`raydium-trade` / `meteora-trade` /
//! `pump-trade` / `dex-router` …）引用同一份定义，而不是各自复制一份。
//!
//! # 为什么需要 [`TokenType`]
//!
//! 几乎所有用户侧 ATA 的推导都依赖"这个 mint 到底归属哪个 token program"
//! （tokenkeg 还是 Token-2022）。有些协议（如 clmm 的 `swap_v2`）链上不暴露每侧的
//! token program，只能由外部（注册表 / 配置）在构造交易时指明 —— 写错就是
//! "账户不存在"这类难查的链上错误。所以 mint 不应该以裸 `Pubkey` 到处传。

use std::str::FromStr;

use solana_client::nonblocking::rpc_client::RpcClient;
use solana_sdk::{
    instruction::{AccountMeta, Instruction},
    pubkey,
    pubkey::Pubkey,
};

/// Associated Token Program（标准 ATA）。
pub static ATA_PROGRAM: Pubkey = const_accounts::ATA_PROGRAM;
/// SPL Token 程序（tokenkeg）。
pub static TOKEN_PROGRAM: Pubkey = const_accounts::TOKEN_PROGRAM;
/// SPL Token-2022 程序。
pub static TOKEN_PROGRAM_2022: Pubkey = const_accounts::TOKEN_PROGRAM_2022;
/// Memo 程序。
pub static MEMO_PROGRAM: Pubkey = const_accounts::MEMO_PROGRAM;
/// System program（建 ATA 时用）。
pub static SYSTEM_PROGRAM: Pubkey = const_accounts::SYSTEM_PROGRAM;

/// 包装后的 SOL（WSOL）mint。
pub static WSOL_MINT: Pubkey = const_accounts::WSOL_MINT;
/// USDC mint。
pub static USDC_MINT: Pubkey = const_accounts::USDC_MINT;

/// mint 账户里 `decimals` 字节的偏移（SPL Mint 与 Token-2022 base layout 一致）。
const MINT_DECIMALS_OFFSET: usize = 44;
/// mint 账户 base layout 的最小长度（= 82）。
const MINT_MIN_LEN: usize = 82;

/// 计算 owner 在某 mint（用 token_program）下的 ATA。
pub fn ata(owner: &Pubkey, mint: &Pubkey, token_program: &Pubkey) -> Pubkey {
    Pubkey::find_program_address(&[owner.as_ref(), token_program.as_ref(), mint.as_ref()], &ATA_PROGRAM).0
}

/// 一个币种：**mint + 归属的 token program + 小数位**。
///
/// 为什么三者要绑在同一个类型里：
/// - **token program**：几乎所有用户侧 ATA / vault 推导都依赖"这个 mint 属于 tokenkeg
///   还是 Token-2022"。有些协议（如 clmm）链上**不暴露**每侧 program，必须由外部指明 ——
///   写错就是"账户不存在"这类难查的链上错误。
/// - **decimals**：决定"1 个币 = 多少最小单位"，凡是涉及人类可读金额（买入量、
///   默认探测量、日志显示）都要用。
///
/// 不确认 decimals / program 时，用 [`TokenType::resolve`] / [`TokenType::from`]
/// 从链上查一次（启动时查一次是正当用法，热路径不要调）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenType {
    /// 经典 SPL Token（`Tokenkeg…`）。
    Legacy { mint: Pubkey, decimals: u8 },
    /// SPL Token-2022（`TokenzQdB…`）。
    Token2022 { mint: Pubkey, decimals: u8 },
}

impl TokenType {
    /// 经典 SPL Token 币种。
    pub const fn legacy(mint: Pubkey, decimals: u8) -> Self {
        Self::Legacy { mint, decimals }
    }

    /// Token-2022 币种。
    pub const fn token_2022(mint: Pubkey, decimals: u8) -> Self {
        Self::Token2022 { mint, decimals }
    }

    /// 包装 SOL（WSOL，9 位，经典 SPL）。
    pub const fn wsol() -> Self {
        Self::legacy(WSOL_MINT, 9)
    }

    /// USDC（6 位，经典 SPL）。
    pub const fn usdc() -> Self {
        Self::legacy(USDC_MINT, 6)
    }

    /// mint 地址。
    pub const fn mint(&self) -> Pubkey {
        match self {
            Self::Legacy { mint, .. } | Self::Token2022 { mint, .. } => *mint,
        }
    }

    /// mint 地址的**引用**（借用 `self`，生命周期跟 `TokenType` 一样长）。
    ///
    /// 给那些需要「长期借用 mint 地址」的结构用 —— `&token.mint()` 是临时值，
    /// 活不过一条语句（E0716）。
    pub const fn mint_ref(&self) -> &Pubkey {
        match self {
            Self::Legacy { mint, .. } | Self::Token2022 { mint, .. } => mint,
        }
    }

    /// 小数位。
    pub const fn decimals(&self) -> u8 {
        match self {
            Self::Legacy { decimals, .. } | Self::Token2022 { decimals, .. } => *decimals,
        }
    }

    /// 归属的 token program（做 ATA / vault 推导时用）。
    pub const fn program(&self) -> Pubkey {
        match self {
            Self::Legacy { .. } => TOKEN_PROGRAM,
            Self::Token2022 { .. } => TOKEN_PROGRAM_2022,
        }
    }

    /// token program 的 **`'static` 引用**（只有两种，都是静态常量）。
    /// 同 [`TokenType::mint_ref`]，避开 `&token.program()` 的临时值问题。
    pub const fn program_ref(&self) -> &'static Pubkey {
        match self {
            Self::Legacy { .. } => &TOKEN_PROGRAM,
            Self::Token2022 { .. } => &TOKEN_PROGRAM_2022,
        }
    }

    /// 是否 Token-2022。
    pub const fn is_token_2022(&self) -> bool {
        matches!(self, Self::Token2022 { .. })
    }

    /// 是否包装 SOL。
    pub fn is_wsol(&self) -> bool {
        self.mint() == WSOL_MINT
    }

    /// 是否 USDC。
    pub fn is_usdc(&self) -> bool {
        self.mint() == USDC_MINT
    }

    /// 该侧在 owner 名下的 ATA。
    pub fn ata(&self, owner: &Pubkey) -> Pubkey {
        ata(owner, &self.mint(), &self.program())
    }

    /// 人类可读描述：`<mint>(<program-kind>, <decimals>)`。
    pub fn describe(&self) -> String {
        let kind = if self.is_token_2022() { "token-2022" } else { "legacy" };
        format!("{}({}, {})", self.mint(), kind, self.decimals())
    }

    /// 从链上解析一个 mint：账户 owner 决定 token program，`decimals` 字段决定小数位。
    ///
    /// 这是"启动时查一次"的正当用法（构造交易对、建 ATA 之前）；热路径不应调用。
    pub async fn resolve(mint: Pubkey, rpc: &RpcClient) -> Result<Self, ResolveError> {
        let acc = rpc.get_account(&mint).await.map_err(|e| ResolveError::Rpc(e.to_string()))?;
        if acc.data.len() < MINT_MIN_LEN {
            return Err(ResolveError::BadMintData(acc.data.len()));
        }
        let decimals = acc.data[MINT_DECIMALS_OFFSET];
        if acc.owner == TOKEN_PROGRAM {
            Ok(Self::Legacy { mint, decimals })
        } else if acc.owner == TOKEN_PROGRAM_2022 {
            Ok(Self::Token2022 { mint, decimals })
        } else {
            Err(ResolveError::NotTokenMint(acc.owner))
        }
    }

    /// 从 base58 mint 地址字符串解析（内部用 [`crate::JSON_RPC_CLIENT`]，读 `JSON_RPC_URL`）。
    ///
    /// 例：`let t = TokenType::from("So111…112").await?;`
    pub async fn from(mint: impl AsRef<str>) -> Result<Self, ResolveError> {
        let raw = mint.as_ref();
        let pk = Pubkey::from_str(raw).map_err(|e| ResolveError::BadMintAddress(e.to_string()))?;
        Self::resolve(pk, &crate::JSON_RPC_CLIENT).await
    }
}

/// [`TokenType::resolve`] / [`TokenType::from`] 的失败原因。
#[derive(Debug)]
pub enum ResolveError {
    /// 传入的字符串不是合法 base58 pubkey。
    BadMintAddress(String),
    /// RPC 调用失败。
    Rpc(String),
    /// 账户数据长度不足 / 不是合法 mint layout。
    BadMintData(usize),
    /// 账户 owner 既不是 SPL Token 也不是 Token-2022。
    NotTokenMint(Pubkey),
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadMintAddress(e) => write!(f, "不是合法 base58 pubkey: {e}"),
            Self::Rpc(e) => write!(f, "RPC 失败: {e}"),
            Self::BadMintData(len) => write!(f, "不是合法 mint 账户（data 长度 {len}）"),
            Self::NotTokenMint(owner) => write!(f, "owner {owner} 不是 SPL Token / Token-2022 program"),
        }
    }
}

impl std::error::Error for ResolveError {}

/// 建 ATA 指令（`create_associated_token_account`）。
///
/// **不幂等**：目标 ATA 已存在时链上会报错，调用方需先确认账户不存在
/// （见 dex-router 测试里的 `ensure_ata`）。
pub fn create_ata_ix(payer: &Pubkey, owner: &Pubkey, token: &TokenType) -> Instruction {
    Instruction {
        program_id: ATA_PROGRAM,
        accounts: vec![
            AccountMeta::new(*payer, true),
            AccountMeta::new(token.ata(owner), false),
            AccountMeta::new_readonly(*owner, false),
            AccountMeta::new_readonly(token.mint(), false),
            AccountMeta::new_readonly(SYSTEM_PROGRAM, false),
            AccountMeta::new_readonly(token.program(), false),
        ],
        data: vec![],
    }
}
