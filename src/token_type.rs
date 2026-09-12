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

use solana_sdk::{
    instruction::{AccountMeta, Instruction},
    pubkey,
    pubkey::Pubkey,
};

/// Associated Token Program（标准 ATA）。
pub static ATA_PROGRAM: Pubkey = pubkey!("ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL");
/// SPL Token 程序（tokenkeg）。
pub static TOKEN_PROGRAM: Pubkey = pubkey!("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA");
/// SPL Token-2022 程序。
pub static TOKEN_PROGRAM_2022: Pubkey = pubkey!("TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb");
/// Memo 程序。
pub static MEMO_PROGRAM: Pubkey = pubkey!("MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr");
/// System program（建 ATA 时用）。
pub static SYSTEM_PROGRAM: Pubkey = pubkey!("11111111111111111111111111111111");

/// 包装后的 SOL（WSOL）mint。
pub static WSOL_MINT: Pubkey = pubkey!("So11111111111111111111111111111111111111112");
/// USDC mint。
pub static USDC_MINT: Pubkey = pubkey!("EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v");

/// 计算 owner 在某 mint（用 token_program）下的 ATA。
pub fn ata(owner: &Pubkey, mint: &Pubkey, token_program: &Pubkey) -> Pubkey {
    Pubkey::find_program_address(&[owner.as_ref(), token_program.as_ref(), mint.as_ref()], &ATA_PROGRAM).0
}

/// 一笔交易的某一侧 token：mint + 它实际归属的 token 程序类型。
///
/// 有些协议（如 clmm）链上不暴露每侧程序，需由外部（注册表）在此指明是 legacy
/// (tokenkeg) 还是 Token-2022，用于推导我们 payer 自己的用户 ATA。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenType {
    /// SPL Token（tokenkeg）。
    TokenLegacy(Pubkey),
    /// SPL Token-2022。
    Token2022(Pubkey),
}

impl TokenType {
    /// 经典 SPL Token（tokenkeg）币种。
    pub const fn legacy(mint: Pubkey) -> Self {
        Self::TokenLegacy(mint)
    }

    /// Token-2022 币种。
    pub const fn token_2022(mint: Pubkey) -> Self {
        Self::Token2022(mint)
    }

    /// mint 地址。
    pub fn mint(&self) -> Pubkey {
        match self {
            TokenType::TokenLegacy(m) | TokenType::Token2022(m) => *m,
        }
    }

    /// 归属的 token program。
    pub fn program(&self) -> Pubkey {
        match self {
            TokenType::TokenLegacy(_) => TOKEN_PROGRAM,
            TokenType::Token2022(_) => TOKEN_PROGRAM_2022,
        }
    }

    /// 是否 Token-2022。
    pub fn is_token_2022(&self) -> bool {
        matches!(self, TokenType::Token2022(_))
    }

    /// 是否 WSOL。
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

    /// 人类可读描述：`<mint>(<program-kind>)`。
    pub fn describe(&self) -> String {
        let kind = if self.is_token_2022() { "token-2022" } else { "legacy" };
        format!("{}({kind})", self.mint())
    }
}

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
