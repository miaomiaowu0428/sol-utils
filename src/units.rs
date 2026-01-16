use solana_sdk::native_token::LAMPORTS_PER_SOL;

/// 1 Lamport = 1,000,000 MicroLamports
pub const MICROLAMPORTS_PER_LAMPORT: u64 = 1_000_000;

pub trait UnitConverter {
    /// 将当前单位转为 MicroLamports (用于和 CU Price 直接计算/比较)
    fn to_micro_lamports(self) -> u64;
    
    /// 从 MicroLamports 转回当前单位 (通常用于计算最终支付的 Lamports)
    fn micro_to_lamports(self) -> u64;
}

// 为 u64 实现 (通常代表 Lamports)
impl UnitConverter for u64 {
    fn to_micro_lamports(self) -> u64 {
        self.saturating_mul(MICROLAMPORTS_PER_LAMPORT)
    }

    fn micro_to_lamports(self) -> u64 {
        self / MICROLAMPORTS_PER_LAMPORT
    }
}

// 为 f64 实现 (通常代表 SOL)
impl UnitConverter for f64 {
    fn to_micro_lamports(self) -> u64 {
        (self * (LAMPORTS_PER_SOL as f64) * (MICROLAMPORTS_PER_LAMPORT as f64)) as u64
    }

    fn micro_to_lamports(self) -> u64 {
        (self / (MICROLAMPORTS_PER_LAMPORT as f64)) as u64
    }
}