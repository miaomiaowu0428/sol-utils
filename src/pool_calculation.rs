#![allow(unused)]

use crate::PoolPriceInfo;

impl PoolPriceInfo {
    // =======================================================
    // --- 交易输出计算 (Exact In) ---
    // =======================================================

    /// [买入 Base] 投入指定数量的 Quote，能买到多少 Base。
    /// 交易方向: Quote -> Base
    /// @param quote_in 投入的 Quote 数量 (u64)
    /// @param fee 手续费率 (f64)
    /// @returns 能买到的 Base 数量 (u64)
    pub fn get_base_out_from_quote_in(&self, quote_in: u64, fee: f64) -> u64 {
        let quote_in_after_fee = quote_in as f64 * (1.0 - fee);

        // Base_out = (Quote_in_net * Base_Reserve) / (Quote_Reserve + Quote_in_net)
        let numerator = quote_in_after_fee * self.base_reserve as f64;
        let denominator = self.quote_reserve as f64 + quote_in_after_fee;

        // 向下取整
        (numerator / denominator) as u64
    }

    /// [卖出 Base] 卖出指定数量的 Base，能得到多少 Quote。
    /// 交易方向: Base -> Quote
    /// @param base_in 卖出的 Base 数量 (u64)
    /// @param fee 手续费率 (f64)
    /// @returns 能得到的 Quote 数量 (u64)
    pub fn get_quote_out_from_base_in(&self, base_in: u64, fee: f64) -> u64 {
        let base_in_f = base_in as f64;

        // 1. AMM公式计算毛输出 (Quote_Gross)
        let numerator = base_in_f * self.quote_reserve as f64;
        let denominator = self.base_reserve as f64 + base_in_f;
        let quote_out_gross = numerator / denominator;

        // 2. 扣除手续费，得到净输出
        let quote_out_net = quote_out_gross * (1.0 - fee);

        // 向下取整
        quote_out_net as u64
    }

    // =======================================================
    // --- 交易输入计算 (Exact Out) ---
    // =======================================================

    /// [买入 Base] 想买指定数量的 Base，需要投入多少 Quote。
    /// 交易方向: Quote -> Base
    /// @param base_out 期望获得的 Base 数量 (u64)
    /// @param fee 手续费率 (f64)
    /// @returns 需要输入的 Quote 数量 (u64)
    pub fn get_quote_in_for_base_out(&self, base_out: u64, fee: f64) -> u64 {
        if base_out >= self.base_reserve {
            // 储备不足以支付输出
            return u64::MAX;
        }

        // Quote_in = ceil( (Base_out * Quote_Reserve) / ((Base_Reserve - Base_out) * (1 - fee)) )
        let base_out_f = base_out as f64;
        let numerator = base_out_f * self.quote_reserve as f64;
        let denominator = (self.base_reserve as f64 - base_out_f) * (1.0 - fee);

        // 向上取整
        (numerator / denominator).ceil() as u64
    }

    /// [卖出 Base] 想得到指定数量的 Quote (净额)，需要卖出多少 Base。
    /// 交易方向: Base -> Quote
    /// @param quote_out 期望获得的 Quote 数量 (净额, u64)
    /// @param fee 手续费率 (f64)
    /// @returns 需要卖出的 Base 数量 (u64)
    pub fn get_base_in_for_quote_out(&self, quote_out: u64, fee: f64) -> u64 {
        // 1. 反推毛输出 (Quote_Gross)
        let quote_gross = quote_out as f64 / (1.0 - fee);

        // 2. 检查储备是否足够支付毛输出
        if quote_gross >= self.quote_reserve as f64 {
            return u64::MAX;
        }

        // 3. AMM 反推所需 Base: Base_in = ceil( (Quote_Gross * Base_Reserve) / (Quote_Reserve - Quote_Gross) )
        let numerator = quote_gross * self.base_reserve as f64;
        let denominator = self.quote_reserve as f64 - quote_gross;

        // 向上取整
        (numerator / denominator).ceil() as u64
    }

    // =======================================================
    // --- 交易后状态计算 (After Trade) ---
    // =======================================================

    /// 模拟 [买入 Base] (Quote -> Base) 后的新状态。
    /// 返回一个新的 PoolPriceInfo 结构体。
    pub fn after_buy_quote_exact_in(&self, quote_in: u64, fee: f64) -> Self {
        let base_out = self.get_base_out_from_quote_in(quote_in, fee);

        let new_quote_reserve = self.quote_reserve.saturating_add(quote_in);
        let new_base_reserve = self.base_reserve.saturating_sub(base_out);

        // 重新计算价格
        let new_base_price_in_quote = new_quote_reserve as f64 / new_base_reserve as f64;

        PoolPriceInfo {
            base_reserve: new_base_reserve,
            quote_reserve: new_quote_reserve,
            base_price_in_quote: new_base_price_in_quote,
            ..*self // 复制其他字段 (地址, mints, 更新时间等)
        }
    }

    /// 模拟 [卖出 Base] (Base -> Quote) 后的新状态。
    /// 返回一个新的 PoolPriceInfo 结构体。
    pub fn after_sell_base_exact_in(&self, base_in: u64, fee: f64) -> Self {
        // 1. 计算毛输出 (Quote_Gross) - 用于更新储备
        let base_in_f = base_in as f64;
        let quote_out_gross =
            (base_in_f * self.quote_reserve as f64) / (self.base_reserve as f64 + base_in_f);

        let new_base_reserve = self.base_reserve.saturating_add(base_in);
        // 修正：使用毛输出更新储备
        let new_quote_reserve = self.quote_reserve.saturating_sub(quote_out_gross as u64);

        // 重新计算价格
        let new_base_price_in_quote = new_quote_reserve as f64 / new_base_reserve as f64;

        PoolPriceInfo {
            base_reserve: new_base_reserve,
            quote_reserve: new_quote_reserve,
            base_price_in_quote: new_base_price_in_quote,
            ..*self
        }
    }

    /// 模拟 [买入 Base] (Quote -> Base) Exact Out 后的新状态。
    /// 返回一个新的 PoolPriceInfo 结构体。
    pub fn after_buy_base_exact_out(&self, base_out: u64, fee: f64) -> Self {
        let quote_in = self.get_quote_in_for_base_out(base_out, fee);

        let new_quote_reserve = self.quote_reserve.saturating_add(quote_in);
        let new_base_reserve = self.base_reserve.saturating_sub(base_out);

        // 重新计算价格
        let new_base_price_in_quote = new_quote_reserve as f64 / new_base_reserve as f64;

        PoolPriceInfo {
            base_reserve: new_base_reserve,
            quote_reserve: new_quote_reserve,
            base_price_in_quote: new_base_price_in_quote,
            ..*self
        }
    }

    /// 模拟 [卖出 Base] (Base -> Quote) Exact Out 后的新状态。
    /// 返回一个新的 PoolPriceInfo 结构体。
    pub fn after_sell_quote_exact_out(&self, quote_out: u64, fee: f64) -> Self {
        let base_in = self.get_base_in_for_quote_out(quote_out, fee);

        // 1. 反推毛输出 (Quote_Gross) - 用于更新储备
        let quote_gross = quote_out as f64 / (1.0 - fee);

        let new_base_reserve = self.base_reserve.saturating_add(base_in);
        // 修正：使用毛输出更新储备
        let new_quote_reserve = self.quote_reserve.saturating_sub(quote_gross as u64);

        // 重新计算价格
        let new_base_price_in_quote = new_quote_reserve as f64 / new_base_reserve as f64;

        PoolPriceInfo {
            base_reserve: new_base_reserve,
            quote_reserve: new_quote_reserve,
            base_price_in_quote: new_base_price_in_quote,
            ..*self
        }
    }
}

mod test {
    use solana_sdk::pubkey::Pubkey;

    use crate::{PoolPriceInfo, PoolTimeStr, SolToLamport};

    #[test]
    fn test() {
        let init_pool = PoolPriceInfo {
            base_reserve: 1073000000000000,
            quote_reserve: 30000000000,
            base_price_in_quote: 0.0,
            base_mint: Pubkey::default(),
            quote_mint: Pubkey::default(),
            pool_address: Pubkey::default(),
            last_updated: PoolTimeStr::now_utc(),
        };

        println!("Pool: {:#?}", init_pool);
        let full_pool = init_pool.after_buy_quote_exact_in(85.to_lamport(), 0.0);
        println!("Full Pool: {:#?}", full_pool);

        let pool_80 = full_pool.after_sell_quote_exact_out(5.to_lamport(), 0.0);
        let pool_80_2 = init_pool.after_buy_quote_exact_in(80.to_lamport(), 0.0);

        println!("Pool 80: {:#?}\n", pool_80);
        println!("Pool 80_2: {:#?}\n", pool_80_2);
        println!(
            "Pool 80 == Pool 80_2: {}",
            if pool_80 == pool_80_2 { "yes" } else { "no" }
        );
    }
}
