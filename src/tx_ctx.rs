//! 一笔交易 + 按需共享的展平结果。
//!
//! # 为什么需要它
//!
//! 同一笔交易要发给 N 个 subscriber（本项目注册了 20+ 个）。改造前每个 subscriber
//! 都在自己的 `on_tx` 里调一次 [`crate::flatten_instructions`]，同一份
//! `Vec<IndexedInstruction>` 被完整重建 8~12 遍（每次都重新生成 index 字符串、
//! 收集 accounts、clone data）。
//!
//! [`TxCtx`] 让 dispatcher 只创建一个实例，用 `Arc` 分发给所有 subscriber：
//! 谁第一个需要指令，谁触发唯一一次展平，其余人直接拿同一份结果。
//!
//! 采用**懒加载**而不是 dispatch 时立即展平，是因为绝大多数主网交易跟本项目
//! 无关（`interested` 就过滤掉了）：提前展平等于给全量交易白交一遍解析成本。
//!
//! # 用法
//!
//! ```ignore
//! async fn on_tx(self: Arc<Self>, ctx: Arc<TxCtx>) {
//!     let ixs = ctx.instructions();        // 首次调用时展平，之后共享
//!     for ix in ixs { /* ... */ }
//!     let _slot = ctx.slot;                // TxCtx: Deref<Target = TransactionFormat>
//! }
//! ```

use std::ops::Deref;
use std::sync::{Arc, OnceLock};

use grpc_client::TransactionFormat;

use crate::IndexedInstruction;

/// 一笔交易 + 按需展平（每笔交易最多展平一次）。
pub struct TxCtx {
    tx: Arc<TransactionFormat>,
    instructions: OnceLock<Arc<Vec<IndexedInstruction>>>,
}

impl TxCtx {
    pub fn new(tx: Arc<TransactionFormat>) -> Self {
        Self {
            tx,
            instructions: OnceLock::new(),
        }
    }

    /// 交易本体。
    pub fn tx(&self) -> &Arc<TransactionFormat> {
        &self.tx
    }

    /// 交易本体的 `Arc`（需要跨任务持有时用）。
    pub fn tx_arc(&self) -> Arc<TransactionFormat> {
        Arc::clone(&self.tx)
    }

    /// 展平后的指令序列（切片视图）。
    ///
    /// **首次调用时计算，之后所有 subscriber 共享同一份结果**；解析失败返回空
    /// 切片（与 [`crate::flatten_instructions`] 的失败语义一致）。
    ///
    /// 余额变化等可选产物不在这里算——见 [`crate::tx_parse::ParseOptions`]。
    pub fn instructions(&self) -> &[IndexedInstruction] {
        self.instructions_arc()
    }

    /// 展平后的指令序列（`Arc` 视图，需要跨任务/跨订阅者持有时用）。
    pub fn instructions_arc(&self) -> &Arc<Vec<IndexedInstruction>> {
        self.instructions
            .get_or_init(|| Arc::new(crate::flatten_instructions(&self.tx)))
    }

    /// 指令是否已经展平过（调试/埋点用）。
    pub fn is_flattened(&self) -> bool {
        self.instructions.get().is_some()
    }
}

impl Deref for TxCtx {
    type Target = TransactionFormat;

    fn deref(&self) -> &Self::Target {
        &self.tx
    }
}

impl AsRef<TransactionFormat> for TxCtx {
    fn as_ref(&self) -> &TransactionFormat {
        &self.tx
    }
}

impl std::fmt::Debug for TxCtx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TxCtx")
            .field("slot", &self.tx.slot)
            .field("flattened", &self.is_flattened())
            .finish()
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use solana_sdk::hash::Hash;
    use solana_sdk::message::{Message, VersionedMessage};
    use solana_sdk::transaction::VersionedTransaction;

    fn empty_tx(slot: u64) -> Arc<TransactionFormat> {
        let message = Message::new_with_blockhash(&[], None, &Hash::default());
        Arc::new(TransactionFormat {
            slot,
            index: 0,
            meta: None,
            transaction: VersionedTransaction {
                signatures: Vec::new(),
                message: VersionedMessage::Legacy(message),
            },
        })
    }

    /// 核心契约：同一笔交易的所有 `Arc<TxCtx>` 克隆共享**同一次**展平结果。
    #[test]
    fn instructions_are_flattened_once_and_shared() {
        let ctx = TxCtx::new(empty_tx(42));
        assert!(!ctx.is_flattened(), "未访问前不应该展平");

        let first = ctx.instructions_arc();
        assert!(ctx.is_flattened());
        assert!(Arc::ptr_eq(first, ctx.instructions_arc()), "第二次访问必须拿到同一份 Arc");
        assert_eq!(ctx.instructions().len(), ctx.instructions_arc().len());

        // 模拟 dispatcher 分发：同一个 `Arc<TxCtx>` 克隆给多个 subscriber，
        // 它们看到的展平结果必须是同一份（而不是各算各的）。
        let shared = Arc::new(TxCtx::new(empty_tx(42)));
        let to_sub_a = Arc::clone(&shared);
        let to_sub_b = Arc::clone(&shared);
        assert!(Arc::ptr_eq(to_sub_a.instructions_arc(), to_sub_b.instructions_arc()));
        assert!(Arc::ptr_eq(first, ctx.instructions_arc()), "同一句柄反复访问必须零重算");
    }

    /// `Deref` 让下游不用改代码就能拿到交易本体（slot / meta / transaction）。
    #[test]
    fn derefs_to_transaction_format() {
        let ctx = TxCtx::new(empty_tx(7));
        assert_eq!(ctx.slot, 7);
        assert!(ctx.meta.is_none());
        assert_eq!(ctx.transaction.signatures.len(), 0);
    }
}
