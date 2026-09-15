//! 信号来源类型（基建与业务共用）
//!
//! 放在 `utils` 而非业务 crate，是为了让 `shred-dispatcher` 等**基建 crate**
//! 能在不产生循环依赖的前提下，在 `ShredContext` 里携带信号来源。

use std::fmt::Display;

/// 信号来自哪个 shred 源。
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum ShredFrom {
    Jito,
    Unshred,
    Tempo,
    NextBlock,
    Node1,
    Unknown,
}

/// 信号的总体来源：gRPC 流 / shred 流（具体哪个源）。
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum SignalOrigin {
    Grpc,
    Shred { from: ShredFrom },
}

impl Display for SignalOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
