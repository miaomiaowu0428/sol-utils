//! 三个来源共享的解析逻辑。
//!
//! 这里放"只要能拿到「账户列表 + 指令 + 内部指令 + 日志」就能做"的事情，
//! 与交易来自 grpc / rpc / shred 无关。

use solana_sdk::message::compiled_instruction::CompiledInstruction;
use solana_sdk::message::VersionedMessage;
use solana_sdk::pubkey::Pubkey;

use crate::parse_rpc_fetched_json::BalanceChange;
use crate::{IndexedInstruction, ParsedInstruction};

/// 解析失败的原因。
#[derive(Debug)]
pub enum ParseError {
    /// 消息体缺失（grpc 的 `transaction.message` 为空）。
    MissingMessage,
    /// 消息头缺失。
    MissingHeader,
    /// 字节长度不合法（公钥、签名、hash 等）。
    BadBytes(&'static str),
    /// 交易字节反序列化失败。
    Deserialize(String),
    /// 来源本身不提供该信息（例如 shred 流没有 meta）。
    Unsupported(&'static str),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingMessage => write!(f, "transaction message missing"),
            Self::MissingHeader => write!(f, "message header missing"),
            Self::BadBytes(what) => write!(f, "invalid bytes for {what}"),
            Self::Deserialize(e) => write!(f, "deserialize failed: {e}"),
            Self::Unsupported(what) => write!(f, "source does not provide: {what}"),
        }
    }
}

impl std::error::Error for ParseError {}

/// 交易级资源限制（compute budget / priority fee）的原始来源。
///
/// **为什么需要枚举而不是直接拍平成一组 `Option<u32>`**
///
/// V1 和 V0/Legacy 表达这些参数的方式根本不同：
///
/// - **V1**：参数写在消息的 `config` 里，是消息结构的一部分，
///   网络只需定长读取就能排序，不用扫指令。
/// - **V0/Legacy**：参数藏在 `ComputeBudgetProgram` 指令（`data[0]` 是
///   tag）里，必须逐条扫描反序列化才能拿到。
///
/// 两者的**默认值语义也不同**：V1 的 `None` 表示"用 0"（不是无限制），
/// 而 V0 不写 ComputeBudget 指令表示"用运行时默认值"。直接拍平会丢信息。
///
/// 所以这里保留来源标记，由下游决定怎么归一化。
///
/// ## 取值辅助
///
/// [`TxConfig::compute_unit_limit`] / [`TxConfig::priority_fee`] 提供
/// "尽力而为"的统一读取，但**不处理默认值差异**——需要精确语义时
/// 请自行 match 三个变体。
#[derive(Debug, Clone, Default)]
pub struct TxConfig {
    /// V1 消息自带的 config（`None` 表示这条交易不是 V1，或 V1 未设该字段）。
    pub v1: Option<V1Config>,
    /// V0/Legacy 扫描 ComputeBudget 指令得到的值（`None` 表示没扫到相关指令）。
    pub compute_budget: Option<ComputeBudgetValues>,
}

/// V1 消息的 config 字段（原样搬运，不做语义转换）。
///
/// 注意默认值语义：`None` 表示**取 0**，而不是"无限制"。
#[derive(Debug, Clone, Copy)]
pub struct V1Config {
    /// 优先费，单位 lamports。
    pub priority_fee: Option<u64>,
    /// 最大 compute unit。`None` 表示用 `0`。
    pub compute_unit_limit: Option<u32>,
    /// 最大可加载账户数据字节数。`None` 表示用 `0`。
    pub loaded_accounts_data_size_limit: Option<u32>,
    /// 堆大小（字节），必须是 1024 的倍数。`None` 表示 32KB。
    pub heap_size: Option<u32>,
}

/// 从 V0/Legacy 的 `ComputeBudgetProgram` 指令里扫出的值。
///
/// 没扫到对应指令时字段为 `None`，此时链上会用**运行时默认值**
/// （与 V1 的"用 0"语义不同）。
#[derive(Debug, Clone, Copy, Default)]
pub struct ComputeBudgetValues {
    /// `SetComputeUnitLimit`（tag 2）。
    pub compute_unit_limit: Option<u32>,
    /// `SetComputeUnitPrice`（tag 3），单位 micro-lamports。
    pub compute_unit_price: Option<u64>,
    /// `SetLoadedAccountsDataSizeLimit`（tag 4）。
    pub loaded_accounts_data_size_limit: Option<u32>,
}

impl TxConfig {
    /// 尽力而为地取 compute unit limit（不做默认值归一化）。
    ///
    /// V1 优先；没有 V1 config 时回退到 ComputeBudget 指令。
    pub fn compute_unit_limit(&self) -> Option<u32> {
        self.v1
            .as_ref()
            .and_then(|v| v.compute_unit_limit)
            .or_else(|| self.compute_budget.as_ref().and_then(|c| c.compute_unit_limit))
    }

    /// 尽力而为地取优先费提示（不做默认值归一化）。
    ///
    /// V1 的 `priority_fee` 是 lamports；ComputeBudget 的 `compute_unit_price`
    /// 是 micro-lamports **单价**。两者单位不同，这里只做"取出来"，
    /// 换算由下游决定。
    pub fn priority_fee_hint(&self) -> Option<u64> {
        self.v1
            .as_ref()
            .and_then(|v| v.priority_fee)
            .or_else(|| self.compute_budget.as_ref().and_then(|c| c.compute_unit_price))
    }
}

/// ComputeBudgetProgram 的指令 tag（`data[0]`）。
///
/// 取自 `solana_compute_budget_interface::ComputeBudgetInstruction`。
///
/// 注意：这些是**指令体内的 tag，不是账户地址**，所以不属于
/// `const-accounts`（那个 crate 只放地址常量）。
pub mod compute_budget_tag {
    pub const REQUEST_UNITS_DEPRECATED: u8 = 0;
    pub const REQUEST_HEAP_FRAME: u8 = 1;
    pub const SET_COMPUTE_UNIT_LIMIT: u8 = 2;
    pub const SET_COMPUTE_UNIT_PRICE: u8 = 3;
    pub const SET_LOADED_ACCOUNTS_DATA_SIZE_LIMIT: u8 = 4;
}

/// 从 V1 消息的 config 提炼成 [`V1Config`]。
pub fn v1_config_of(config: &solana_sdk::message::v1::TransactionConfig) -> V1Config {
    V1Config {
        priority_fee: config.priority_fee,
        compute_unit_limit: config.compute_unit_limit,
        loaded_accounts_data_size_limit: config.loaded_accounts_data_size_limit,
        heap_size: config.heap_size,
    }
}

/// 扫指令列表，提取 ComputeBudgetProgram 设置的值。
///
/// 只认 tag + 长度都匹配的指令；`request_units_deprecated` 和
/// `request_heap_frame` 忽略（前者已废弃，后者对应 V1 的 `heap_size`，
/// 但 V0 里它不影响计费，暂不收集）。
///
/// `program_id` 用于过滤：只处理来自 ComputeBudgetProgram 的指令。
pub fn scan_compute_budget(
    instructions: &[CompiledInstruction],
    account_keys: &[Pubkey],
    program_id: &Pubkey,
) -> Option<ComputeBudgetValues> {
    let mut out = ComputeBudgetValues::default();
    let mut found = false;

    for ix in instructions {
        if account_keys.get(ix.program_id_index as usize) != Some(program_id) {
            continue;
        }
        let Some((&tag, rest)) = ix.data.split_first() else {
            continue;
        };
        match tag {
            compute_budget_tag::SET_COMPUTE_UNIT_LIMIT => {
                if let Ok(bytes) = <[u8; 4]>::try_from(rest) {
                    out.compute_unit_limit = Some(u32::from_le_bytes(bytes));
                    found = true;
                }
            }
            compute_budget_tag::SET_COMPUTE_UNIT_PRICE => {
                if let Ok(bytes) = <[u8; 8]>::try_from(rest) {
                    out.compute_unit_price = Some(u64::from_le_bytes(bytes));
                    found = true;
                }
            }
            compute_budget_tag::SET_LOADED_ACCOUNTS_DATA_SIZE_LIMIT => {
                if let Ok(bytes) = <[u8; 4]>::try_from(rest) {
                    out.loaded_accounts_data_size_limit = Some(u32::from_le_bytes(bytes));
                    found = true;
                }
            }
            _ => {}
        }
    }

    found.then_some(out)
}

/// 从消息里提炼 [`TxConfig`]。
///
/// 三种消息的处理方式不同，这正是 V1 最需要注意的地方：
///
/// - **V1**：config 在消息结构里，直接搬运。**不扫指令**——V1 的
///   compute budget 不在 `ComputeBudgetProgram` 指令里，扫也扫不到。
/// - **V0 / Legacy**：扫主指令里的 `ComputeBudgetProgram` 调用。
///
/// 注意 `inner_instructions` 里的 ComputeBudget 不参与——链上规则是
/// 只认顶层指令。
pub fn tx_config_of(msg: &VersionedMessage, instructions: &[CompiledInstruction], account_keys: &[Pubkey]) -> TxConfig {
    match msg {
        VersionedMessage::V1(m) => TxConfig {
            v1: Some(v1_config_of(&m.config)),
            compute_budget: None,
        },
        VersionedMessage::V0(_) | VersionedMessage::Legacy(_) => TxConfig {
            v1: None,
            compute_budget: scan_compute_budget(instructions, account_keys, &const_accounts::COMPUTE_BUDGET_PROGRAM),
        },
    }
}

/// 统一后的解析产物，三个来源都归到这里。
///
/// 字段与旧 API 保持一致的语义，下游切换来源时不需要改调用代码。
#[derive(Debug, Clone)]
pub struct ParsedTx {
    pub slot: u64,
    /// 完整账户列表：静态账户 + ALT 加载的 writable + readonly。
    /// 指令的 `program_id_index` / `accounts` 索引的就是它。
    pub account_keys: Vec<Pubkey>,
    /// 按稳定顺序展开的指令序列，索引规则同旧 API。
    ///
    /// 注意：**V1 的 compute budget 会以伪装指令的形式出现在这里**
    /// （见 [`inject_v1_config_as_instructions`]），index 为
    /// `"SetCuLimit"` / `"SetCuPrice"`。
    pub instructions: Vec<IndexedInstruction>,
    /// 交易级资源限制的原始来源，见 [`TxConfig`]。
    ///
    /// 注意：V1 的这些参数在消息结构里，不在指令里，所以
    /// **真正权威的来源是这个字段**；`instructions` 里的伪装指令
    /// 只是为了让基于指令匹配的下游能用。
    pub config: TxConfig,
    /// 余额变化（SOL + SPL token）。
    ///
    /// **`None` 表示来源拿不到执行结果**（如 shred 流），不等于"没有变化"。
    /// `Some(vec![])` 才是"执行了但余额没变"。
    pub balance_changes: Option<Vec<BalanceChange>>,
}

/// 取"完整"账户列表：静态账户在前，随后是 ALT 加载的 writable、readonly。
///
/// 顺序不能错——链上执行时的账户索引就是按这个顺序排的：
/// `static_account_keys` 是消息里直接列出的，`loaded_addresses` 是运行时
/// 从 ALT 解析出来的，链上把它们拼在静态账户之后。
///
/// - `msg`：版本化消息。
/// - `loaded_writable` / `loaded_readonly`：来自 meta 的 ALT 地址。
///   若来源没有 meta（如 shred），调用方传空切片即可，
///   此时 v0 消息里引用了 ALT 的指令会拿不到账户（这是数据本身的限制，
///   不是解析 bug）。
pub fn account_keys_of(msg: &VersionedMessage, loaded_writable: &[Pubkey], loaded_readonly: &[Pubkey]) -> Vec<Pubkey> {
    let mut keys: Vec<Pubkey> = msg.static_account_keys().to_vec();
    keys.extend_from_slice(loaded_writable);
    keys.extend_from_slice(loaded_readonly);
    keys
}

/// 把消息里的指令展开成 `IndexedInstruction` 序列。
///
/// 索引规则（与旧 API 完全一致）：
/// - 主指令：`"1"`、`"2"`…（从 1 开始）
/// - 内部指令：`"1.1"`、`"1.2"`…（父索引.子序号，都从 1 开始）
/// - 日志重建的假 CPI：`"logevent.1"`、`"logevent.2"`…
///
/// - `instructions`：主指令。v0/legacy 消息都从 `msg.instructions()` 取。
/// - `inner_instructions`：按父指令下标分组的内部指令，
///   `Vec<(父指令下标, 内部指令列表)>`。来源没有 meta 时传空。
/// - `log_messages`：日志，用于重建假 CPI。来源没有 meta 时传空。
pub fn flatten_instructions_with_keys(
    instructions: &[CompiledInstruction],
    inner_instructions: &[(usize, Vec<CompiledInstruction>)],
    log_messages: Option<&[String]>,
    keys: &[Pubkey],
    slot: u64,
) -> Vec<IndexedInstruction> {
    let mut out = Vec::new();

    let parse_ix = |ix: &CompiledInstruction| -> ParsedInstruction {
        let program = keys.get(ix.program_id_index as usize).cloned().unwrap_or_default();
        let accounts = ix.accounts.iter().filter_map(|&i| keys.get(i as usize).cloned()).collect();
        ParsedInstruction {
            program,
            accounts,
            data: ix.data.clone(),
            slot,
        }
    };

    for (i, main_ix) in instructions.iter().enumerate() {
        out.push(IndexedInstruction {
            index: (i + 1).to_string(),
            instruction: parse_ix(main_ix),
            slot,
        });

        if let Some((_, inner)) = inner_instructions.iter().find(|(idx, _)| *idx == i) {
            for (j, inner_ix) in inner.iter().enumerate() {
                out.push(IndexedInstruction {
                    index: format!("{}.{}", i + 1, j + 1),
                    instruction: parse_ix(inner_ix),
                    slot,
                });
            }
        }
    }

    // 追加：log 事件重建出的"假 CPI 指令"（由各协议通过 `log_events` 注册的解析器产出）。
    if let Some(logs) = log_messages {
        for (k, inst) in crate::log_events::parse_log_events(logs, slot).into_iter().enumerate() {
            out.push(IndexedInstruction {
                index: format!("{LOG_EVENT_INDEX_PREFIX}{}", k + 1),
                instruction: inst,
                slot,
            });
        }
    }

    out
}

/// 伪装指令的 index 名。
///
/// **不带点**，所以 `IndexedInstruction::is_main_ix()` 会判定为 `true`，
/// 下游按"主指令"遍历时能自然看到它们——这正是我们要的效果：
/// 让 V1 的 config 在下游眼里和真实的 ComputeBudget 指令长得一样。
///
/// ⚠️ 代价：它们**不在** `log_messages` 的 `invoke [1]` 序列里。任何要跟日志
/// **按位置**对齐的代码（典型：从 `consumed N of M` 取每条指令的 CU）都必须
/// 先用 [`IndexedInstruction::absolute_index`](crate::IndexedInstruction::absolute_index)
/// 排除它们，否则每笔 V1 交易都会整体错位。
pub mod synthetic_index {
    /// 对应 `SetComputeUnitLimit`。
    pub const SET_CU_LIMIT: &str = "SetCuLimit";
    /// 对应 `SetComputeUnitPrice`。
    pub const SET_CU_PRICE: &str = "SetCuPrice";
    /// 对应 `SetLoadedAccountsDataSizeLimit`。
    pub const SET_LOADED_ACCOUNTS_DATA_SIZE_LIMIT: &str = "SetLoadedAccountsDataSizeLimit";

    /// 是否是 V1 config 的伪装 index 名。
    ///
    /// **只认这三条常量**，不靠"是不是纯数字"来判断——将来改命名也不会漏。
    pub fn is_synthetic(name: &str) -> bool {
        name == SET_CU_LIMIT || name == SET_CU_PRICE || name == SET_LOADED_ACCOUNTS_DATA_SIZE_LIMIT
    }
}

/// 日志事件重建出的**假 CPI** 的 index 前缀（`"logevent.1"`、`"logevent.2"`…）。
///
/// 它们同样**不在** `invoke [1]` 序列里（是"事后补出来的"），
/// 且排在所有真实主指令**之后**。
pub const LOG_EVENT_INDEX_PREFIX: &str = "logevent.";

/// V1 的 `priority_fee`（lamports **总额**）→ **等效的** `SetComputeUnitPrice`
/// 单价（micro-lamports/CU）。
///
/// # 为什么必须反解，而不是直接填
///
/// 两种消息对"优先费"的表达方式根本不同：
///
/// | 消息 | 表达 | 算法 |
/// |---|---|---|
/// | V0 / Legacy | 单价 `micro_lamports` + 上限 `units` | `price × limit / 1e6` |
/// | V1 | `config.priority_fee` | **直接就是 lamports 总额** |
///
/// 伪装指令的全部意义就是「让 V1 在只看指令的下游眼里和 V0 长得一样」。
/// 如果直接把 `priority_fee` 塞进 `micro_lamports` 字段，任何按 V0 口径
/// 算 `price × limit / 1e6` 的消费者都会得到 `priority_fee × limit / 1e6`
/// —— 20 万 CU 下**少算 5 倍**，高费率/竞价判定直接失效（曾因此让
/// `dash_snipe_high_fee` 的 V1 对手全被读成 gas = 0）。
///
/// 所以这里反解：
///
/// ```text
/// price = ceil(priority_fee × 1e6 / cu_limit)
/// ```
///
/// 于是 `floor(price × limit / 1e6) ∈ [priority_fee, priority_fee + 1]`
/// —— 向上取整，残差在 gas 口径下 **≤ 1 lamport**（宁可多报 1 lamport，
/// 也不要因为截断少报一档）。
///
/// # 边界
///
/// - `cu_limit == 0`（V1 里 `compute_unit_limit` 缺省即取 0，这种交易本身就
///   跑不完任何 CU）**没有等效单价** —— 返回 `None`，调用方不生成 price 伪装指令。
/// - 只有 `cu_limit ≤ 运行时上限（1_400_000）`才与 V0 口径**严格**等价：
///   夹取 limit 的消费者（如 `sol-parser-sdk` 的 `min(limit, MAX_CU_LIMIT)`）
///   在 limit 更大时会按夹取后的值算。V1 的实际 limit 基本都 ≤ 该上限。
pub fn v1_equivalent_cu_price(priority_fee_lamports: u64, cu_limit: u32) -> Option<u64> {
    if cu_limit == 0 {
        return None;
    }
    let micro_lamports = (priority_fee_lamports as u128).saturating_mul(1_000_000);
    let price = micro_lamports.div_ceil(cu_limit as u128);
    Some(u64::try_from(price).unwrap_or(u64::MAX))
}

/// 把 [`V1Config`] 投影成 1~3 条 `ComputeBudgetProgram` 伪装指令。
///
/// **这是「V1 → V0 口径」唯一的投影点**：`tx_parse` 的三个来源
/// （grpc / rpc / shred，经 [`inject_v1_config_as_instructions`]）和
/// 信号链路的指令展平（`utils::flatten_main_instructions`）都调它，
/// 保证同一笔 V1 交易在两条链路上看到的值完全一致。
///
/// 顺序与真实交易惯例一致：**先 limit，再 price，最后 loaded size**。
///
/// 取值口径：
///
/// - `compute_unit_limit`：V1 与 V0 语义相同（都是 CU 上限），**原样搬运**；
/// - `priority_fee`：V1 是总额，必须按 limit **折算成等效单价**，
///   见 [`v1_equivalent_cu_price`]（不能直接填总额）；
/// - `loaded_accounts_data_size_limit`：语义相同，原样搬运。
pub fn v1_config_as_instructions(config: &V1Config, slot: u64) -> Vec<IndexedInstruction> {
    fn make_ix(name: &str, data: Vec<u8>, slot: u64) -> IndexedInstruction {
        IndexedInstruction {
            index: name.to_string(),
            instruction: ParsedInstruction {
                program: const_accounts::COMPUTE_BUDGET_PROGRAM,
                accounts: Vec::new(),
                data,
                slot,
            },
            slot,
        }
    }

    let mut synthetic: Vec<IndexedInstruction> = Vec::with_capacity(3);

    // ① limit：与 V0 同语义，原样搬运。
    if let Some(cu) = config.compute_unit_limit {
        let mut data = vec![compute_budget_tag::SET_COMPUTE_UNIT_LIMIT];
        data.extend_from_slice(&cu.to_le_bytes());
        synthetic.push(make_ix(synthetic_index::SET_CU_LIMIT, data, slot));
    }

    // ② price：V1 的 `priority_fee` 是**总额**，必须除以 limit 折算成单价。
    //    直接填总额会差 limit/1e6 倍（见 `v1_equivalent_cu_price` 文档）。
    if let Some(fee) = config.priority_fee
        && let Some(price) = v1_equivalent_cu_price(fee, config.compute_unit_limit.unwrap_or(0))
    {
        let mut data = vec![compute_budget_tag::SET_COMPUTE_UNIT_PRICE];
        data.extend_from_slice(&price.to_le_bytes());
        synthetic.push(make_ix(synthetic_index::SET_CU_PRICE, data, slot));
    }

    // ③ loaded accounts data size：同语义，原样搬运。
    if let Some(size) = config.loaded_accounts_data_size_limit {
        let mut data = vec![compute_budget_tag::SET_LOADED_ACCOUNTS_DATA_SIZE_LIMIT];
        data.extend_from_slice(&size.to_le_bytes());
        synthetic.push(make_ix(synthetic_index::SET_LOADED_ACCOUNTS_DATA_SIZE_LIMIT, data, slot));
    }

    synthetic
}

/// 把 V1 消息的 `config` 伪装成 `ComputeBudgetProgram` 指令，插入指令序列开头。
///
/// # 为什么需要这个
///
/// 主网会**长期** Legacy / V0 / V1 三种格式共存（V1 是 opt-in）。
/// 但 V1 把 compute budget 从"指令"搬到了"消息 config"里，
/// 于是所有"遍历指令、匹配 `ComputeBudgetProgram`"的既有管线
/// 在 V1 交易上会**静默失效**——不报错，只是取不到 CU 值，
/// 结果就是优先级费算错、交易排队靠后甚至上不去链。
///
/// 与其让每个消费点都改成"先查 config 再查指令"（散落各处、漏一处就
/// 静默出错），不如在**解析出口**做一次投影：把 config 还原成
/// 形态完全一致的虚拟指令。这样下游零改动。
///
/// # 伪装保真度
///
/// 生成的指令在下面几方面与真实指令一致，所以下游即使做深度解析也不会出错：
///
/// - `program`：真实的 `ComputeBudgetProgram` id
/// - `data`：真实的编码（tag + little-endian 数值）
/// - `accounts`：空（ComputeBudget 指令不带账户）
/// - 位置：插在序列**最前面**（链上要求 ComputeBudget 指令必须最先出现）
///
/// **关键的一条不是"原样搬运"，而是"口径对齐"**：`priority_fee` 会被反解成
/// 等效单价（[`v1_equivalent_cu_price`]），使 `price × limit / 1e6` 就是这笔
/// 优先费的 lamports 总额。否则按 V0 公式算的下游会拿到一个差 limit/1e6 倍的数。
///
/// 唯一区别是 `index` 用了 `"SetCuLimit"` / `"SetCuPrice"` 这样的名字
/// （不带点 → `is_main_ix()` 为 `true`），而不是数字序号。
///
/// # 只对 V1 生效
///
/// V0/Legacy 的 ComputeBudget 指令**本来就在** `instructions` 里，
/// 重复插入会导致下游读到两次。所以这个函数只处理 `config.v1`。
pub fn inject_v1_config_as_instructions(parsed: &mut ParsedTx) {
    let Some(v1cfg) = parsed.config.v1 else {
        return;
    };

    // 插到最前面，模拟"ComputeBudget 指令必须最先出现"的链上约束。
    let synthetic = v1_config_as_instructions(&v1cfg, parsed.slot);
    parsed.instructions.splice(0..0, synthetic);
}

/// 从官方 meta 计算余额变化（SOL + SPL token）。
///
/// **只依赖官方 `TransactionStatusMeta`**，所以 grpc 路径直接传 meta 即可，
/// rpc 路径则先把 `UiTransactionStatusMeta` 转成官方类型再传（见
/// [`super::ui_meta::ui_meta_to_official`]）。
///
/// - `account_keys`：完整账户列表。用于把 token 余额里的
///   `account_index` 还原成 token account 的 pubkey。
///
/// 返回按 `(owner, mint)` 归并后的变化列表，只保留净值非零的项。
pub fn balance_changes_of(
    meta: &solana_transaction_status::TransactionStatusMeta,
    account_keys: &[Pubkey],
) -> Vec<crate::parse_rpc_fetched_json::BalanceChange> {
    use crate::parse_rpc_fetched_json::{diff_sol_balances, diff_token_balances, merge_balance_changes, BalanceChange};

    let sol = diff_sol_balances(crate::parse_rpc_fetched_json::SolBalanceInput {
        owners: account_keys,
        pre_balances: &meta.pre_balances,
        post_balances: &meta.post_balances,
    });

    let token = match (&meta.pre_token_balances, &meta.post_token_balances) {
        (Some(pre), Some(post)) => convert_and_diff_token_balances(pre, post, account_keys),
        _ => Vec::new(),
    };

    merge_balance_changes([sol, token])
}

/// 把官方 `TransactionTokenBalance` 转成 UI 版后复用既有的 diff 逻辑。
///
/// 这里绕一层是刻意的：既有的 `diff_token_balances` 已经过验证，
/// 不重新实现。官方版和 UI 版的字段几乎一一对应，转换是机械的。
fn convert_and_diff_token_balances(
    pre: &[solana_transaction_status::TransactionTokenBalance],
    post: &[solana_transaction_status::TransactionTokenBalance],
    account_keys: &[Pubkey],
) -> Vec<crate::parse_rpc_fetched_json::BalanceChange> {
    use solana_transaction_status::UiTransactionTokenBalance;

    let to_ui = |v: &[solana_transaction_status::TransactionTokenBalance]| -> Vec<UiTransactionTokenBalance> {
        v.iter()
            .map(|b| UiTransactionTokenBalance {
                account_index: b.account_index,
                mint: b.mint.clone(),
                ui_token_amount: b.ui_token_amount.clone(),
                owner: solana_client::rpc_response::OptionSerializer::Some(b.owner.clone()),
                program_id: solana_client::rpc_response::OptionSerializer::Some(b.program_id.clone()),
            })
            .collect()
    };

    crate::parse_rpc_fetched_json::diff_token_balances(&to_ui(pre), &to_ui(post), account_keys).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 闭环验证：V1 的 config 伪装成指令后，
    /// 能被既有的 `scan_compute_budget` 原样读回，**且 gas 口径等价**。
    ///
    /// 这正是兼容性目标——下游不用知道 V1 的存在，
    /// 按 V0 公式算出来的 gas 就等于 V1 的 `priority_fee`。
    #[test]
    fn v1_config_survives_roundtrip_through_synthetic_instructions() {
        const FEE: u64 = 1234;
        const LIMIT: u32 = 200_000;

        let mut parsed = ParsedTx {
            slot: 42,
            account_keys: vec![const_accounts::COMPUTE_BUDGET_PROGRAM, const_accounts::SYSTEM_PROGRAM],
            instructions: vec![],
            config: TxConfig {
                v1: Some(V1Config {
                    priority_fee: Some(FEE),
                    compute_unit_limit: Some(LIMIT),
                    loaded_accounts_data_size_limit: Some(65_536),
                    heap_size: Some(32_768),
                }),
                compute_budget: None,
            },
            balance_changes: None,
        };

        inject_v1_config_as_instructions(&mut parsed);

        assert_eq!(parsed.instructions.len(), 3, "limit/price/size 三条都应生成");

        // 伪装指令必须是"主指令"语义，下游遍历时才看得到。
        assert!(parsed.instructions.iter().all(|ix| ix.is_main_ix()));

        // 伪装指令的 program 必须是真实的 ComputeBudgetProgram。
        assert!(parsed
            .instructions
            .iter()
            .all(|ix| ix.instruction.program == const_accounts::COMPUTE_BUDGET_PROGRAM));

        // 关键：用既有扫描逻辑读回。
        // ComputeBudget 指令不带账户，直接用空 accounts 构造。
        let compiled: Vec<CompiledInstruction> = parsed
            .instructions
            .iter()
            .map(|ix| CompiledInstruction {
                program_id_index: 0, // account_keys[0] = COMPUTE_BUDGET_PROGRAM
                accounts: Vec::new(),
                data: ix.instruction.data.clone(),
            })
            .collect();

        let scanned = scan_compute_budget(&compiled, &parsed.account_keys, &const_accounts::COMPUTE_BUDGET_PROGRAM)
            .expect("应能扫到 ComputeBudget 值");

        // limit / size 是原样搬运的。
        assert_eq!(scanned.compute_unit_limit, Some(LIMIT));
        assert_eq!(scanned.loaded_accounts_data_size_limit, Some(65_536));

        // price 是**折算后**的等效单价，不是 priority_fee 原值。
        let price = scanned.compute_unit_price.expect("应生成的等效单价");
        assert_ne!(price, FEE, "不能把 V1 的 lamports 总额直接当单价填进去");

        // 核心不变量：按 V0 公式算出来的 gas == V1 的 priority_fee（±取整残差）。
        let gas = price.saturating_mul(LIMIT as u64) / 1_000_000;
        assert!(gas >= FEE, "向上取整：gas({gas}) 不能小于 priority_fee({FEE})");
        assert!(gas - FEE <= 1, "取整残差最多 1 lamport，实际 {} lamports", gas - FEE);
    }

    /// 等效单价：**任意**（fee, limit）组合下，`price × limit / 1e6` 都必须
    /// 复现 fee（向上取整，残差 ≤ 1 lamport）。
    #[test]
    fn v1_equivalent_price_reproduces_fee() {
        // (priority_fee lamports, cu_limit) —— 覆盖整除 / 非整除 / 大额 / 小额
        const CASES: &[(u64, u32)] = &[
            (0, 200_000),
            (1, 200_000),
            (999, 200_000),
            (44_800, 140_000),   // 320_000 micro-lamports × 140k CU / 1e6（整除）
            (40_000, 200_000),   // 200_000 micro-lamports × 200k CU / 1e6（整除）
            (1234, 200_000),     // 非整除
            (15_000_000_000, 200_000), // 15 SOL：高费率档
            (15_000_000_000, 1_400_000), // 15 SOL + 最大 CU
        ];

        for &(fee, limit) in CASES {
            let price = v1_equivalent_cu_price(fee, limit).expect("limit > 0 一定有解");
            let gas = price.saturating_mul(limit as u64) / 1_000_000;
            assert!(gas >= fee, "fee={fee} limit={limit} price={price} gas={gas} 少报了");
            assert!(gas - fee <= 1, "fee={fee} limit={limit} price={price} gas={gas} 残差过大");
        }

        // 整除的样本必须**精确**还原成原来的单价（不能因为取整漂移，
        // 否则 `same_cu_1_plus_n` / `spam_min_1` 那类「单价 == 常量」的匹配会失效）。
        assert_eq!(v1_equivalent_cu_price(44_800, 140_000), Some(320_000));
        assert_eq!(v1_equivalent_cu_price(40_000, 200_000), Some(200_000));

        // limit = 0 无解（V1 缺省 compute_unit_limit 的语义），不生成 price 伪装指令。
        assert_eq!(v1_equivalent_cu_price(1234, 0), None);
    }

    /// `priority_fee` 有值但 `compute_unit_limit` 缺省（= 0）时，
    /// 只能生成 limit 伪装指令，不能瞎编一个单价。
    #[test]
    fn v1_without_cu_limit_does_not_invent_price() {
        let ixs = v1_config_as_instructions(
            &V1Config {
                priority_fee: Some(15_000_000_000),
                compute_unit_limit: None,
                loaded_accounts_data_size_limit: None,
                heap_size: None,
            },
            7,
        );

        assert!(ixs.is_empty(), "limit 缺省时 infeasible：既无 limit 也无价格，不应生成任何伪装指令");
    }

    /// V0/Legacy 不该被注入——它们的 ComputeBudget 指令本来就在。
    #[test]
    fn non_v1_config_is_not_injected() {
        let mut parsed = ParsedTx {
            slot: 1,
            account_keys: vec![const_accounts::COMPUTE_BUDGET_PROGRAM],
            instructions: vec![],
            config: TxConfig {
                v1: None,
                compute_budget: Some(ComputeBudgetValues {
                    compute_unit_limit: Some(100),
                    compute_unit_price: Some(7),
                    loaded_accounts_data_size_limit: None,
                }),
            },
            balance_changes: None,
        };

        inject_v1_config_as_instructions(&mut parsed);

        assert!(parsed.instructions.is_empty(), "非 V1 不应注入任何指令");
    }
}
