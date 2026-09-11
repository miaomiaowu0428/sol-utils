//! log 事件 → 伪 CPI 指令：**注册式**调度。
//!
//! 为什么需要它：log 里的事件不像 CPI 指令那样有统一编码，现实里至少两种：
//! - anchor 系（cpmm / clmm / dlmm_v2 / pumpswap …）：`Program data: <b58|b64>`，
//!   payload 以 8 字节事件 discriminator 开头；
//! - Raydium AMM v4：`Program log: ray_log: <b64>`，payload 以 1 字节 `log_type` 开头。
//!
//! 所以这里只做**调度**，不硬编码任何协议：
//! 各协议库自己实现解析函数，用 `inventory::submit!` 注册；`flatten_instructions` /
//! `parse_fetched_json` 在处理完真实指令后调 [`parse_log_events`] 补齐。
//!
//! utils 自身也只是一个**注册者**（内置 anchor `Program data:` 的通用格式），
//! [`parse_log_events`] 里没有任何特例分支。
//!
//! # 注册示例
//! ```ignore
//! inventory::submit! {
//!     utils::log_events::LogEventParser("raydium-amm-v4:ray_log", parse_ray_log)
//! }
//! ```

use solana_sdk::pubkey::Pubkey;

use crate::ParsedInstruction;

/// log 事件解析器：输入整段 log，产出若干"假 CPI 指令"。
///
/// 无状态，故用 `fn` 指针 —— `inventory::submit!` 要求 const 构造，闭包不行。
pub type LogEventParserFn = fn(&[String], u64) -> Vec<ParsedInstruction>;

/// 一个已注册的 log 事件解析器：`(名字, 解析函数)`。
///
/// 名字只用于诊断（见 [`registered_log_parsers`]），不参与去重。
pub struct LogEventParser(pub &'static str, pub LogEventParserFn);

inventory::collect!(LogEventParser);

// 内置注册：anchor `sol_log_data` 的通用 `Program data:` 格式。
//
// 注意它**不是**写在 [`parse_log_events`] 里的特例，而是和其他协议一样通过注册进入。
inventory::submit! {
    LogEventParser("anchor:Program data", anchor_program_data_events)
}

/// 调度：跑所有已注册的解析器并拼接结果。
///
/// 迭代顺序不做保证（`inventory` 不保证顺序），各解析器之间必须互相独立。
pub fn parse_log_events(log_messages: &[String], slot: u64) -> Vec<ParsedInstruction> {
    let mut out = Vec::new();
    for p in inventory::iter::<LogEventParser> {
        out.extend((p.1)(log_messages, slot));
    }
    out
}

/// 当前已注册解析器的名字（诊断用）。
pub fn registered_log_parsers() -> Vec<&'static str> {
    inventory::iter::<LogEventParser>.into_iter().map(|p| p.0).collect()
}

/// `sol_log_data` 在 logMessages 中输出的行前缀。
const LOG_DATA_PREFIX: &str = "Program data: ";

/// 边扫 log 边维护 invoke/success 调用栈，对每条"非控制行"回调 `(当前 program, 行内容)`。
///
/// 各协议解析器可直接复用它来定位"这条 log 属于哪个程序"：
/// AMM v4 的 `Program log: ray_log: …` 前面通常自带一行
/// `Program log: Program ID: <pubkey>`，用栈也能正确归属。
///
/// 控制行（`Program X invoke [...]` / `Program X success|failed`）不触发回调。
pub fn walk_log_with_program_stack<F: FnMut(Pubkey, &str)>(log_messages: &[String], mut f: F) {
    let mut stack: Vec<Pubkey> = Vec::new();
    for line in log_messages {
        let line = line.as_str();
        if let Some(rest) = line.strip_prefix("Program ") {
            let head = rest.split(' ').next().unwrap_or("");
            if rest.contains(" invoke") {
                if let Ok(pk) = head.parse::<Pubkey>() {
                    stack.push(pk);
                }
                continue;
            }
            if rest.contains(" success") || rest.contains(" failed") {
                let _ = stack.pop();
                continue;
            }
        }
        if let Some(program) = stack.last() {
            f(*program, line);
        }
    }
}

/// anchor `sol_log_data` 事件：`Program data: <payload>`。
///
/// - 严格绑定：`Program data:` 归到当前调用栈顶的程序；
/// - data = 原始 log 字节（`[8 字节事件 disc][payload]`，**无** e445 前缀）；
/// - 编码自适应：优先 base58（标准 RPC / geyser），含 `+/=` 或失败则按 base64。
fn anchor_program_data_events(log_messages: &[String], slot: u64) -> Vec<ParsedInstruction> {
    let mut out = Vec::new();
    walk_log_with_program_stack(log_messages, |program, line| {
        if let Some(payload) = line.strip_prefix(LOG_DATA_PREFIX)
            && let Some(data) = decode_log_data(payload)
        {
            out.push(ParsedInstruction {
                program,
                accounts: Vec::new(),
                data,
                slot,
            });
        }
    });
    out
}

/// 自适应解码 log 数据：base58（标准）或 base64（某些 explorer dump）。
fn decode_log_data(s: &str) -> Option<Vec<u8>> {
    use base64::Engine;
    let t = s.trim();
    if t.is_empty() {
        return None;
    }
    if t.contains('=') || t.contains('+') || t.contains('/') {
        return base64::engine::general_purpose::STANDARD.decode(t).ok();
    }
    if let Ok(v) = bs58::decode(t).into_vec() {
        return Some(v);
    }
    base64::engine::general_purpose::STANDARD.decode(t).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 一笔真实的 pumpswap/cpmm 风格交易：`Program data:` 归属到当前栈顶程序。
    #[test]
    fn anchor_program_data_is_attributed_to_top_of_stack() {
        let logs = vec![
            "Program CPMMoo8L3F4NbTegBCKVNunggL7H1ZpdTHKxQB5qKP1C invoke [2]".to_string(),
            "Program log: Instruction: SwapBaseInput".to_string(),
            // base58 编码的 payload（8 字节 disc + 少量数据）
            "Program data: 5NmzYNF3Q5B7YfKEoYdGKb".to_string(),
            "Program CPMMoo8L3F4NbTegBCKVNunggL7H1ZpdTHKxQB5qKP1C success".to_string(),
        ];
        let events = parse_log_events(&logs, 42);
        assert_eq!(events.len(), 1, "应解析出 1 条 anchor 事件");
        assert_eq!(events[0].slot, 42);
        assert_eq!(events[0].accounts.len(), 0);
        assert_eq!(
            events[0].program.to_string(),
            "CPMMoo8L3F4NbTegBCKVNunggL7H1ZpdTHKxQB5qKP1C"
        );
        assert!(!events[0].data.is_empty());
    }

    /// 控制行不产生事件；未注册任何匹配格式时返回空。
    #[test]
    fn no_events_for_control_lines_only() {
        let logs = vec![
            "Program 11111111111111111111111111111111 invoke [1]".to_string(),
            "Program 11111111111111111111111111111111 success".to_string(),
        ];
        assert!(parse_log_events(&logs, 1).is_empty());
    }

    /// 内置的 anchor 解析器必须已注册（utils 自己也走注册路径）。
    #[test]
    fn anchor_parser_is_registered() {
        let names = registered_log_parsers();
        assert!(
            names.contains(&"anchor:Program data"),
            "内置 anchor 解析器未注册: {names:?}"
        );
    }
}
