#[macro_export]
macro_rules! log_time {
    ($name:expr, $expr:expr) => {{
        let start = std::time::Instant::now();
        let result = $expr;
        let elapsed = start.elapsed();
        let ms = elapsed.as_secs_f64() * 1000.0;
        info!("[timeit] {} cost {:.3} ms", $name, ms);
        result
    }};
}

#[macro_export]
macro_rules! timeit {
    ($expr:expr) => {{
        let start = std::time::Instant::now();
        let result = $expr;
        let elapsed = start.elapsed();
        let ms = elapsed.as_secs_f64() * 1000.0;
        (result, ms)
    }};
}

#[macro_export]
macro_rules! retry_result {
    ($times:expr, $expr:expr) => {{
        let mut last_err = None;
        let mut i = 0;
        loop {
            if i >= $times {
                break Err(last_err.expect("All retries failed"));
            }
            match $expr {
                Ok(val) => break Ok(val),
                Err(e) => last_err = Some(e),
            }
            i += 1;
        }
    }};
}

#[macro_export]
macro_rules! retry_option {
    ($times:expr, $expr:expr) => {{
        let mut i = 0;
        loop {
            if i >= $times {
                break None;
            }
            match $expr {
                Some(val) => break Some(val),
                None => {}
            }
            i += 1;
        }
    }};
}

/// 支持每次尝试都加超时的 retry_result 宏
#[macro_export]
macro_rules! retry_result_timeout {
    ($times:expr, $timeout:expr, $expr:expr) => {{
        let mut last_err = None;
        let mut i = 0;
        loop {
            if i >= $times {
                break Err(last_err.expect("All retries failed"));
            }
            let fut = async { $expr };
            match tokio::time::timeout($timeout, fut).await {
                Ok(Ok(val)) => break Ok(val),
                Ok(Err(e)) => last_err = Some(e),
                Err(_) => {
                    ::log::debug!("第 {i} 次尝试超时");
                    last_err = Some("timeout".into())
                }
            }
            i += 1;
        }
    }};
}

/// 支持每次尝试都加超时的 retry_option 宏
#[macro_export]
macro_rules! retry_option_timeout {
    ($times:expr, $timeout:expr, $expr:expr) => {{
        let mut i = 0;
        loop {
            if i >= $times {
                break None;
            }
            let fut = async { $expr };
            match tokio::time::timeout($timeout, fut).await {
                Ok(Some(val)) => break Some(val),
                Ok(None) => {}
                Err(_) => {
                    ::log::debug!("第 {i} 次尝试超时")
                } // 超时也继续重试
            }
            i += 1;
        }
    }};
}

/// 定义一个全局 channel 模块的宏，包含事件类型定义
#[macro_export]
macro_rules! global_channel {
    (
        mod $mod_name:ident {
            $(#[$event_meta:meta])*
            struct $event_name:ident {
                $($field_name:ident: $field_type:ty),* $(,)?
            }
        }
    ) => {
        pub mod $mod_name {
            use super::*;

            /// 事件数据结构
            $(#[$event_meta])*
            #[derive(Debug, Clone)]
            pub struct $event_name {
                $(pub $field_name: $field_type),*
            }

            /// 全局 channel 实例（sender/receiver）
            static GLOBAL_CHANNEL: std::sync::LazyLock<(
                tokio::sync::mpsc::UnboundedSender<$event_name>,
                tokio::sync::RwLock<tokio::sync::mpsc::UnboundedReceiver<$event_name>>
            )> = std::sync::LazyLock::new(|| {
                let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<$event_name>();
                (tx, tokio::sync::RwLock::new(rx))
            });

            /// 接收一条事件（从共享队列中取出）
            pub async fn recv() -> Option<$event_name> {
                let mut rx = GLOBAL_CHANNEL.1.write().await;
                rx.recv().await
            }


            /// 发送事件
            pub async fn send(event: $event_name) -> Result<(), tokio::sync::mpsc::error::SendError<$event_name>> {
                GLOBAL_CHANNEL.0.send(event)
            }

            /// 尝试发送事件（不会 panic）
            pub fn try_send(event: $event_name) -> bool {
                GLOBAL_CHANNEL.0.send(event).is_ok()
            }

            pub async fn find(condition: impl Fn(&$event_name) -> bool) -> Option<$event_name> {
                let mut rx = GLOBAL_CHANNEL.1.write().await;
                while let Some(event) = rx.recv().await {
                    if condition(&event) {
                        return Some(event);
                    }
                }
                None
            }
        }
    };
}

/// 定义一个全局广播 channel 模块的宏，包含事件类型定义
#[macro_export]
macro_rules! global_broadcast {
    (
        mod $mod_name:ident {
            $(#[$event_meta:meta])*
            struct $event_name:ident {
                $($field_name:ident: $field_type:ty),* $(,)?
            }
        }
    ) => {
        pub mod $mod_name {
            use super::*;

            /// 事件数据结构
            $(#[$event_meta])*
            #[derive(Debug, Clone)]
            pub struct $event_name {
                $(pub $field_name: $field_type),*
            }

            /// 全局广播 channel 实例（使用较大的默认容量）
            static GLOBAL_BROADCAST: std::sync::LazyLock<tokio::sync::broadcast::Sender<$event_name>> =
                std::sync::LazyLock::new(|| {
                    let (tx, _) = tokio::sync::broadcast::channel::<$event_name>(16384); // 16K 容量，基本等于无界
                    tx
                });

            /// 创建一个新的接收者（订阅广播）
            pub fn subscribe() -> tokio::sync::broadcast::Receiver<$event_name> {
                GLOBAL_BROADCAST.subscribe()
            }

            /// 发送事件到所有订阅者
            pub fn send(event: $event_name) -> Result<usize, tokio::sync::broadcast::error::SendError<$event_name>> {
                GLOBAL_BROADCAST.send(event)
            }

            /// 获取当前订阅者数量
            pub fn receiver_count() -> usize {
                GLOBAL_BROADCAST.receiver_count()
            }
        }
    };
}

#[macro_export]
macro_rules! retry {
    ($times:expr, $expr:expr) => {{
        let mut last_err = None;
        let mut i = 0;
        loop {
            match $expr {
                Ok(val) => break Ok(val),
                Err(e) => {
                    last_err = Some(e);
                }
            }
            i += 1;
            if i >= $times {
                break Err(last_err);
            }
        }
    }};
}


// #[macro_export]
// macro_rules! impl_enum_getters {
//     ($enum_name:ident, $( $field:ident : $ret:ty ),* $(,)?) => {
//         impl $enum_name {
//             $(
//                 pub fn $field(&self) -> $ret {
//                     match self {
//                         $enum_name::V1(inner) => inner.$field,
//                         $enum_name::V2(inner) => inner.$field,
//                     }
//                 }
//             )*
//         }
//     };
// }

#[macro_export]
macro_rules! impl_enum_getters {
    (
        $enum_name:ident,
        variants = [ $( $variant:ident ),+ ],
        fields = [ $( $field:ident : $ret:ty ),+ ]
    ) => {
        impl $enum_name {
            $(
                impl_enum_getters!(@one $enum_name, [$($variant),+], $field : $ret);
            )+
        }
    };

    (@one
        $enum_name:ident,
        [ $( $variant:ident ),+ ],
        $field:ident : $ret:ty
    ) => {
        pub fn $field(&self) -> $ret {
            match self {
                $(
                    $enum_name::$variant(inner) => inner.$field,
                )+
            }
        }
    };
}
