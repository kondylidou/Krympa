use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Level {
    Error = 1,
    Warn = 2,
    Info = 3,
    Debug = 4,
}

fn parse_level(s: &str) -> Level {
    match s.trim().to_ascii_lowercase().as_str() {
        "error" => Level::Error,
        "warn" | "warning" => Level::Warn,
        "debug" => Level::Debug,
        _ => Level::Info,
    }
}

fn current_level() -> Level {
    static LEVEL: OnceLock<Level> = OnceLock::new();
    *LEVEL.get_or_init(|| {
        let level = std::env::var("KRYMPA_LOG").unwrap_or_else(|_| "info".to_string());
        parse_level(&level)
    })
}

pub fn enabled(level: Level) -> bool {
    level <= current_level()
}

pub fn log(level: Level, msg: String) {
    if !enabled(level) {
        return;
    }
    match level {
        Level::Error | Level::Warn => eprintln!("{}", msg),
        Level::Info | Level::Debug => println!("{}", msg),
    }
}

#[macro_export]
macro_rules! klog_error {
    ($($arg:tt)*) => {{
        if $crate::logging::enabled($crate::logging::Level::Error) {
            $crate::logging::log($crate::logging::Level::Error, format!($($arg)*));
        }
    }};
}

#[macro_export]
macro_rules! klog_warn {
    ($($arg:tt)*) => {{
        if $crate::logging::enabled($crate::logging::Level::Warn) {
            $crate::logging::log($crate::logging::Level::Warn, format!($($arg)*));
        }
    }};
}

#[macro_export]
macro_rules! klog_info {
    ($($arg:tt)*) => {{
        if $crate::logging::enabled($crate::logging::Level::Info) {
            $crate::logging::log($crate::logging::Level::Info, format!($($arg)*));
        }
    }};
}

#[macro_export]
macro_rules! klog_debug {
    ($($arg:tt)*) => {{
        if $crate::logging::enabled($crate::logging::Level::Debug) {
            $crate::logging::log($crate::logging::Level::Debug, format!($($arg)*));
        }
    }};
}
