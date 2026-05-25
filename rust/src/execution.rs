use std::sync::OnceLock;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionMode {
    Parallel,
    Sequential,
}

impl ExecutionMode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Parallel => "parallel",
            Self::Sequential => "sequential",
        }
    }
}

static EXECUTION_MODE: OnceLock<ExecutionMode> = OnceLock::new();
static TERM_SIZE_AWARE: OnceLock<bool> = OnceLock::new();

pub fn execution_mode() -> ExecutionMode {
    *EXECUTION_MODE.get_or_init(|| ExecutionMode::Parallel)
}

pub fn set_execution_mode(mode: ExecutionMode) {
    let _ = EXECUTION_MODE.set(mode);
}

pub fn term_size_aware() -> bool {
    *TERM_SIZE_AWARE.get_or_init(|| false)
}

pub fn set_term_size_aware(enabled: bool) {
    let _ = TERM_SIZE_AWARE.set(enabled);
}

/// Strip --sequential / --parallel / --term-size from args;
/// return (mode, term_size_aware, remaining positional args).
/// Default mode is Parallel; term_size_aware defaults to false.
pub fn parse_execution_mode(args: &[String]) -> (ExecutionMode, bool, Vec<String>) {
    let mut mode = ExecutionMode::Parallel;
    let mut tsa = false;
    let mut rest = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--parallel" => mode = ExecutionMode::Parallel,
            "--sequential" => mode = ExecutionMode::Sequential,
            "--term-size" => tsa = true,
            _ => rest.push(arg.clone()),
        }
    }
    (mode, tsa, rest)
}
