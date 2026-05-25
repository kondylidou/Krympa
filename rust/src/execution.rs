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

pub fn execution_mode() -> ExecutionMode {
    *EXECUTION_MODE.get_or_init(|| ExecutionMode::Parallel)
}

pub fn set_execution_mode(mode: ExecutionMode) {
    let _ = EXECUTION_MODE.set(mode);
}

/// Strip --sequential / --parallel from args; return (mode, remaining positional args).
/// Default is Parallel if neither flag is present.
pub fn parse_execution_mode(args: &[String]) -> (ExecutionMode, Vec<String>) {
    let mut mode = ExecutionMode::Parallel;
    let mut rest = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--parallel" => mode = ExecutionMode::Parallel,
            "--sequential" => mode = ExecutionMode::Sequential,
            _ => rest.push(arg.clone()),
        }
    }
    (mode, rest)
}
