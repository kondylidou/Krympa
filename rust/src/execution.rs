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
static REFINE: OnceLock<bool> = OnceLock::new();
static VAMPIRE_EXECUTABLE: OnceLock<Option<String>> = OnceLock::new();
static TWEE_EXECUTABLE: OnceLock<Option<String>> = OnceLock::new();

pub fn execution_mode() -> ExecutionMode {
    *EXECUTION_MODE.get_or_init(|| ExecutionMode::Parallel)
}

pub fn term_size_aware() -> bool {
    *TERM_SIZE_AWARE.get_or_init(|| false)
}

/// Whether the final refinement was asked for with `--refine`.
pub fn refine_requested() -> bool {
    *REFINE.get_or_init(|| false)
}

/// The Vampire executable given with `--vampire`, if any.
pub fn vampire_executable() -> Option<String> {
    VAMPIRE_EXECUTABLE.get().cloned().flatten()
}

/// The Twee executable given with `--twee`, if any.
pub fn twee_executable() -> Option<String> {
    TWEE_EXECUTABLE.get().cloned().flatten()
}

/// The flags of the command line.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Flags {
    /// `--sequential`: one prover call at a time (`--parallel` is the default)
    pub sequential: bool,
    /// `--term-size`: prefer proofs with smaller terms
    pub term_size: bool,
    /// `--refine`: run the final refinement on the best proof
    pub refine: bool,
    /// `--debug`: full trace
    pub debug: bool,
    /// `--vampire <exe>`, `--twee <exe>`
    pub vampire: Option<String>,
    pub twee: Option<String>,
}

/// Strip the flags from the arguments; return them and what is left.
pub fn parse_flags(args: &[String]) -> (Flags, Vec<String>) {
    let (mut flags, mut rest) = (Flags::default(), Vec::new());
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--parallel" => flags.sequential = false,
            "--sequential" => flags.sequential = true,
            "--term-size" => flags.term_size = true,
            "--refine" => flags.refine = true,
            "--debug" => flags.debug = true,
            "--vampire" => flags.vampire = args.next().cloned(),
            "--twee" => flags.twee = args.next().cloned(),
            _ => rest.push(arg.clone()),
        }
    }
    (flags, rest)
}

/// Make the flags known to the rest of the program. Call once, at the start.
pub fn apply_flags(flags: Flags) {
    let _ = EXECUTION_MODE.set(if flags.sequential {
        ExecutionMode::Sequential
    } else {
        ExecutionMode::Parallel
    });
    let _ = TERM_SIZE_AWARE.set(flags.term_size);
    let _ = REFINE.set(flags.refine);
    let _ = VAMPIRE_EXECUTABLE.set(flags.vampire);
    let _ = TWEE_EXECUTABLE.set(flags.twee);
    if flags.debug {
        crate::logging::set_level(crate::logging::Level::Debug);
    }
}

/// The phases that can be run on their own, in the order of a whole run.
pub const PHASES: [&str; 6] = [
    "run_vampire",
    "collect",
    "shorten",
    "minimize",
    "direct",
    "group",
];

/// What the command line asks for, once the flags above have been stripped.
#[derive(Debug, PartialEq, Eq)]
pub enum Request {
    /// `krympa [--direct] [--lean] <problem>`: every phase, from Vampire's proof
    /// to the shortened one. With `direct`, only the lemmas the search needs
    /// are proved; with `lean`, the result is checked in Lean.
    Whole {
        input: String,
        direct: bool,
        lean: bool,
    },
    /// `krympa <phase> <problem>`: one phase, reading what the previous one wrote.
    Phase { phase: String, input: String },
}

/// Read the request from the arguments left after the other flags.
pub fn parse_request(args: &[String]) -> Result<Request, String> {
    const WHOLE_RUN_FLAGS: [&str; 2] = ["--direct", "--lean"];
    let given = |flag: &str| args.iter().any(|arg| arg == flag);
    let (direct, lean) = (given("--direct"), given("--lean"));
    let rest: Vec<&str> = args
        .iter()
        .map(String::as_str)
        .filter(|arg| !WHOLE_RUN_FLAGS.contains(arg))
        .collect();
    if let Some(option) = rest.iter().find(|arg| arg.starts_with("--")) {
        return Err(format!("Unknown option '{}'", option));
    }
    match rest.as_slice() {
        [input] if !PHASES.contains(input) => Ok(Request::Whole {
            input: input.to_string(),
            direct,
            lean,
        }),
        [phase] => Err(format!("'{}' needs a problem file", phase)),
        [phase, _] if !PHASES.contains(phase) => Err(format!("Unknown command '{}'", phase)),
        [phase, _] if direct || lean => Err(format!(
            "--direct and --lean belong to a whole run and cannot be combined with '{}'",
            phase
        )),
        [phase, input] => Ok(Request::Phase {
            phase: phase.to_string(),
            input: input.to_string(),
        }),
        _ => Err("Expected one problem file".to_string()),
    }
}
