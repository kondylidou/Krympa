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

/// Commands that work on a proof file Krympa wrote, not on a problem.
pub const TOOLS: [&str; 2] = ["lean", "compress"];

/// What a whole run does after the search.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct WholeRun {
    /// `--direct`: prove only the lemmas the search can use
    pub direct: bool,
    /// `--compress`: remove avoidable steps from the proof
    pub compress: bool,
    /// `--lean`: check the proof in Lean
    pub lean: bool,
}

/// What the command line asks for, once the flags above have been stripped.
#[derive(Debug, PartialEq, Eq)]
pub enum Request {
    /// `krympa [--direct] [--compress] [--lean] <problem>`: every phase, from
    /// Vampire's proof to the shortened one.
    Whole { input: String, options: WholeRun },
    /// `krympa <phase> <problem>`: one phase, reading what the previous one wrote.
    Phase { phase: String, input: String },
    /// `krympa <lean|compress> <proof>`: work on a proof file.
    Tool { tool: String, proof: String },
}

/// Read the request from the arguments left after the other flags.
pub fn parse_request(args: &[String]) -> Result<Request, String> {
    const WHOLE_RUN_FLAGS: [&str; 3] = ["--direct", "--compress", "--lean"];
    let given = |flag: &str| args.iter().any(|arg| arg == flag);
    let options = WholeRun {
        direct: given("--direct"),
        compress: given("--compress"),
        lean: given("--lean"),
    };
    let rest: Vec<&str> = args
        .iter()
        .map(String::as_str)
        .filter(|arg| !WHOLE_RUN_FLAGS.contains(arg))
        .collect();
    if let Some(option) = rest.iter().find(|arg| arg.starts_with("--")) {
        return Err(format!("Unknown option '{}'", option));
    }
    let is_command = |name: &str| PHASES.contains(&name) || TOOLS.contains(&name);
    match rest.as_slice() {
        [input] if !is_command(input) => Ok(Request::Whole {
            input: input.to_string(),
            options,
        }),
        [command] => Err(format!("'{}' needs a file", command)),
        [command, _] if !is_command(command) => Err(format!("Unknown command '{}'", command)),
        [command, _] if options != WholeRun::default() => Err(format!(
            "--direct, --compress and --lean belong to a whole run and cannot be combined with '{}'",
            command
        )),
        [tool, proof] if TOOLS.contains(tool) => Ok(Request::Tool {
            tool: tool.to_string(),
            proof: proof.to_string(),
        }),
        [phase, input] => Ok(Request::Phase {
            phase: phase.to_string(),
            input: input.to_string(),
        }),
        _ => Err("Expected one problem file".to_string()),
    }
}
