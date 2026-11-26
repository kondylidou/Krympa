use std::env;
use std::path::{Path, PathBuf};
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
#[derive(Debug, PartialEq, Eq)]
pub struct WholeRun {
    /// `--direct`: prove only the lemmas the search can use
    pub direct: bool,
    /// remove avoidable steps from the proof; `--no-compress` turns it off
    pub compress: bool,
    /// `--lean`: check the proof in Lean
    pub lean: bool,
    /// `--vampire-proof <file>`: start from this saved Vampire proof instead
    /// of running Vampire
    pub vampire_proof: Option<String>,
}

impl Default for WholeRun {
    fn default() -> Self {
        WholeRun {
            direct: false,
            compress: true,
            lean: false,
            vampire_proof: None,
        }
    }
}

/// What the command line asks for, once the flags above have been stripped.
#[derive(Debug, PartialEq, Eq)]
pub enum Request {
    /// `krympa [--direct] [--no-compress] [--lean] [--vampire-proof <file>] <problem>`:
    /// every phase, from Vampire's proof to the shortened one.
    Whole { input: String, options: WholeRun },
    /// `krympa <phase> <problem>`: one phase, reading what the previous one wrote.
    Phase { phase: String, input: String },
    /// `krympa <lean|compress> <proof>`: work on a proof file.
    Tool { tool: String, proof: String },
}

/// Read the request from the arguments left after the other flags.
pub fn parse_request(args: &[String]) -> Result<Request, String> {
    let mut options = WholeRun::default();
    let mut rest: Vec<&str> = Vec::new();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--direct" => options.direct = true,
            "--no-compress" => options.compress = false,
            "--lean" => options.lean = true,
            "--vampire-proof" => {
                let file = args
                    .next()
                    .ok_or_else(|| "--vampire-proof needs a file".to_string())?;
                options.vampire_proof = Some(file.clone());
            }
            other => rest.push(other),
        }
    }
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
            "--direct, --no-compress, --lean and --vampire-proof belong to a whole run and cannot be combined with '{}'",
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

// ---------------------------------------------------------------------------
// Where Krympa works
// ---------------------------------------------------------------------------

/// The folder Krympa was started from.
static LAUNCH_DIR: OnceLock<PathBuf> = OnceLock::new();

/// The Krympa folder: the nearest folder above the executable that holds the
/// lemma extractor `ocaml_install/tptp_parser`, or else the current folder.
/// Krympa works in it: `output/`, `lemmas/`, `proofs/` and `tmp/` are there,
/// and so are `bin/` and `lean/`.
pub fn krympa_home() -> PathBuf {
    let extractor = Path::new("ocaml_install").join("tptp_parser");
    env::current_exe()
        .and_then(|exe| exe.canonicalize())
        .ok()
        .and_then(|exe| {
            exe.ancestors()
                .skip(1)
                .find(|dir| dir.join(&extractor).exists())
                .map(Path::to_path_buf)
        })
        .unwrap_or_else(|| env::current_dir().unwrap_or_default())
}

/// Change into the Krympa folder, so that Krympa can be started from anywhere.
/// Paths given by the user are then resolved with `absolute`.
pub fn enter_krympa_home() -> Result<PathBuf, String> {
    let launched = env::current_dir().map_err(|e| format!("No current folder: {}", e))?;
    let _ = LAUNCH_DIR.set(launched);
    let home = krympa_home();
    env::set_current_dir(&home)
        .map_err(|e| format!("Cannot change into {}: {}", home.display(), e))?;
    Ok(home)
}

/// A path the user gave, resolved against the folder Krympa was started from.
pub fn absolute(path: &str) -> String {
    let given = Path::new(path);
    if given.is_absolute() {
        return path.to_string();
    }
    let launched = LAUNCH_DIR
        .get()
        .cloned()
        .unwrap_or_else(|| env::current_dir().unwrap_or_default());
    let joined = launched.join(given);
    joined
        .canonicalize()
        .unwrap_or(joined)
        .to_string_lossy()
        .into_owned()
}
