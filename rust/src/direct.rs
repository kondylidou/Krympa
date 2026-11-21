//! The pipeline without proving every lemma first.
//!
//! `collect` proves each lemma of the Vampire proof in three variants with two
//! provers, although `minimize` only ever looks at the lemmas it can reach
//! from its arrival candidates. `direct` proves exactly those:
//!
//!   1. the arrival candidates of `minimize`: the last lemmas of the proof;
//!   2. the lemmas their proofs use, then the lemmas those use, and so on.
//!
//! A lemma that is proved gets the same treatment as in `collect` (all three
//! variants, both provers, shortest proof kept), and "uses" means what it
//! means in `minimize`: the lemmas cited by the Twee proof of the kept
//! variant. `shorten` and `minimize` then run unchanged on the result, so the
//! segmentation and every choice in it are the ones of the full pipeline.

use crate::collect::{extract_lemma_files, save_summary, shorten_proofs};
use crate::minimize::{try_minimize, MAX_ARRIVAL_CANDIDATES};
use crate::provers::{prove_lemmas_into, reset_proof_dir};
use crate::regex_cache::cached_regex;
use crate::utils::load_lemma;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::Path;

const LEMMAS_DIR: &str = "../lemmas";
const PROOFS_DIR: &str = "../proofs";

/// Run the pipeline on the lemmas that `minimize` can reach.
pub fn try_direct(
    input_file: &str,
    vampire_file: &str,
    summary_file: &str,
    suffix: &str,
) -> Result<String, String> {
    let started = std::time::Instant::now();
    crate::klog_info!("[INFO] Phase 1: Collection of the lemmas the search can use");
    let mut lemmas = Lemmas::extract(vampire_file);
    lemmas.prove_arrival_candidates()?;
    lemmas.prove_reachable();
    save_summary(&lemmas.proved, suffix);

    // `shorten` proves some lemmas again from abstracted statements. Such a
    // proof may use a lemma that was not needed before, so close up again.
    loop {
        shorten_proofs(summary_file);
        if lemmas.prove_reachable() == 0 {
            break;
        }
        save_summary(&lemmas.proved, suffix);
    }

    crate::klog_info!(
        "[INFO] Proved {} of {} lemmas ({} prover runs instead of {}) in {:.0} s",
        lemmas.attempted.len(),
        lemmas.files.len(),
        6 * lemmas.attempted.len(),
        6 * lemmas.files.len(),
        started.elapsed().as_secs_f64()
    );
    try_minimize(input_file, vampire_file, summary_file)
}

/// The lemmas of a Vampire proof and what has been proved of them so far.
struct Lemmas {
    /// lemma number -> its problem files (big-step, small-step, abstracted)
    files: BTreeMap<u32, Vec<String>>,
    /// lemma number -> (kept variant, prover, proof), as in `summary.json`
    proved: HashMap<u32, (String, String, String)>,
    attempted: BTreeSet<u32>,
}

impl Lemmas {
    fn extract(vampire_file: &str) -> Self {
        let mut files: BTreeMap<u32, Vec<String>> = BTreeMap::new();
        for file in extract_lemma_files(vampire_file) {
            if let Some(number) = lemma_number(&file) {
                files.entry(number).or_default().push(file);
            }
        }
        reset_proof_dir(PROOFS_DIR);
        Lemmas {
            files,
            proved: HashMap::new(),
            attempted: BTreeSet::new(),
        }
    }

    /// Prove the given lemmas in all variants; returns the ones that were proved.
    fn prove(&mut self, numbers: &BTreeSet<u32>) -> BTreeSet<u32> {
        let files: Vec<String> = numbers
            .iter()
            .filter_map(|n| self.files.get(n))
            .flatten()
            .cloned()
            .collect();
        self.attempted.extend(numbers);
        let results = prove_lemmas_into(&files, &["vampire", "twee"], PROOFS_DIR);
        let proved = results.keys().copied().collect();
        self.proved.extend(results);
        proved
    }

    /// The arrival candidates of `minimize`: going back from the end of the
    /// proof, the first lemmas that have no Skolem constant and can be proved.
    fn prove_arrival_candidates(&mut self) -> Result<(), String> {
        let skolem = cached_regex(r"\bsK\d+\b");
        let mut candidates = Vec::new();
        for number in self.files.keys().rev() {
            let statement = load_lemma(LEMMAS_DIR, &format!("big_step_lemma_{:04}", number))?;
            if !skolem.is_match(&statement) {
                candidates.push(*number);
            }
        }
        let mut found = 0;
        let mut next = candidates.into_iter();
        while found < MAX_ARRIVAL_CANDIDATES {
            let batch: BTreeSet<u32> = next.by_ref().take(MAX_ARRIVAL_CANDIDATES - found).collect();
            if batch.is_empty() {
                break;
            }
            found += self.prove(&batch).len();
        }
        Ok(())
    }

    /// Prove every lemma that a proved lemma uses, until nothing new turns up.
    /// Returns how many lemmas were attempted.
    fn prove_reachable(&mut self) -> usize {
        let mut attempted = 0;
        loop {
            let wanted: BTreeSet<u32> = self
                .proved
                .iter()
                .flat_map(|(number, (variant, _, _))| used_lemmas(*number, variant))
                .filter(|n| self.files.contains_key(n) && !self.attempted.contains(n))
                .collect();
            if wanted.is_empty() {
                return attempted;
            }
            attempted += wanted.len();
            self.prove(&wanted);
        }
    }
}

/// The lemmas that the kept proof of a lemma uses, read the way `minimize`
/// reads them: from the Twee proof of the kept variant, if there is one.
fn used_lemmas(number: u32, variant: &str) -> BTreeSet<u32> {
    let twee_proof = Path::new(PROOFS_DIR)
        .join("twee_tmp")
        .join(format!("{}_twee.proof", variant));
    let mut used = fs::read_to_string(twee_proof)
        .map(|proof| cited_lemmas(&proof))
        .unwrap_or_default();
    used.remove(&number);
    used
}

/// Numbers of the lemmas a Twee proof cites as axioms or goals.
pub fn cited_lemmas(twee_proof: &str) -> BTreeSet<u32> {
    cached_regex(r"(?m)^\s*(?:Axiom|Goal)\s+\d+\s+\(lemma_(\d+)\)")
        .captures_iter(twee_proof)
        .filter_map(|caps| caps[1].parse().ok())
        .collect()
}

/// `../lemmas/small-step/small_step_lemma_0021.p` -> 21
fn lemma_number(file: &str) -> Option<u32> {
    let stem = Path::new(file).file_stem()?.to_str()?;
    stem.rsplit('_').next()?.parse().ok()
}
