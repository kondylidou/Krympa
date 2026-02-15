// src/paths.rs
use std::path::{Path, PathBuf};
use std::fs;

#[derive(Clone, Debug)]
pub struct Paths {
    pub workdir: PathBuf,     // private per job
    pub lemmas: PathBuf,      // workdir/lemmas
    pub proofs: PathBuf,      // workdir/proofs
    pub tmp: PathBuf,         // workdir/tmp
    pub output: PathBuf,      // shared or per-job
}

impl Paths {
    pub fn new(workdir: impl AsRef<Path>, output: impl AsRef<Path>) -> Self {
        let workdir = workdir.as_ref().to_path_buf();
        Self {
            lemmas: workdir.join("lemmas"),
            proofs: workdir.join("proofs"),
            tmp: workdir.join("tmp"),
            workdir,
            output: output.as_ref().to_path_buf(),
        }
    }

    pub fn ensure_dirs(&self) -> std::io::Result<()> {
        fs::create_dir_all(&self.lemmas)?;
        fs::create_dir_all(&self.proofs)?;
        fs::create_dir_all(&self.tmp)?;
        fs::create_dir_all(&self.output)?;
        Ok(())
    }
}
