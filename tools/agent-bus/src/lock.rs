//! Cross-process mutation lock, held outside the committed tree
//! (AGENT_BUS.md section 8: "Mutation commands acquire an operating-system
//! lock outside the committed tree").

use crate::error::{AbError, AbResult};
use fs4::FileExt;
use std::fs::{File, OpenOptions};
use std::path::{Path, PathBuf};

pub struct BusLock {
    _file: File,
    path: PathBuf,
}

impl BusLock {
    /// Acquire an exclusive advisory lock at `<repo_git_dir>/agent-bus.lock`.
    /// This lives under `.git/`, which is never part of any committed tree.
    pub fn acquire(git_dir: &Path) -> AbResult<BusLock> {
        std::fs::create_dir_all(git_dir).map_err(|e| AbError::Io {
            path: git_dir.display().to_string(),
            source: e,
        })?;
        let path = git_dir.join("agent-bus.lock");
        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(false)
            .open(&path)
            .map_err(|e| AbError::Io {
                path: path.display().to_string(),
                source: e,
            })?;
        FileExt::lock_exclusive(&file)
            .map_err(|e| AbError::Git(format!("failed to lock {}: {e}", path.display())))?;
        Ok(BusLock { _file: file, path })
    }
}

impl Drop for BusLock {
    fn drop(&mut self) {
        let _ = FileExt::unlock(&self._file);
        let _ = &self.path;
    }
}
