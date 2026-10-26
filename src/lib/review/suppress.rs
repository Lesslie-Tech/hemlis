//! The suppression baseline: `review/suppressed/<rule>.json` next to the config, one entry per
//! file with the number of findings it is allowed to have. A file whose count grows loses its
//! suppression for that rule entirely; `--update-baseline` rewrites the counts from the current
//! findings. Same design as elm-review's `review/suppressed/`.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct BaselineFile {
    version: u32,
    rule: String,
    suppressions: Vec<Entry>,
}

#[derive(Serialize, Deserialize)]
struct Entry {
    count: usize,
    file: String,
}

#[derive(Debug, Default)]
pub struct Baseline {
    /// rule -> file -> allowed count
    counts: BTreeMap<String, BTreeMap<String, usize>>,
}

pub struct Applied {
    /// One flag per input key: true when the finding is reported, false when suppressed.
    pub reported: Vec<bool>,
    pub suppressed: usize,
    /// Baseline entries that allow more findings than currently exist.
    pub stale: usize,
}

pub fn baseline_dir(config_dir: &Path) -> PathBuf {
    config_dir.join("review").join("suppressed")
}

impl Baseline {
    /// A missing directory is an empty baseline; an unreadable or malformed file is an error.
    pub fn load(dir: &Path) -> Result<Self, String> {
        let mut counts: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
        if !dir.exists() {
            return Ok(Self { counts });
        }
        let entries = fs::read_dir(dir).map_err(|e| format!("could not read '{}': {}", dir.display(), e))?;
        for entry in entries {
            let path = entry.map_err(|e| format!("could not read '{}': {}", dir.display(), e))?.path();
            if path.extension().and_then(|e| e.to_str()) != Some("json") {
                continue;
            }
            let text = fs::read_to_string(&path)
                .map_err(|e| format!("could not read baseline '{}': {}", path.display(), e))?;
            let file: BaselineFile = serde_json::from_str(&text)
                .map_err(|e| format!("invalid baseline '{}': {}", path.display(), e))?;
            let per_file = counts.entry(file.rule).or_default();
            for s in file.suppressions {
                *per_file.entry(s.file).or_default() += s.count;
            }
        }
        Ok(Self { counts })
    }

    pub fn apply(&self, keys: &[(&str, &str)]) -> Applied {
        let mut current: BTreeMap<(&str, &str), usize> = BTreeMap::new();
        for k in keys {
            *current.entry(*k).or_default() += 1;
        }
        let allowed = |rule: &str, file: &str| {
            self.counts.get(rule).and_then(|m| m.get(file)).copied().unwrap_or(0)
        };

        let mut reported = Vec::with_capacity(keys.len());
        let mut suppressed = 0;
        for k in keys {
            let suppress = current[k] <= allowed(k.0, k.1);
            reported.push(!suppress);
            if suppress {
                suppressed += 1;
            }
        }

        let mut stale = 0;
        for (rule, files) in self.counts.iter() {
            for (file, &count) in files.iter() {
                let now = current.get(&(rule.as_str(), file.as_str())).copied().unwrap_or(0);
                if now < count {
                    stale += 1;
                }
            }
        }
        Applied { reported, suppressed, stale }
    }
}

/// Rewrites the baseline directory from `keys`: one `<rule>.json` per rule with findings, and no
/// file for rules without. Returns the number of files written.
pub fn write(dir: &Path, keys: &[(&str, &str)]) -> Result<usize, String> {
    let mut counts: BTreeMap<&str, BTreeMap<&str, usize>> = BTreeMap::new();
    for (rule, file) in keys {
        *counts.entry(rule).or_default().entry(file).or_default() += 1;
    }

    fs::create_dir_all(dir).map_err(|e| format!("could not create '{}': {}", dir.display(), e))?;
    for entry in fs::read_dir(dir).map_err(|e| format!("could not read '{}': {}", dir.display(), e))? {
        let path = entry.map_err(|e| format!("could not read '{}': {}", dir.display(), e))?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("json") {
            fs::remove_file(&path).map_err(|e| format!("could not remove '{}': {}", path.display(), e))?;
        }
    }

    for (rule, files) in counts.iter() {
        let file = BaselineFile {
            version: 1,
            rule: rule.to_string(),
            suppressions: files
                .iter()
                .map(|(file, &count)| Entry { count, file: file.to_string() })
                .collect(),
        };
        let path = dir.join(format!("{}.json", rule));
        let text = serde_json::to_string_pretty(&file).expect("baseline is serialisable");
        fs::write(&path, text + "\n").map_err(|e| format!("could not write '{}': {}", path.display(), e))?;
    }
    Ok(counts.len())
}

/// `path` relative to `base` when both resolve on disk and `path` is inside `base`; otherwise
/// `path` unchanged. Always forward slashes.
pub fn relative_path(path: &str, base: &Path) -> String {
    match (fs::canonicalize(path), fs::canonicalize(base)) {
        (Ok(p), Ok(b)) => match p.strip_prefix(&b) {
            Ok(rel) => rel.to_string_lossy().replace('\\', "/"),
            Err(_) => path.to_string(),
        },
        _ => path.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn baseline(entries: &[(&str, &str, usize)]) -> Baseline {
        let mut counts: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
        for (rule, file, count) in entries {
            counts.entry(rule.to_string()).or_default().insert(file.to_string(), *count);
        }
        Baseline { counts }
    }

    #[test]
    fn same_count_is_suppressed_and_growth_unsuppresses_the_whole_file() {
        let b = baseline(&[("r", "a.purs", 2)]);
        let same = b.apply(&[("r", "a.purs"), ("r", "a.purs")]);
        assert_eq!(same.reported, vec![false, false]);
        assert_eq!(same.suppressed, 2);
        assert_eq!(same.stale, 0);

        let grown = b.apply(&[("r", "a.purs"), ("r", "a.purs"), ("r", "a.purs")]);
        assert_eq!(grown.reported, vec![true, true, true]);
        assert_eq!(grown.suppressed, 0);
    }

    #[test]
    fn fewer_findings_than_allowed_is_stale() {
        let b = baseline(&[("r", "a.purs", 2), ("r", "gone.purs", 1)]);
        let a = b.apply(&[("r", "a.purs")]);
        assert_eq!(a.reported, vec![false]);
        assert_eq!(a.stale, 2);
    }

    #[test]
    fn other_rules_and_files_are_not_covered() {
        let b = baseline(&[("r", "a.purs", 5)]);
        let a = b.apply(&[("other", "a.purs"), ("r", "b.purs")]);
        assert_eq!(a.reported, vec![true, true]);
    }
}
