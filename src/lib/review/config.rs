//! `hemlis-review.json`.
//!
//! ```json
//! {
//!   "files": ["lib/**/*.purs"],
//!   "rules": {
//!     "unqualified-do": { "enabled": true },
//!     "missing-export-list": { "enabled": false }
//!   }
//! }
//! ```
//!
//! Rules not mentioned are enabled. Rule-specific options sit next to `enabled` and are read by
//! the rule itself. `files` is relative to the config file and is only used when the command line
//! names no files.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;

pub const DEFAULT_PATH: &str = "hemlis-review.json";
const DEFAULT_FILES: &[&str] = &["lib/**/*.purs"];

#[derive(Debug, Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    #[serde(default)]
    pub files: Vec<String>,
    #[serde(default)]
    pub rules: BTreeMap<String, RuleConfig>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct RuleConfig {
    #[serde(default = "default_true")]
    pub enabled: bool,
    #[serde(flatten)]
    pub options: serde_json::Map<String, serde_json::Value>,
}

fn default_true() -> bool {
    true
}

impl Config {
    pub fn enabled(&self, rule: &str) -> bool {
        self.rules.get(rule).map(|r| r.enabled).unwrap_or(true)
    }

    pub fn options(&self, rule: &str) -> Option<&serde_json::Map<String, serde_json::Value>> {
        self.rules.get(rule).map(|r| &r.options)
    }
}

/// Loads the config and returns it with the directory it lives in, which anchors `files`, the
/// baseline and relative paths. No explicit path and no `hemlis-review.json` in the current
/// directory means an empty config anchored at `.`.
pub fn load(explicit: Option<&str>) -> Result<(Config, PathBuf), String> {
    let path = PathBuf::from(explicit.unwrap_or(DEFAULT_PATH));
    if !path.exists() {
        if explicit.is_some() {
            return Err(format!("config file '{}' not found", path.display()));
        }
        return Ok((Config::default(), PathBuf::from(".")));
    }
    let text = fs::read_to_string(&path)
        .map_err(|e| format!("could not read config '{}': {}", path.display(), e))?;
    let cfg: Config = serde_json::from_str(&text)
        .map_err(|e| format!("invalid config '{}': {}", path.display(), e))?;
    let dir = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));
    Ok((cfg, dir))
}

/// The files to review when the command line names none: the config's `files` globs (or
/// `lib/**/*.purs`), relative to the config directory, sorted.
pub fn expand_files(cfg: &Config, dir: &Path) -> Result<Vec<String>, String> {
    let patterns: Vec<String> = if cfg.files.is_empty() {
        DEFAULT_FILES.iter().map(|s| s.to_string()).collect()
    } else {
        cfg.files.clone()
    };
    let mut out = Vec::new();
    for pattern in patterns {
        let full = dir.join(&pattern);
        let full = full.to_string_lossy();
        let paths = glob::glob(&full).map_err(|e| format!("bad glob '{}': {}", full, e))?;
        for entry in paths {
            let p = entry.map_err(|e| format!("glob '{}': {}", full, e))?;
            if p.is_file() {
                out.push(p.to_string_lossy().into_owned());
            }
        }
    }
    out.sort();
    out.dedup();
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_rules_are_enabled_and_options_flatten() {
        let cfg: Config = serde_json::from_str(
            r#"{ "rules": { "a": { "enabled": false }, "b": { "roots": ["x"] } } }"#,
        )
        .unwrap();
        assert!(!cfg.enabled("a"));
        assert!(cfg.enabled("b"));
        assert!(cfg.enabled("not-mentioned"));
        assert_eq!(cfg.options("b").unwrap()["roots"][0], "x");
    }

    #[test]
    fn unknown_top_level_keys_are_rejected() {
        assert!(serde_json::from_str::<Config>(r#"{ "rulez": {} }"#).is_err());
    }
}
