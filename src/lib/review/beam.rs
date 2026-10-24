//! Cross-module call edges from the compiled BEAM, produced by xref (see the pay-backend
//! `fab beam-edges`). One `caller callee function` triple per line, module atoms as purerl names
//! them (`accessRight_storage@ps`). A call into a `@ps` module from any other module, Elixir or
//! Erlang included, counts as a use of that export.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

pub struct BeamEdges {
    /// (PureScript module name, function name) pairs that some other module calls.
    used: BTreeSet<(String, String)>,
}

impl BeamEdges {
    pub fn load(path: &Path) -> Result<Self, String> {
        // Module names may carry non-UTF-8 bytes from Elixir atoms; lossy is fine, we only
        // match `@ps` modules.
        let bytes = fs::read(path)
            .map_err(|e| format!("could not read BEAM edges '{}': {}", path.display(), e))?;
        let text = String::from_utf8_lossy(&bytes);
        let mut used = BTreeSet::new();
        for line in text.lines() {
            let mut parts = line.split_whitespace();
            let (Some(caller), Some(callee), Some(fun)) = (parts.next(), parts.next(), parts.next())
            else {
                continue;
            };
            if caller == callee {
                continue;
            }
            if let Some(module) = callee.strip_suffix("@ps") {
                used.insert((ps_module_name(module), fun.to_string()));
            }
        }
        Ok(Self { used })
    }

    pub fn is_used(&self, module: &str, name: &str) -> bool {
        self.used.contains(&(module.to_string(), name.to_string()))
    }

    pub fn len(&self) -> usize {
        self.used.len()
    }

    pub fn is_empty(&self) -> bool {
        self.used.is_empty()
    }
}

/// `accessRight_storage` -> `AccessRight.Storage`. purerl lowers the first letter of every
/// module segment and joins them with `_`.
pub fn ps_module_name(beam: &str) -> String {
    beam.split('_')
        .map(|seg| {
            let mut chars = seg.chars();
            match chars.next() {
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect::<Vec<_>>()
        .join(".")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_names_round_trip_purerl_casing() {
        assert_eq!(ps_module_name("accessRight_storage"), "AccessRight.Storage");
        assert_eq!(ps_module_name("cM1_flow"), "CM1.Flow");
        assert_eq!(ps_module_name("accountec"), "Accountec");
    }
}
