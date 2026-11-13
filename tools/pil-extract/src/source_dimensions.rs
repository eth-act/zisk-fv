//! Physical AIR dimensions from compiled PIL metadata.
//!
//! The pinned compiler serializes the physical row count in `Air.num_rows`.
//! Missing metadata is an error: it must not acquire a default capacity.

use std::collections::BTreeSet;
use std::fmt::Write;

use anyhow::{bail, Context, Result};

use crate::pilout::PilOut;

/// Render all physical AIR dimensions without choosing a hand-maintained subset.
pub fn render(pilout: &PilOut) -> Result<String> {
    let mut out = String::from(
        "/-! Physical AIR dimensions extracted from `Air.numRows` in the pinned pilout.\n\
         `rowCount` is the physical capacity serialized by the pinned compiler.\n\
         These are compiler metadata, not the number of populated witness rows. -/\n\n\
         namespace Extraction.SourceDimensions\n\n",
    );
    let mut names = BTreeSet::new();
    for (group_index, group) in pilout.air_groups.iter().enumerate() {
        for (air_index, air) in group.airs.iter().enumerate() {
            let name = air.name.as_deref().context("AIR dimension has no name")?;
            if name.is_empty()
                || name.chars().any(|c| matches!(c, '\n' | '\r' | '«' | '»'))
            {
                bail!("AIR dimension name cannot be rendered as a Lean identifier: {name:?}");
            }
            if !names.insert(name) {
                bail!("duplicate AIR dimension name: {name}");
            }
            let rows = air
                .num_rows
                .with_context(|| format!("AIR {name} has no numRows metadata"))?;
            writeln!(out, "namespace «{name}»").unwrap();
            writeln!(out, "def airGroupIndex : Nat := {group_index}").unwrap();
            writeln!(out, "def airIndex : Nat := {air_index}").unwrap();
            writeln!(out, "def rowCount : Nat := {rows}").unwrap();
            writeln!(out, "end «{name}»\n").unwrap();
        }
    }
    if names.is_empty() {
        bail!("pilout has no AIR dimensions");
    }
    out.push_str("end Extraction.SourceDimensions\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pilout::{Air, AirGroup};

    fn dimensions(name: &str, rows: Option<u32>) -> PilOut {
        PilOut {
            air_groups: vec![AirGroup {
                airs: vec![Air {
                    name: Some(name.into()),
                    num_rows: rows,
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        }
    }

    #[test]
    fn preserves_actual_physical_row_count() {
        let lean = render(&dimensions("MemAlign", Some(2097152))).unwrap();
        assert!(lean.contains("namespace «MemAlign»\ndef airGroupIndex : Nat := 0\ndef airIndex : Nat := 0\ndef rowCount : Nat := 2097152"));
    }

    #[test]
    fn changing_compiled_dimension_changes_consumed_definition() {
        let original = render(&dimensions("MemAlign", Some(2097152))).unwrap();
        let mutated = render(&dimensions("MemAlign", Some(1048576))).unwrap();
        assert_ne!(original, mutated);
        assert!(mutated.contains("def rowCount : Nat := 1048576"));
    }

    #[test]
    fn zero_is_not_reinterpreted_as_a_one_row_exponent() {
        assert!(render(&dimensions("Empty", Some(0)))
            .unwrap()
            .contains("def rowCount : Nat := 0"));
    }

    #[test]
    fn missing_dimension_does_not_default_to_zero() {
        assert!(render(&dimensions("MemAlign", None))
            .unwrap_err()
            .to_string()
            .contains("no numRows metadata"));
    }

    #[test]
    fn missing_or_duplicate_air_names_are_rejected() {
        let mut pilout = dimensions("MemAlign", Some(2097152));
        let duplicate = pilout.air_groups[0].airs[0].clone();
        pilout.air_groups[0].airs.push(duplicate);
        assert!(render(&pilout).unwrap_err().to_string().contains("duplicate"));
        pilout.air_groups[0].airs.truncate(1);
        pilout.air_groups[0].airs[0].name = None;
        assert!(render(&pilout).is_err());
    }

    #[test]
    fn all_groups_and_air_indices_are_retained() {
        let mut pilout = dimensions("Main", Some(4194304));
        pilout.air_groups.push(AirGroup {
            airs: vec![Air {
                name: Some("MemAlign".into()),
                num_rows: Some(2097152),
                ..Default::default()
            }],
            ..Default::default()
        });
        let lean = render(&pilout).unwrap();
        assert!(lean.contains("namespace «Main»"));
        assert!(lean.contains("namespace «MemAlign»\ndef airGroupIndex : Nat := 1"));
    }

    #[test]
    fn empty_inventory_and_lean_delimiters_are_rejected() {
        assert!(render(&PilOut::default()).is_err());
        assert!(render(&dimensions("Mem»", Some(2097152))).is_err());
    }
}
