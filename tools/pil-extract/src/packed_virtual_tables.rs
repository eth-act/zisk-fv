//! Compressed provenance for target projections of the actual production
//! VirtualTable0/1 fixed columns. The JSON is emitted by the compiler observer,
//! which checks every target cell and its converse ownership before writing it.
//! No row-building/packing algorithm or external fixed-value oracle is emitted.

use anyhow::{bail, ensure, Context, Result};
use serde_json::Value;
use std::collections::BTreeSet;
use std::fmt::Write;

const ROWS: u64 = 1 << 21;
const TARGETS: [(u64, u64, u64); 5] = [
    (88, 65536, 2),
    (124, 3151872, 7),
    (125, 5505024, 7),
    (330, 4194304, 2),
    (331, 128, 4),
];

fn natural(value: &Value, key: &str) -> Result<u64> {
    value.get(key).and_then(Value::as_u64).with_context(|| format!("missing/non-natural {key}"))
}

struct Source {
    table: u64,
    bus: u64,
    width: u64,
    rows: u64,
    air: u64,
    start: u64,
}

pub fn render(source_json: &str) -> Result<String> {
    let json: Value = serde_json::from_str(source_json).context("invalid packed source JSON")?;
    ensure!(natural(&json, "version")? == 1, "unsupported packed source version");
    let airs = json.get("airs").and_then(Value::as_array).context("missing packed AIRs")?;
    ensure!(airs.len() == 2, "expected both physical packed AIRs");
    let mut air_ids = BTreeSet::new();
    for air in airs {
        let id = natural(air, "air")?;
        ensure!(id < 2 && air_ids.insert(id), "unknown/duplicate packed AIR");
        ensure!(natural(air, "rows")? == ROWS && natural(air, "rawWidth")? == 8,
            "physical packed row/multiplicity schema changed");
        let widths = air.get("widths").and_then(Value::as_array).context("missing packed widths")?;
        ensure!(widths.len() == 8 && widths.iter().all(|width| width.as_u64().is_some_and(|n| n > 0 && n <= 64)),
            "unknown packed fixed schema");
        let total: u64 = widths.iter().map(|width| width.as_u64().unwrap()).sum();
        ensure!(total == if id == 0 { 43 } else { 64 }, "packed fixed-column count changed");
    }
    let inputs = json.get("sources").and_then(Value::as_array).context("missing packed sources")?;
    ensure!(inputs.len() == TARGETS.len(), "target table/UID source set changed");
    let mut sources = Vec::with_capacity(inputs.len());
    let mut tables = BTreeSet::new();
    let mut buses = BTreeSet::new();
    for input in inputs {
        let source = Source {
            table: natural(input, "tableId")?, bus: natural(input, "busId")?,
            width: natural(input, "width")?, rows: natural(input, "rows")?,
            air: natural(input, "air")?, start: natural(input, "start")?,
        };
        let (_, rows, width) = TARGETS.iter().find(|(bus, _, _)| *bus == source.bus)
            .context("unknown target bus")?;
        ensure!(source.rows == *rows && source.width == *width && source.air < 2,
            "target source domain/schema changed");
        ensure!(tables.insert(source.table) && buses.insert(source.bus), "duplicate source table/target UID");
        ensure!(source.start.checked_add(source.rows).is_some_and(|end| end <= 8 * ROWS),
            "source interval exceeds the physical multiplicity domain");
        let digest = input.get("sha256").and_then(Value::as_str).context("missing source digest")?;
        ensure!(digest.len() == 64 && digest.bytes().all(|c| c.is_ascii_hexdigit()), "invalid source digest");
        sources.push(source);
    }
    sources.sort_by_key(|source| source.bus);
    for (i, left) in sources.iter().enumerate() {
        for right in &sources[i + 1..] {
            ensure!(left.air != right.air || left.start + left.rows <= right.start ||
                right.start + right.rows <= left.start, "target source multiplicity cells collide");
        }
    }
    if buses.len() != TARGETS.len() { bail!("incomplete target source set"); }
    let mut out = String::from("import Mathlib\n\nnamespace Extraction.PackedVirtualTables\n\n");
    out.push_str("/- Production compiler observations, not a reimplementation of pack_tables.\n\
        Only buses 88/124/125/330/331 are projected; no unrelated fixed value is invented. -/\n");
    out.push_str("def physicalRows : Nat := 2097152\n\n\
        structure Location where\n  air : Fin 2\n  lane : Fin 8\n  row : Fin physicalRows\n\
        deriving DecidableEq\n\n\
        def Location.offset (location : Location) : Nat :=\n  location.lane.val * physicalRows + location.row.val\n\n\
        structure Source where\n  tableId : Nat\n  busId : Nat\n  width : Nat\n  rows : Nat\n  air : Fin 2\n  start : Nat\n  domain : start + rows ≤ 8 * physicalRows\n\n\
        def Source.location (source : Source) (index : Fin source.rows) : Location :=\n\
          { air := source.air\n\
            lane := ⟨(source.start + index.val) / physicalRows, by\n\
              have h := source.domain\n\
              have hi := index.isLt\n\
              dsimp [physicalRows] at *\n\
              omega⟩\n\
            row := ⟨(source.start + index.val) % physicalRows, Nat.mod_lt _ (by decide)⟩ }\n\n\
        theorem location_offset (source : Source) (index : Fin source.rows) :\n\
            (source.location index).offset = source.start + index.val := by\n\
          simp only [Source.location, Location.offset]\n\
          omega\n\n\
        theorem location_injective (source : Source) : Function.Injective source.location := by\n\
          intro i j h\n\
          have he := congrArg Location.offset h\n\
          rw [location_offset, location_offset] at he\n\
          apply Fin.ext\n\
          omega\n\n");
    out.push_str("theorem Location.eq_of_air_offset {left right : Location}\n\
          (hair : left.air = right.air) (hoffset : left.offset = right.offset) : left = right := by\n\
          have hl := left.row.isLt\n\
          have hr := right.row.isLt\n\
          have hlane : left.lane.val = right.lane.val := by\n\
            simp only [Location.offset, physicalRows] at hoffset\n\
            simp only [physicalRows] at hl hr\n\
            omega\n\
          have hrow : left.row.val = right.row.val := by\n\
            simp only [Location.offset] at hoffset\n\
            omega\n\
          cases left\n\
          cases right\n\
          simp_all only [Location.mk.injEq, Fin.ext_iff, and_self]\n\n");
    for source in &sources {
        writeln!(out, "def source{} : Source :=", source.bus)?;
        writeln!(out, "  {{ tableId := {}, busId := {}, width := {}, rows := {},", source.table, source.bus, source.width, source.rows)?;
        writeln!(out, "    air := {}, start := {}, domain := by decide }}\n", source.air, source.start)?;
    }
    out.push_str("def sourceAt (location : Location) : Option (Nat × Nat) :=\n");
    for source in &sources {
        writeln!(out, "  if location.air.val = {} ∧ {} ≤ location.offset ∧ location.offset < {} then", source.air, source.start, source.start + source.rows)?;
        writeln!(out, "    some ({}, location.offset - {}) else", source.table, source.start)?;
    }
    out.push_str("    none\n\n");
    for source in &sources {
        writeln!(out, "theorem source{}_at (index : Fin source{}.rows) :", source.bus, source.bus)?;
        writeln!(out, "    sourceAt (source{}.location index) = some ({}, index.val) := by", source.bus, source.table)?;
        writeln!(out, "  have hi := index.isLt\n  simp only [source{}] at hi", source.bus)?;
        // Simplifying the observed interval chain leaves only linear arithmetic.
        writeln!(out, "  simp only [sourceAt, location_offset, Source.location, source{}]", source.bus)?;
        out.push_str("  split_ifs <;> simp_all only [Option.some.injEq, Prod.mk.injEq] <;> omega\n\n");
        writeln!(out, "theorem source{}_of_at (location : Location) (index : Nat)", source.bus)?;
        writeln!(out, "    (h : sourceAt location = some (source{}.tableId, index)) :", source.bus)?;
        writeln!(out, "    ∃ sourceIndex : Fin source{}.rows, sourceIndex.val = index ∧", source.bus)?;
        writeln!(out, "      source{}.location sourceIndex = location := by", source.bus)?;
        writeln!(out, "  have hf : index < source{}.rows ∧ location.air = source{}.air ∧", source.bus, source.bus)?;
        writeln!(out, "      location.offset = source{}.start + index := by", source.bus)?;
        writeln!(out, "    simp only [sourceAt, source{}] at h ⊢", source.bus)?;
        out.push_str("    split_ifs at h <;> simp_all only [Option.some.injEq, Prod.mk.injEq]\n\
            all_goals first | omega | (refine ⟨by omega, Fin.ext (by omega), by omega⟩)\n");
        out.push_str("  obtain ⟨hi, hair, hoffset⟩ := hf\n\
          refine ⟨⟨index, hi⟩, rfl, ?_⟩\n\
          apply Location.eq_of_air_offset\n\
          · exact hair.symm\n\
          · rw [location_offset]\n\
            exact hoffset.symm\n\n");
        writeln!(out, "def source{}Locations : List Location := List.ofFn source{}.location\n", source.bus, source.bus)?;
        writeln!(out, "theorem source{}Locations_nodup : source{}Locations.Nodup :=", source.bus, source.bus)?;
        writeln!(out, "  List.nodup_ofFn_ofInjective (location_injective source{})\n", source.bus)?;
        writeln!(out, "theorem source{}Locations_complete (location : Location) :", source.bus)?;
        writeln!(out, "    location ∈ source{}Locations ↔", source.bus)?;
        writeln!(out, "      ∃ index, sourceAt location = some (source{}.tableId, index) := by", source.bus)?;
        out.push_str("  constructor\n\
          · intro h\n\
            obtain ⟨index, rfl⟩ := List.mem_ofFn.mp h\n");
        writeln!(out, "    exact ⟨index.val, source{}_at index⟩", source.bus)?;
        out.push_str("  · rintro ⟨index, h⟩\n");
        writeln!(out, "    obtain ⟨sourceIndex, _, he⟩ := source{}_of_at location index h", source.bus)?;
        out.push_str("    exact List.mem_ofFn.mpr ⟨sourceIndex, he⟩\n\n");
    }
    out.push_str("end Extraction.PackedVirtualTables\n");
    Ok(out)
}
