//! Extract the fixed 256-row MemAlign ROM from its upstream PIL definition.
//!
//! `MemAlignRom` is virtual, so it is intentionally absent from pilout's AIR
//! list. Its rows are observed from the pinned PIL compiler after it executes
//! the upstream fixed-column builder in `mem_align_rom.pil`. No builder logic
//! is reimplemented here. The Rust state-machine source supplies the separately
//! checked physical table parameters (id, size, and padding-row index).

use std::fmt::Write;
use std::path::Path;

use anyhow::{ensure, Context, Result};
use regex::Regex;

const EXPECTED_TABLE_ID: usize = 133;
const EXPECTED_TABLE_SIZE: usize = 256;
const EXPECTED_PADDING_ROW: usize = 0;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Row {
    pc: i64,
    delta_pc: i64,
    delta_addr: i64,
    offset: i64,
    width: i64,
    flags: i64,
}

/// Parse the upstream PIL fixed columns and emit `Extraction.MemAlignRom`.
pub fn run(
    pil_source: &Path,
    rust_source: &Path,
    compiled_rows: &Path,
    output: Option<&Path>,
) -> Result<String> {
    let pil = std::fs::read_to_string(pil_source)
        .with_context(|| format!("failed to read {}", pil_source.display()))?;
    let rust = std::fs::read_to_string(rust_source)
        .with_context(|| format!("failed to read {}", rust_source.display()))?;

    let table_id = rust_const(&rust, "TABLE_ID")?;
    let table_size = rust_const(&rust, "TABLE_SIZE")?;
    let padding_row = rust_const(&rust, "PADDING_ROW")?;
    ensure!(
        table_id == EXPECTED_TABLE_ID,
        "MemAlignRomSM::TABLE_ID changed: expected {EXPECTED_TABLE_ID}, got {table_id}"
    );
    ensure!(
        table_size == EXPECTED_TABLE_SIZE,
        "MemAlignRomSM::TABLE_SIZE changed: expected {EXPECTED_TABLE_SIZE}, got {table_size}"
    );
    ensure!(
        padding_row == EXPECTED_PADDING_ROW,
        "MemAlignRomSM::PADDING_ROW changed: expected {EXPECTED_PADDING_ROW}, got {padding_row}"
    );
    ensure!(
        pil.contains("lookup_proves(MEMORY_ALIGN_ROM_ID, [PC, DELTA_PC, DELTA_ADDR, OFFSET, WIDTH, FLAGS], multiplicity)"),
        "MemAlignRom lookup_proves tuple no longer has the expected six-column shape"
    );

    let program_rows = program_rows(&pil)?;
    ensure!(program_rows < table_size, "program exceeds physical table size");
    let compiled = std::fs::read_to_string(compiled_rows)
        .with_context(|| format!("failed to read {}", compiled_rows.display()))?;
    let rows = parse_compiled_rows(&compiled, table_size)?;

    let lean = emit_lean(&rows, table_id, table_size, padding_row, program_rows);
    if let Some(path) = output {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).ok();
        }
        std::fs::write(path, &lean)
            .with_context(|| format!("failed to write {}", path.display()))?;
        tracing::info!(path = %path.display(), rows = rows.len(), "wrote MemAlignRom extraction");
    }
    Ok(lean)
}

fn rust_const(source: &str, name: &str) -> Result<usize> {
    let pattern = format!(r"pub const {name}: \w+\s*=\s*(\d+)");
    let re = Regex::new(&pattern).expect("constant regex is valid");
    let capture = re
        .captures(source)
        .with_context(|| format!("MemAlignRomSM::{name} declaration not found"))?;
    capture[1]
        .parse()
        .with_context(|| format!("MemAlignRomSM::{name} is not a natural number"))
}

fn program_rows(source: &str) -> Result<usize> {
    let sizes = int_array(source, "spsize")?;
    ensure!(sizes.len() == 4, "spsize must have four operation lengths");
    let one_word = const_int(source, "one_word_combinations")?;
    let two_word = const_int(source, "two_word_combinations")?;
    Ok(one_word * sizes[0] + one_word * sizes[1] + two_word * sizes[2] + two_word * sizes[3])
}

fn const_int(source: &str, name: &str) -> Result<usize> {
    let pattern = format!(r"const int {name}\s*=\s*(\d+)");
    let re = Regex::new(&pattern).expect("constant regex is valid");
    let capture = re
        .captures(source)
        .with_context(|| format!("PIL constant {name} not found"))?;
    capture[1]
        .parse()
        .with_context(|| format!("PIL constant {name} is not a natural number"))
}

fn int_array(source: &str, name: &str) -> Result<Vec<usize>> {
    let pattern = format!(r"const int {name}\s*\[\d+\]\s*=\s*\[([^\]]+)\]");
    let re = Regex::new(&pattern).expect("array regex is valid");
    let capture = re
        .captures(source)
        .with_context(|| format!("PIL integer array {name} not found"))?;
    capture[1]
        .split(',')
        .map(|value| value.trim().parse().with_context(|| format!("invalid {name} entry {value}")))
        .collect()
}

/// Parse rows observed from the compiler, preserving every column and row.
fn parse_compiled_rows(source: &str, table_size: usize) -> Result<Vec<Row>> {
    let mut lines = source.lines();
    ensure!(
        lines.next() == Some("PC\tDELTA_PC\tDELTA_ADDR\tOFFSET\tWIDTH\tFLAGS"),
        "compiled MemAlignRom column order differs from the lookup tuple"
    );
    let mut rows = Vec::new();
    for (index, line) in lines.enumerate() {
        let values = line.split('\t')
            .map(|value| value.parse::<i64>().context("invalid compiled fixed-column value"))
            .collect::<Result<Vec<_>>>()?;
        ensure!(values.len() == 6, "compiled MemAlignRom row {index} must have six columns");
        rows.push(Row {
            pc: values[0], delta_pc: values[1], delta_addr: values[2],
            offset: values[3], width: values[4], flags: values[5],
        });
    }
    ensure!(rows.len() == table_size,
        "compiled MemAlignRom has {} rows, expected {table_size}", rows.len());
    Ok(rows)
}

fn emit_lean(
    rows: &[Row],
    table_id: usize,
    table_size: usize,
    padding_row: usize,
    program_rows: usize,
) -> String {
    let mut out = String::new();
    writeln!(out, "import ZiskFv.Field.Goldilocks").unwrap();
    out.push('\n');
    writeln!(out, "/-!").unwrap();
    writeln!(out, "# Extracted MemAlignRom fixed table.").unwrap();
    out.push('\n');
    writeln!(out, "Auto-generated by `pil-extract mem-align-rom` from the fixed").unwrap();
    writeln!(out, "columns observed by the pinned PIL compiler executing").unwrap();
    writeln!(out, "`zisk/state-machines/mem/pil/mem_align_rom.pil:6-313`.").unwrap();
    writeln!(out, "The physical table parameters are checked against").unwrap();
    writeln!(out, "`zisk/state-machines/mem/src/mem_align_rom_sm.rs::MemAlignRomSM`.").unwrap();
    writeln!(out, "The six fields retain the `lookup_proves` order:").unwrap();
    writeln!(out, "`[PC, DELTA_PC, DELTA_ADDR, OFFSET, WIDTH, FLAGS]` on bus 133.").unwrap();
    writeln!(
        out,
        "The {} physical rows include {} program rows and {} reset-padding rows",
        rows.len(),
        program_rows,
        rows.len() - program_rows
    )
    .unwrap();

    writeln!(out, "-/").unwrap();
    out.push('\n');
    writeln!(out, "namespace Extraction.MemAlignRom").unwrap();
    out.push('\n');
    writeln!(out, "open Goldilocks").unwrap();
    out.push('\n');
    writeln!(out, "structure Row where").unwrap();
    writeln!(out, "  pc : FGL").unwrap();
    writeln!(out, "  deltaPc : FGL").unwrap();
    writeln!(out, "  deltaAddr : FGL").unwrap();
    writeln!(out, "  offset : FGL").unwrap();
    writeln!(out, "  width : FGL").unwrap();
    writeln!(out, "  flags : FGL").unwrap();
    writeln!(out, "  deriving DecidableEq").unwrap();
    out.push('\n');
    writeln!(out, "def tableId : Nat := {table_id}").unwrap();
    writeln!(out, "def tableSize : Nat := {table_size}").unwrap();
    writeln!(out, "def paddingRowIndex : Nat := {padding_row}").unwrap();
    writeln!(out, "def programRowCount : Nat := {program_rows}").unwrap();
    out.push('\n');
    writeln!(out, "set_option maxRecDepth 100000 in").unwrap();
    writeln!(out, "def rows : Vector Row {table_size} := #v[").unwrap();
    for (index, row) in rows.iter().enumerate() {
        let comma = if index + 1 == rows.len() { "" } else { "," };
        writeln!(
            out,
            "  {{ pc := {}, deltaPc := {}, deltaAddr := {}, offset := {}, width := {}, flags := {} }}{}",
            lean_fgl(row.pc),
            lean_fgl(row.delta_pc),
            lean_fgl(row.delta_addr),
            lean_fgl(row.offset),
            lean_fgl(row.width),
            lean_fgl(row.flags),
            comma,
        )
        .unwrap();
    }
    writeln!(out, "]").unwrap();
    out.push('\n');
    writeln!(out, "end Extraction.MemAlignRom").unwrap();
    out
}

fn lean_fgl(value: i64) -> String {
    format!("({value} : FGL)")
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEADER: &str = "PC\tDELTA_PC\tDELTA_ADDR\tOFFSET\tWIDTH\tFLAGS\n";

    #[test]
    fn compiled_rows_preserve_all_fields_and_signs() {
        let rows = parse_compiled_rows(&format!("{HEADER}1\t-1\t0\t0\t1\t1\n"), 1).unwrap();
        assert_eq!(rows[0], Row {
            pc: 1, delta_pc: -1, delta_addr: 0, offset: 0, width: 1, flags: 1,
        });
    }

    #[test]
    fn rejects_missing_extra_or_misordered_columns_and_rows() {
        for source in [
            format!("{HEADER}0\t0\t0\t0\t0\n"),
            format!("{HEADER}0\t0\t0\t0\t0\t512\t0\n"),
            format!("{HEADER}0\t0\t0\t0\t0\t512\n0\t0\t0\t0\t0\t512\n"),
            HEADER.to_string(),
            format!("{}0\t0\t0\t0\t0\t512\n", HEADER.replace("PC\tDELTA_PC", "DELTA_PC\tPC")),
        ] {
            assert!(parse_compiled_rows(&source, 1).is_err());
        }
    }
}
