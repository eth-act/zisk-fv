//! Extract the fixed 256-row MemAlign ROM from its upstream PIL definition.
//!
//! `MemAlignRom` is virtual, so it is intentionally absent from pilout's AIR
//! list. Its authoritative rows instead come from the `OFFSET` and `WIDTH`
//! fixed-column definitions plus the fixed-column builder in
//! `mem_align_rom.pil`. The Rust state-machine source supplies the separately
//! checked physical table parameters (id, size, and padding-row index).

use std::fmt::Write;
use std::path::Path;

use anyhow::{bail, ensure, Context, Result};
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
pub fn run(pil_source: &Path, rust_source: &Path, output: Option<&Path>) -> Result<String> {
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

    let offsets = fixed_column(&pil, "OFFSET", table_size)?;
    let widths = fixed_column(&pil, "WIDTH", table_size)?;
    let program_rows = program_rows(&pil)?;
    let rows = build_rows(&offsets, &widths, program_rows)?;
    ensure!(rows.len() == table_size, "row builder emitted {} rows", rows.len());

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

fn fixed_column(source: &str, name: &str, length: usize) -> Result<Vec<usize>> {
    let without_comments = source
        .lines()
        .map(|line| line.split_once("//").map_or(line, |(before, _)| before))
        .collect::<Vec<_>>()
        .join("\n");
    let declaration = format!("col fixed {name}");
    let start = without_comments
        .find(&declaration)
        .with_context(|| format!("fixed column {name} not found"))?;
    let tail = &without_comments[start + declaration.len()..];
    let equals = tail
        .find('=')
        .with_context(|| format!("fixed column {name} has no initializer"))?;
    let semicolon = tail[equals + 1..]
        .find(';')
        .with_context(|| format!("fixed column {name} has no terminating semicolon"))?;
    let initializer = &tail[equals + 1..equals + 1 + semicolon];
    let mut parser = FixedColumnParser::new(initializer);
    let (mut values, tail_fill) = parser.list(true)?;
    parser.finish()?;
    if let Some(fill) = tail_fill {
        ensure!(values.len() <= length, "fixed column {name} prefix exceeds {length} rows");
        values.resize(length, fill);
    }
    ensure!(
        values.len() == length,
        "fixed column {name} has {} rows, expected {length}",
        values.len()
    );
    Ok(values)
}

struct FixedColumnParser<'a> {
    input: &'a [u8],
    position: usize,
}

impl<'a> FixedColumnParser<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            position: 0,
        }
    }

    fn list(&mut self, allow_tail: bool) -> Result<(Vec<usize>, Option<usize>)> {
        self.skip_space();
        self.expect(b'[')?;
        let mut values = Vec::new();
        let mut tail_fill = None;
        loop {
            self.skip_space_and_commas();
            if self.consume(b']') {
                break;
            }
            let (item, item_tail) = if self.peek() == Some(b'[') {
                self.list(false)?
            } else {
                let value = self.natural()?;
                if self.consume_bytes(b"...") {
                    ensure!(allow_tail, "ellipsis is only supported in the outer fixed-column list");
                    (Vec::new(), Some(value))
                } else {
                    (vec![value], None)
                }
            };
            ensure!(item_tail.is_none() || tail_fill.is_none(), "multiple fixed-column ellipses");
            if let Some(fill) = item_tail {
                tail_fill = Some(fill);
            } else {
                let repeat = if self.consume(b':') { self.natural()? } else { 1 };
                for _ in 0..repeat {
                    values.extend_from_slice(&item);
                }
            }
        }
        Ok((values, tail_fill))
    }

    fn finish(&mut self) -> Result<()> {
        self.skip_space();
        ensure!(self.position == self.input.len(), "unexpected fixed-column syntax after initializer");
        Ok(())
    }

    fn natural(&mut self) -> Result<usize> {
        self.skip_space();
        let start = self.position;
        while self.peek().is_some_and(|byte| byte.is_ascii_digit()) {
            self.position += 1;
        }
        ensure!(start != self.position, "expected a natural-number fixed-column value");
        std::str::from_utf8(&self.input[start..self.position])
            .expect("digits are UTF-8")
            .parse()
            .context("fixed-column value does not fit usize")
    }

    fn skip_space_and_commas(&mut self) {
        loop {
            self.skip_space();
            if !self.consume(b',') {
                break;
            }
        }
    }

    fn skip_space(&mut self) {
        while self.peek().is_some_and(|byte| byte.is_ascii_whitespace()) {
            self.position += 1;
        }
    }

    fn expect(&mut self, byte: u8) -> Result<()> {
        ensure!(self.consume(byte), "expected `{}` in fixed-column initializer", byte as char);
        Ok(())
    }

    fn consume(&mut self, byte: u8) -> bool {
        self.skip_space();
        if self.peek() == Some(byte) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn consume_bytes(&mut self, bytes: &[u8]) -> bool {
        if self.input[self.position..].starts_with(bytes) {
            self.position += bytes.len();
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<u8> {
        self.input.get(self.position).copied()
    }
}

fn build_rows(offsets: &[usize], widths: &[usize], program_rows: usize) -> Result<Vec<Row>> {
    ensure!(offsets.len() == widths.len(), "OFFSET/WIDTH length mismatch");
    ensure!(program_rows == 188, "MemAlignRom program size changed: expected 188, got {program_rows}");
    ensure!(offsets.len() == EXPECTED_TABLE_SIZE, "MemAlignRom must have 256 fixed rows");

    let mut rows = Vec::with_capacity(offsets.len());
    for line in 0..offsets.len() {
        let mut pc = 0i64;
        let mut delta_pc = 0i64;
        let mut delta_addr = 0i64;
        let mut is_write = 0i64;
        let mut reset = 0i64;
        let mut selectors = [0i64; 8];
        let mut up_to_down = 0i64;
        let mut down_to_up = 0i64;

        if line == 0 || line > program_rows {
            reset = 1;
        } else if line < 41 {
            if line % 2 == 1 {
                delta_pc = line as i64;
                reset = 1;
                mark_range(&mut selectors, offsets[line + 1], widths[line + 1]);
                up_to_down = 1;
            } else {
                pc = (line - 1) as i64;
                delta_pc = -pc;
                mark_one(&mut selectors, offsets[line]);
            }
        } else if line < 101 {
            if line % 3 == 2 {
                delta_pc = line as i64;
                reset = 1;
                mark_complement_range(&mut selectors, offsets[line + 2], widths[line + 2]);
                up_to_down = 1;
            } else if line % 3 == 0 {
                pc = (line - 1) as i64;
                delta_pc = 1;
                is_write = 1;
                mark_range(&mut selectors, offsets[line + 1], widths[line + 1]);
                up_to_down = 1;
            } else {
                pc = (line - 1) as i64;
                delta_pc = -pc;
                is_write = 1;
                mark_one(&mut selectors, offsets[line]);
            }
        } else if line < 134 {
            if line % 3 == 2 {
                delta_pc = line as i64;
                reset = 1;
                mark_from(&mut selectors, offsets[line + 1]);
                up_to_down = 1;
            } else if line % 3 == 0 {
                pc = (line - 1) as i64;
                delta_pc = 1;
                mark_one(&mut selectors, offsets[line]);
            } else {
                pc = (line - 1) as i64;
                delta_pc = -pc;
                delta_addr = 1;
                mark_before(&mut selectors, (offsets[line - 1] + widths[line - 1]) % 8);
                down_to_up = 1;
            }
        } else if line < 189 {
            if line % 5 == 4 {
                delta_pc = line as i64;
                reset = 1;
                mark_before(&mut selectors, offsets[line + 2]);
                up_to_down = 1;
            } else if line % 5 == 0 {
                pc = (line - 1) as i64;
                delta_pc = 1;
                is_write = 1;
                mark_from(&mut selectors, offsets[line + 1]);
                up_to_down = 1;
            } else if line % 5 == 1 {
                pc = (line - 1) as i64;
                delta_pc = 1;
                is_write = 1;
                mark_one(&mut selectors, offsets[line]);
            } else if line % 5 == 2 {
                pc = (line - 1) as i64;
                delta_pc = 1;
                delta_addr = 1;
                is_write = 1;
                mark_before(&mut selectors, (offsets[line - 1] + widths[line - 1]) % 8);
                down_to_up = 1;
            } else {
                pc = (line - 1) as i64;
                delta_pc = -pc;
                mark_from(&mut selectors, (offsets[line - 2] + widths[line - 2]) % 8);
                down_to_up = 1;
            }
        } else {
            bail!("MemAlignRom row {line} has no source builder case");
        }

        let flags = selectors
            .iter()
            .enumerate()
            .map(|(index, selector)| selector * (1i64 << index))
            .sum::<i64>()
            + is_write * 256
            + reset * 512
            + up_to_down * 1024
            + down_to_up * 2048;
        rows.push(Row {
            pc,
            delta_pc,
            delta_addr,
            offset: offsets[line] as i64,
            width: widths[line] as i64,
            flags,
        });
    }
    Ok(rows)
}

fn mark_one(selectors: &mut [i64; 8], index: usize) {
    selectors[index] = 1;
}

fn mark_range(selectors: &mut [i64; 8], offset: usize, width: usize) {
    for (index, selector) in selectors.iter_mut().enumerate() {
        if index >= offset && index < offset + width {
            *selector = 1;
        }
    }
}

fn mark_complement_range(selectors: &mut [i64; 8], offset: usize, width: usize) {
    for (index, selector) in selectors.iter_mut().enumerate() {
        if index < offset || index >= offset + width {
            *selector = 1;
        }
    }
}

fn mark_from(selectors: &mut [i64; 8], offset: usize) {
    for (index, selector) in selectors.iter_mut().enumerate() {
        if index >= offset {
            *selector = 1;
        }
    }
}

fn mark_before(selectors: &mut [i64; 8], end: usize) {
    for selector in selectors.iter_mut().take(end) {
        *selector = 1;
    }
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
    writeln!(out, "`OFFSET`/`WIDTH` columns and row builder in").unwrap();
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
    writeln!(out, "whose exact tuple is `[0, 0, 0, 0, 0, 512]`.").unwrap();
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

    #[test]
    fn parses_nested_repetition_and_outer_padding() {
        let source = "col fixed OFFSET = [0, [[0, 1]:2, 3], 0...];";
        assert_eq!(
            fixed_column(source, "OFFSET", 8).unwrap(),
            vec![0, 0, 1, 0, 1, 3, 0, 0],
        );
    }

    #[test]
    fn builder_preserves_the_reset_padding_tuple() {
        let offsets = vec![0; EXPECTED_TABLE_SIZE];
        let widths = vec![0; EXPECTED_TABLE_SIZE];
        let rows = build_rows(&offsets, &widths, 188).unwrap();
        assert_eq!(rows.len(), EXPECTED_TABLE_SIZE);
        assert_eq!(
            rows[0],
            Row {
                pc: 0,
                delta_pc: 0,
                delta_addr: 0,
                offset: 0,
                width: 0,
                flags: 512,
            }
        );
        assert_eq!(rows[189].flags, 512);
    }
}
