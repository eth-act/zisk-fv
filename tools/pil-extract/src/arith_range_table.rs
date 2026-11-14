//! Extract the Arith chunk-range inverse from the Rust helper's constants and row formula.
//! The supported source grammar is deliberately narrow: unknown expressions fail closed.

use std::fmt::Write;

use anyhow::{bail, Context, Result};
use regex::Regex;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HalfBlock {
    id: usize,
    kind: usize,
    high_full: bool,
    neg: bool,
}

#[derive(Debug)]
struct Source {
    full: usize,
    pos: usize,
    neg: usize,
    ranges: Vec<usize>,
    offsets: Vec<usize>,
    half_block_size: usize,
    chunk_rows: usize,
    table_length: usize,
    blocks: Vec<HalfBlock>,
}

pub(crate) fn render(rust_source: &str) -> Result<String> {
    Ok(emit_lean(&parse(rust_source)?))
}

fn number(text: &str) -> Result<usize> {
    let text = text.trim().replace('_', "");
    if let Some(hex) = text.strip_prefix("0x") {
        usize::from_str_radix(hex, 16).context("invalid hexadecimal literal")
    } else {
        text.parse().context("invalid unsigned literal")
    }
}

fn declaration(text: &str, name: &str, ty: &str) -> Result<String> {
    let re = Regex::new(&format!(
        r"(?m)^\s*const\s+{}\s*:\s*{}\s*=\s*([^;]+);",
        regex::escape(name), ty
    ))?;
    let mut matches = re.captures_iter(text);
    let value = matches.next().with_context(|| format!("missing or unsupported {name}"))?;
    if matches.next().is_some() {
        bail!("duplicate {name} declaration");
    }
    Ok(value[1].trim().to_owned())
}

fn array(text: &str, name: &str, ty: &str, symbols: &[(&str, usize)]) -> Result<Vec<usize>> {
    let re = Regex::new(&format!(
        r"(?m)^\s*const\s+{}\s*:\s*\[\s*{}\s*;\s*([0-9_]+)\s*\]\s*=\s*\[([^\]]*)\]\s*;",
        regex::escape(name), ty
    ))?;
    let mut matches = re.captures_iter(text);
    let caps = matches.next().with_context(|| format!("missing or unsupported {name} array"))?;
    if matches.next().is_some() {
        bail!("duplicate {name} array");
    }
    let len = number(&caps[1])?;
    let mut entries: Vec<&str> = caps[2].split(',').map(str::trim).collect();
    if entries.last() == Some(&"") {
        entries.pop();
    }
    let values = entries.into_iter().map(|entry| {
        if let Some((_, value)) = symbols.iter().find(|(symbol, _)| *symbol == entry) {
            Ok(*value)
        } else {
            number(entry).with_context(|| format!("unsupported {name} entry {entry:?}"))
        }
    }).collect::<Result<Vec<_>>>()?;
    if len == 0 || values.len() != len {
        bail!("{name} array length does not match its declaration");
    }
    Ok(values)
}

fn function_body(text: &str, name: &str) -> Result<String> {
    let re = Regex::new(&format!(r"\bpub\s+fn\s+{}\s*\([^{{]*\{{", regex::escape(name)))?;
    let mut matches = re.find_iter(text);
    let start = matches.next().with_context(|| format!("missing {name}"))?.end();
    if matches.next().is_some() {
        bail!("duplicate {name}");
    }
    let mut depth = 1usize;
    for (offset, ch) in text[start..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(text[start..start + offset].chars().filter(|c| !c.is_whitespace()).collect());
                }
            }
            _ => {}
        }
    }
    bail!("unclosed {name}")
}

fn parse(text: &str) -> Result<Source> {
    // Ignore upstream documentation and line comments, not arbitrary unparsed array tokens.
    let comments = Regex::new(r"(?m)//[^\n]*")?;
    let text = comments.replace_all(text, "");
    let full = number(&declaration(&text, "FULL", "u8")?)?;
    let pos = number(&declaration(&text, "POS", "u8")?)?;
    let neg = number(&declaration(&text, "NEG", "u8")?)?;
    if full > 255 || pos > 255 || neg > 255 || full == pos || full == neg || pos == neg {
        bail!("FULL/POS/NEG must be distinct u8 values");
    }
    let symbols = [("FULL", full), ("POS", pos), ("NEG", neg)];
    let ranges = array(&text, "RANGES", "u8", &symbols)?;
    let offsets = array(&text, "OFFSETS", "usize", &[])?;
    if ranges.len() != offsets.len() || ranges.iter().any(|r| ![full, pos, neg].contains(r)) {
        bail!("inconsistent RANGES/OFFSETS or unknown range kind");
    }
    let rows = declaration(&text, "ROWS", "usize")?;
    let parts: Vec<_> = rows.split("<<").collect();
    let table_length = match parts.as_slice() {
        [literal] => number(literal)?,
        [base, shift] => {
            let base = number(base)?;
            let shift = u32::try_from(number(shift)?)?;
            base.checked_shl(shift).filter(|result| (*result >> shift) == base)
                .context("ROWS overflow")?
        }
        _ => bail!("unsupported ROWS expression"),
    };

    // Parse the *whole* supported helper body, including source assertions. A changed
    // formula cannot silently retain a stale model. Captured literals drive the model.
    let chunk = function_body(&text, "get_row_chunk_range_check")?;
    let literal = r"(0x[0-9a-fA-F_]+|[0-9_]+)";
    let chunk_re = Regex::new(&format!(
        concat!(r#"^letrange_type=RANGES\[range_indexasusize\];assert!\(range_index<{}\);"#,
            r#"assert!\(value>=ifrange_type==NEG\{{{}\}}else\{{{}\}}\);"#,
            r#"assert!\(value<=matchrange_type\{{FULL=>{},POS=>{},NEG=>{},_=>panic!\("[^"\n]*"\),\}}\);"#,
            r#"OFFSETS\[range_indexasusize\]\*{}\+ifrange_type==NEG\{{value-{}\}}else\{{value\}}asusize$"#),
        literal, literal, literal, literal, literal, literal, literal, literal
    ))?;
    let caps = chunk_re.captures(&chunk).context("unsupported chunk row formula/assertions")?;
    let literals = (1..=8).map(|i| number(&caps[i])).collect::<Result<Vec<_>>>()?;
    let [range_count, neg_min, other_min, full_max, pos_max, neg_max, half_block_size, neg_adjust] =
        <[usize; 8]>::try_from(literals).unwrap();
    if range_count != ranges.len() || half_block_size == 0 || neg_min != half_block_size
        || neg_adjust != half_block_size || other_min != 0
        || half_block_size.checked_mul(2).and_then(|n| n.checked_sub(1)) != Some(full_max)
        || pos_max.checked_add(1) != Some(half_block_size) || neg_max != full_max
    {
        bail!("inconsistent chunk range bounds/formula");
    }
    let carry = function_body(&text, "get_row_carry_range_check")?;
    let carry_re = Regex::new(&format!(
        r"^assert!\(value>=-{}\);assert!\(value<={}\);\({}\+{}\+value\)asusize$",
        literal, literal, literal, literal
    ))?;
    let caps = carry_re.captures(&carry).context("unsupported carry row formula")?;
    let carry_min = number(&caps[1])?;
    let carry_max = number(&caps[2])?;
    let chunk_rows = number(&caps[3])?;
    if number(&caps[4])? != carry_min
        || chunk_rows.checked_add(carry_min).and_then(|n| n.checked_add(carry_max))
            .and_then(|n| n.checked_add(1)) != Some(table_length)
        || chunk_rows % half_block_size != 0
    {
        bail!("inconsistent chunk/carry region dimensions");
    }
    let block_count = chunk_rows / half_block_size;
    let occupied = ranges.iter().map(|kind| if *kind == full { 2 } else { 1 }).sum::<usize>();
    if occupied != block_count {
        bail!("chunk region has missing or excess half-block data");
    }
    let mut blocks = vec![None; block_count];
    for (id, (&kind, &offset)) in ranges.iter().zip(&offsets).enumerate() {
        let width = if kind == full { 2 } else { 1 };
        for half in 0..width {
            let index = offset.checked_add(half).context("offset overflow")?;
            let slot = blocks.get_mut(index).context("half-block offset outside chunk region")?;
            if slot.is_some() {
                bail!("overlapping half-block at {index}");
            }
            *slot = Some(HalfBlock { id, kind, high_full: half == 1, neg: kind == neg });
        }
    }
    let blocks = blocks.into_iter().map(|b| b.context("missing chunk half-block")).collect::<Result<_>>()?;
    Ok(Source { full, pos, neg, ranges, offsets, half_block_size, chunk_rows, table_length, blocks })
}

fn emit_lean(source: &Source) -> String {
    let mut out = String::from("import Mathlib\n\n/-! Source-extracted Arith RANGES/OFFSETS inverse.\nGenerated by `pil-extract arith-range-table` from\n`state-machines/arith/src/arith_range_table_helpers.rs`.\nThe finite inverse certificates below are checked by the Lean kernel. -/\n\nnamespace Extraction.ArithRangeTable\n\n");
    for (name, value) in [
        ("full", source.full), ("pos", source.pos), ("neg", source.neg),
        ("halfBlockSize", source.half_block_size), ("chunkRows", source.chunk_rows),
        ("tableLength", source.table_length), ("halfBlockCount", source.blocks.len()),
    ] {
        writeln!(out, "def {name} : Nat := {value}\n").unwrap();
    }
    for (name, values) in [("ranges", &source.ranges), ("offsets", &source.offsets)] {
        writeln!(out, "def {name} : List Nat := {:?}\n", values).unwrap();
    }
    for (name, ty) in [("halfBlockId", "Nat"), ("halfBlockKind", "Option Nat"),
        ("halfBlockHighFull", "Bool"), ("halfBlockNeg", "Bool")] {
        writeln!(out, "def {name} : Nat → {ty}").unwrap();
        for (index, block) in source.blocks.iter().enumerate() {
            match name {
                "halfBlockId" => writeln!(out, "  | {index} => {}", block.id),
                "halfBlockKind" => writeln!(out, "  | {index} => some {}", block.kind),
                "halfBlockHighFull" => writeln!(out, "  | {index} => {}", block.high_full),
                "halfBlockNeg" => writeln!(out, "  | {index} => {}", block.neg),
                _ => unreachable!(),
            }.unwrap();
        }
        let outside = match ty {
            "Nat" => "0", // Preserve the existing live inverse's out-of-domain behavior.
            "Option Nat" => "none",
            _ => "false",
        };
        writeln!(out, "  | _ => {outside}\n").unwrap();
    }
    out.push_str(r#"/-- Source row arithmetic; absent IDs stay absent, rather than acquiring a zero row.
The Rust helper's assertions are expressed by `ChunkValueValid`. -/
def chunkRow (rangeId value : Nat) : Option Nat := do
  let kind ← ranges[rangeId]?
  let offset ← offsets[rangeId]?
  pure (offset * halfBlockSize + if kind = neg then value - halfBlockSize else value)

def ChunkValueValid (rangeId value : Nat) : Prop :=
  (ranges[rangeId]? = some full ∧ value < 2 * halfBlockSize) ∨
  (ranges[rangeId]? = some pos ∧ value < halfBlockSize) ∨
  (ranges[rangeId]? = some neg ∧ halfBlockSize ≤ value ∧ value < 2 * halfBlockSize)

set_option maxHeartbeats 2000000 in
/-- Every generated inverse entry comes from the actual source arrays. -/
theorem halfBlock_source_data (block : Fin halfBlockCount) :
    ranges[halfBlockId block.val]? = halfBlockKind block.val ∧
    offsets[halfBlockId block.val]? =
      some (block.val - if halfBlockHighFull block.val then 1 else 0) ∧
    (halfBlockHighFull block.val = true → halfBlockKind block.val = some full) ∧
    (halfBlockNeg block.val = true ↔ halfBlockKind block.val = some neg) := by
  fin_cases block <;> decide

set_option maxHeartbeats 2000000 in
/-- Symbolic inversion of the Rust chunk-row formula, including its value bounds. -/
theorem halfBlock_row_inverse (block : Fin halfBlockCount) (rem : Nat)
    (hrem : rem < halfBlockSize) :
    let value := rem + if halfBlockHighFull block.val || halfBlockNeg block.val
      then halfBlockSize else 0
    ChunkValueValid (halfBlockId block.val) value ∧
      chunkRow (halfBlockId block.val) value = some (block.val * halfBlockSize + rem) := by
  have hrem' : rem < halfBlockSize := hrem
  norm_num [halfBlockSize] at hrem'
  fin_cases block <;>
    simp [ChunkValueValid, chunkRow, ranges, offsets, full, pos, neg,
      halfBlockId, halfBlockHighFull, halfBlockNeg, halfBlockSize,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

end Extraction.ArithRangeTable
"#);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // The source-bearing declarations and method bodies from the pinned helper.
    const SOURCE: &str = r#"
const ROWS: usize = 1 << 22;
const FULL: u8 = 0x00;
const POS: u8 = 0x01;
const NEG: u8 = 0x02;
const RANGES: [u8; 43] = [
    FULL, FULL, FULL, POS, POS, POS, NEG, NEG, NEG, FULL, FULL, FULL, FULL, FULL, FULL, FULL, FULL,
    FULL, POS, NEG, FULL, POS, NEG, FULL, POS, NEG, FULL, FULL, FULL, FULL, FULL, FULL, FULL, FULL,
    FULL, FULL, FULL, POS, POS, POS, NEG, NEG, NEG,
];
const OFFSETS: [usize; 43] = [
    0, 2, 4, 50, 51, 52, 59, 60, 61, 6, 8, 10, 12, 14, 16, 18, 20, 22, 53, 62, 24, 54, 63, 26, 55,
    64, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 56, 57, 58, 65, 66, 67,
];
pub fn get_row_chunk_range_check(range_index: u8, value: u64) -> usize {
    let range_type = RANGES[range_index as usize];
    assert!(range_index < 43);
    assert!(value >= if range_type == NEG { 0x8000 } else { 0 });
    assert!(value <= match range_type {
        FULL => 0xFFFF, POS => 0x7FFF, NEG => 0xFFFF, _ => panic!("Invalid range type"),
    });
    OFFSETS[range_index as usize] * 0x8000
        + if range_type == NEG { value - 0x8000 } else { value } as usize
}
pub fn get_row_carry_range_check(value: i64) -> usize {
    assert!(value >= -0xEFFFF);
    assert!(value <= 0xF0000);
    (0x220000 + 0xEFFFF + value) as usize
}
"#;

    #[test]
    fn parses_source_and_inverts_every_half_block() {
        let source = parse(SOURCE).unwrap();
        assert_eq!(source.blocks.len(), 68);
        for (index, block) in source.blocks.iter().enumerate() {
            assert_eq!(source.ranges[block.id], block.kind);
            let delta = usize::from(block.high_full);
            assert_eq!(source.offsets[block.id] + delta, index);
            assert_eq!(block.neg, block.kind == source.neg);
            for rem in [0, source.half_block_size - 1] {
                let value = rem + if block.high_full || block.neg { source.half_block_size } else { 0 };
                let adjusted = if block.neg { value - source.half_block_size } else { value };
                assert_eq!(source.offsets[block.id] * source.half_block_size + adjusted,
                    index * source.half_block_size + rem);
            }
        }
    }

    #[test]
    fn changed_offsets_change_the_consumed_inverse() {
        let changed = SOURCE.replace("0, 2, 4, 50", "2, 0, 4, 50");
        let source = parse(&changed).unwrap();
        assert_eq!(source.blocks[0].id, 1);
        assert_eq!(source.blocks[2].id, 0);
        assert!(source.blocks[1].high_full);
    }

    #[test]
    fn changed_range_kinds_change_the_consumed_flags() {
        // Exchange one POS and one NEG kind, preserving the source's partition.
        let changed = SOURCE.replace("FULL, FULL, FULL, POS, POS, POS, NEG, NEG, NEG, FULL",
            "FULL, FULL, FULL, NEG, POS, POS, POS, NEG, NEG, FULL");
        let source = parse(&changed).unwrap();
        assert_eq!(source.blocks[50].id, 3);
        assert!(source.blocks[50].neg);
        assert_eq!(source.blocks[59].id, 6);
        assert!(!source.blocks[59].neg);
    }

    #[test]
    fn rejects_overlap_holes_and_bad_array_entries() {
        for changed in [
            SOURCE.replace("0, 2, 4, 50", "0, 0, 4, 50"),
            SOURCE.replace("65, 66, 67,", "65, 66, 68,"),
            SOURCE.replace("FULL, FULL, FULL, POS", "POS, FULL, FULL, POS"),
            SOURCE.replace("NEG, NEG, NEG,\n];", "NEG, NEG,\n];"),
            SOURCE.replace("FULL, FULL, FULL, POS", "UNKNOWN, FULL, FULL, POS"),
            SOURCE.replace("0, 2, 4, 50", "0, 2 + 0, 4, 50"),
        ] {
            assert!(parse(&changed).is_err());
        }
    }

    #[test]
    fn rejects_changed_or_inconsistent_row_formula() {
        for changed in [
            SOURCE.replace("* 0x8000", "* 0x4000"),
            SOURCE.replace("value - 0x8000", "value + 0x8000"),
            SOURCE.replace("(0x220000 +", "(0x218000 +"),
        ] {
            assert!(parse(&changed).is_err());
        }
    }
}
