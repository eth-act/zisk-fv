use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Context, Result};
use clap::Parser;
use prost::Message;

pub mod pilout {
    include!(concat!(env!("OUT_DIR"), "/pilout.rs"));
}

use pilout::{
    constraint::Constraint as ConstraintKind, expression::Operation as ExprOp,
    operand::Operand as OperandKind, Air, Constraint, Expression, Operand, PilOut, SymbolType,
};

#[derive(Parser, Debug)]
#[command(
    name = "zisk-pil-extract",
    about = "Emit Lean4 constraint definitions for a single AIR from a ZisK pilout."
)]
struct Cli {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match).
    #[arg(long)]
    air: String,

    /// Output path for the generated .lean file. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,

    /// List AIRs and exit (ignores --air).
    #[arg(long)]
    list: bool,

    /// Emit a commented stub instead of erroring when a constraint uses an
    /// operand kind we don't render yet (FixedCol, Challenge, …). Off by
    /// default: unsupported operands in the selected AIR abort the run.
    #[arg(long)]
    skip_unsupported: bool,

    /// Restrict emission to the given constraint indices (comma-separated).
    /// Constraints outside this set are omitted entirely (no stub). An
    /// unsupported operand inside an `--only` constraint always aborts,
    /// regardless of `--skip-unsupported`.
    #[arg(long, value_delimiter = ',')]
    only: Vec<usize>,
}

fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with_writer(std::io::stderr)
        .init();

    let cli = Cli::parse();

    let bytes = fs::read(&cli.pilout)
        .with_context(|| format!("failed to read pilout {}", cli.pilout.display()))?;
    let pilout = PilOut::decode(bytes.as_slice()).context("failed to decode pilout protobuf")?;

    if cli.list {
        list_airs(&pilout);
        return Ok(());
    }

    let hit = find_air(&pilout, &cli.air)?;
    let opts = RenderOpts {
        skip_unsupported: cli.skip_unsupported,
        only: if cli.only.is_empty() { None } else { Some(cli.only.iter().copied().collect()) },
    };
    let rendered = render_air(&pilout, hit, &opts)?;

    match &cli.output {
        Some(path) => {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).ok();
            }
            fs::write(path, &rendered)
                .with_context(|| format!("failed to write {}", path.display()))?;
            tracing::info!(path = %path.display(), "wrote extraction");
        }
        None => print!("{}", rendered),
    }
    Ok(())
}

fn list_airs(pilout: &PilOut) {
    for (gi, group) in pilout.air_groups.iter().enumerate() {
        let gname = group.name.as_deref().unwrap_or("<unnamed>");
        for (ai, air) in group.airs.iter().enumerate() {
            let aname = air.name.as_deref().unwrap_or("<unnamed>");
            println!(
                "[{}][{}] {}::{} (rows=2^{}, exprs={}, constraints={})",
                gi,
                ai,
                gname,
                aname,
                air.num_rows.unwrap_or(0),
                air.expressions.len(),
                air.constraints.len(),
            );
        }
    }
}

struct AirHit<'a> {
    airgroup_idx: usize,
    air_idx: usize,
    airgroup_name: String,
    air: &'a Air,
}

fn find_air<'a>(pilout: &'a PilOut, needle: &str) -> Result<AirHit<'a>> {
    let mut matches: Vec<AirHit<'a>> = Vec::new();
    for (gi, group) in pilout.air_groups.iter().enumerate() {
        for (ai, air) in group.airs.iter().enumerate() {
            let name = air.name.as_deref().unwrap_or("");
            if name.contains(needle) {
                matches.push(AirHit {
                    airgroup_idx: gi,
                    air_idx: ai,
                    airgroup_name: group.name.clone().unwrap_or_default(),
                    air,
                });
            }
        }
    }
    match matches.len() {
        0 => Err(anyhow!(
            "no AIR matches '{needle}'. Run with --list to see available AIRs."
        )),
        1 => Ok(matches.into_iter().next().unwrap()),
        n => {
            let names: Vec<String> = matches
                .iter()
                .map(|h| format!("{}::{}", h.airgroup_name, h.air.name.clone().unwrap_or_default()))
                .collect();
            Err(anyhow!(
                "{} AIRs match '{}' ({}); refine the needle.",
                n,
                needle,
                names.join(", ")
            ))
        }
    }
}

/// Map stage-relative witness column indices to their declared names. Walks the
/// pilout symbol table and keeps only `WITNESS_COL` symbols bound to this AIR.
fn witness_column_names(pilout: &PilOut, hit: &AirHit<'_>) -> HashMap<(u32, u32), String> {
    let mut m = HashMap::new();
    for sym in &pilout.symbols {
        let ty = SymbolType::try_from(sym.r#type).unwrap_or(SymbolType::WitnessCol);
        if ty != SymbolType::WitnessCol {
            continue;
        }
        if sym.air_group_id != Some(hit.airgroup_idx as u32) {
            continue;
        }
        if sym.air_id != Some(hit.air_idx as u32) {
            continue;
        }
        let stage = sym.stage.unwrap_or(1);
        if sym.dim == 0 {
            m.insert((stage, sym.id), sym.name.clone());
        } else {
            // Array symbol: lengths[...] gives per-dimension sizes and `id` is
            // the base column index. Flatten across all indices.
            let total: u32 = sym.lengths.iter().product();
            for k in 0..total {
                m.insert((stage, sym.id + k), format!("{}[{}]", sym.name, k));
            }
        }
    }
    m
}

struct RenderOpts {
    skip_unsupported: bool,
    only: Option<std::collections::BTreeSet<usize>>,
}

fn render_air(pilout: &PilOut, hit: AirHit<'_>, opts: &RenderOpts) -> Result<String> {
    let name = hit
        .air
        .name
        .clone()
        .ok_or_else(|| anyhow!("air has no name"))?;
    let sanitized = sanitize(&name);
    let col_names = witness_column_names(pilout, &hit);

    let mut out = String::new();
    out.push_str("import Mathlib\n\n");
    out.push_str("import LeanZKCircuit.OpenVM.Circuit\n\n");
    out.push_str("set_option linter.all false\n\n");
    out.push_str(&format!(
        "register_simp_attr {}_air_simplification\n",
        sanitized
    ));
    out.push_str(&format!(
        "register_simp_attr {}_constraint_and_interaction_simplification\n\n",
        sanitized
    ));
    out.push_str(&format!("namespace {}.extraction\n\n", sanitized));
    out.push_str(&format!(
        "-- airgroup: {} (id {})  air: {} (id {})\n",
        hit.airgroup_name, hit.airgroup_idx, name, hit.air_idx,
    ));
    if !col_names.is_empty() {
        out.push_str("-- witness column names:\n");
        let mut entries: Vec<_> = col_names.iter().collect();
        entries.sort_by_key(|((stage, id), _)| (*stage, *id));
        for ((stage, id), nm) in entries {
            out.push_str(&format!("--   stage {} col {}: {}\n", stage, id, nm));
        }
        out.push('\n');
    }

    for (i, c) in hit.air.constraints.iter().enumerate() {
        if let Some(only) = &opts.only {
            if !only.contains(&i) {
                continue;
            }
        }
        match render_constraint(&mut out, pilout, hit.air, i, c) {
            Ok(()) => {}
            Err(e) if opts.skip_unsupported && opts.only.is_none() => {
                tracing::warn!(
                    constraint = i,
                    error = %e,
                    "skipped constraint (unsupported); emitting stub"
                );
                out.push_str(&format!(
                    "  -- constraint_{} skipped: {}\n\n",
                    i,
                    e.to_string().replace('\n', " ")
                ));
            }
            Err(e) => return Err(e.context(format!("constraint #{}", i))),
        }
    }

    out.push_str(&format!("end {}.extraction\n", sanitized));
    Ok(out)
}

fn render_constraint(
    out: &mut String,
    pilout: &PilOut,
    air: &Air,
    idx: usize,
    c: &Constraint,
) -> Result<()> {
    let kind = c
        .constraint
        .as_ref()
        .ok_or_else(|| anyhow!("constraint #{} is empty", idx))?;
    let (expr_idx, debug_line) = match kind {
        ConstraintKind::EveryRow(er) => (er.expression_idx.as_ref(), er.debug_line.clone()),
        ConstraintKind::FirstRow(fr) => (fr.expression_idx.as_ref(), fr.debug_line.clone()),
        ConstraintKind::LastRow(lr) => (lr.expression_idx.as_ref(), lr.debug_line.clone()),
        ConstraintKind::EveryFrame(ef) => (ef.expression_idx.as_ref(), ef.debug_line.clone()),
    };
    let expr_idx = expr_idx
        .ok_or_else(|| anyhow!("constraint #{} has no expression_idx", idx))?
        .idx as usize;

    let rendered = render_expr_by_idx(pilout, air, expr_idx)?;
    out.push_str("  @[simp]\n");
    out.push_str(&format!(
        "  def constraint_{} {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=\n",
        idx
    ));
    if let Some(line) = debug_line.as_deref().filter(|s| !s.is_empty()) {
        out.push_str(&format!("    -- {}\n", line));
    }
    out.push_str(&format!("    ({}) = 0\n\n", rendered));
    Ok(())
}

fn render_expr_by_idx(pilout: &PilOut, air: &Air, idx: usize) -> Result<String> {
    let expr = air
        .expressions
        .get(idx)
        .ok_or_else(|| anyhow!("expression index {} out of range", idx))?;
    render_expr(pilout, air, expr)
}

fn render_expr(pilout: &PilOut, air: &Air, expr: &Expression) -> Result<String> {
    let op = expr
        .operation
        .as_ref()
        .ok_or_else(|| anyhow!("expression has no operation"))?;
    match op {
        ExprOp::Add(add) => {
            let l = render_operand(pilout, air, add.lhs.as_ref())?;
            let r = render_operand(pilout, air, add.rhs.as_ref())?;
            Ok(format!("({} + {})", l, r))
        }
        ExprOp::Sub(sub) => {
            let l = render_operand(pilout, air, sub.lhs.as_ref())?;
            let r = render_operand(pilout, air, sub.rhs.as_ref())?;
            Ok(format!("({} - {})", l, r))
        }
        ExprOp::Mul(mul) => {
            let l = render_operand(pilout, air, mul.lhs.as_ref())?;
            let r = render_operand(pilout, air, mul.rhs.as_ref())?;
            Ok(format!("({} * {})", l, r))
        }
        ExprOp::Neg(neg) => {
            let v = render_operand(pilout, air, neg.value.as_ref())?;
            Ok(format!("(-{})", v))
        }
    }
}

fn render_operand(pilout: &PilOut, air: &Air, operand: Option<&Operand>) -> Result<String> {
    let operand = operand.ok_or_else(|| anyhow!("operand missing"))?;
    let kind = operand
        .operand
        .as_ref()
        .ok_or_else(|| anyhow!("operand has no kind"))?;
    match kind {
        OperandKind::Constant(c) => Ok(format_basefield(&c.value)),
        OperandKind::WitnessCol(w) => Ok(format!(
            "(Circuit.main c (id := {}) (column := {}) (row := row) (rotation := {}))",
            /* airgroup-level id used by openvm-fv is the stage index here: */
            w.stage,
            w.col_idx,
            w.row_offset,
        )),
        OperandKind::Expression(e) => render_expr_by_idx(pilout, air, e.idx as usize),
        OperandKind::FixedCol(_)
        | OperandKind::PeriodicCol(_)
        | OperandKind::Challenge(_)
        | OperandKind::ProofValue(_)
        | OperandKind::AirGroupValue(_)
        | OperandKind::AirValue(_)
        | OperandKind::PublicValue(_)
        | OperandKind::CustomCol(_) => bail!(
            "operand kind {:?} not yet supported by zisk-pil-extract",
            kind
        ),
    }
}

/// Render a protobuf-encoded base-field constant (little-endian bytes) as a
/// decimal Lean literal.
fn format_basefield(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "0".to_string();
    }
    // Arbitrary-precision decimal via repeated base-256 × add. Pilout constants
    // are small enough in practice (< 64 bits) but we stay generic.
    let mut digits: Vec<u64> = vec![0];
    for &b in bytes.iter() {
        let mut carry = b as u64;
        for d in digits.iter_mut() {
            let v = *d * 256 + carry;
            *d = v % 1_000_000_000;
            carry = v / 1_000_000_000;
        }
        while carry > 0 {
            digits.push(carry % 1_000_000_000);
            carry /= 1_000_000_000;
        }
    }
    let mut s = String::new();
    let mut iter = digits.iter().rev();
    if let Some(head) = iter.next() {
        s.push_str(&head.to_string());
    }
    for d in iter {
        s.push_str(&format!("{:09}", d));
    }
    s
}

fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn format_basefield_empty() {
        assert_eq!(format_basefield(&[]), "0");
    }

    #[test]
    fn format_basefield_single_zero() {
        assert_eq!(format_basefield(&[0x00]), "0");
    }

    #[test]
    fn format_basefield_single_one() {
        assert_eq!(format_basefield(&[0x01]), "1");
    }

    #[test]
    fn format_basefield_65536_big_endian() {
        // Regression: pilout stores constants as BE; the initial LE decode
        // turned 65536 into "1" and silently produced wrong Lean.
        assert_eq!(format_basefield(&[0x01, 0x00, 0x00]), "65536");
    }

    #[test]
    fn format_basefield_2_to_32_multi_limb() {
        // 2^32 = 4_294_967_296 — exercises the u64 arithmetic (u32 would overflow).
        assert_eq!(format_basefield(&[0x01, 0x00, 0x00, 0x00, 0x00]), "4294967296");
    }

    #[test]
    fn format_basefield_u64_max() {
        // 0xFFFF_FFFF_FFFF_FFFF = 18_446_744_073_709_551_615.
        assert_eq!(format_basefield(&[0xff; 8]), "18446744073709551615");
    }

    #[test]
    fn format_basefield_crosses_chunk_boundary() {
        // 2^72 = 4_722_366_482_869_645_213_696, which is larger than any single
        // 10^9 digit — verifies multi-chunk rendering preserves leading-zero
        // padding within chunks.
        let mut bytes = vec![0x01];
        bytes.extend(std::iter::repeat(0x00).take(9));
        assert_eq!(format_basefield(&bytes), "4722366482869645213696");
    }

    #[test]
    fn sanitize_identifier_unchanged() {
        assert_eq!(sanitize("BinaryAdd"), "BinaryAdd");
    }

    #[test]
    fn sanitize_colons_to_underscore() {
        assert_eq!(sanitize("Zisk::BinaryAdd"), "Zisk__BinaryAdd");
    }

    #[test]
    fn sanitize_mixed_punctuation() {
        assert_eq!(sanitize("foo-bar.baz"), "foo_bar_baz");
    }

    #[test]
    fn sanitize_empty() {
        assert_eq!(sanitize(""), "");
    }
}
