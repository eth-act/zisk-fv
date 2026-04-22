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
    let mut exact: Vec<AirHit<'a>> = Vec::new();
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
            if name == needle {
                exact.push(AirHit {
                    airgroup_idx: gi,
                    air_idx: ai,
                    airgroup_name: group.name.clone().unwrap_or_default(),
                    air,
                });
            }
        }
    }
    // Prefer an unambiguous exact-name match over a broader substring set. This
    // lets the caller disambiguate "Arith" from "ArithEq" / "ArithEq384" by
    // passing the exact AIR name.
    if exact.len() == 1 {
        return Ok(exact.into_iter().next().unwrap());
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
                let suffix = c
                    .constraint
                    .as_ref()
                    .map(constraint_kind_suffix)
                    .unwrap_or_else(|| "unknown_kind".to_string());
                out.push_str(&format!(
                    "  -- constraint_{}_{} skipped: {}\n\n",
                    i,
                    suffix,
                    e.to_string().replace('\n', " ")
                ));
            }
            Err(e) => return Err(e.context(format!("constraint #{}", i))),
        }
    }

    out.push_str(&format!("end {}.extraction\n", sanitized));
    Ok(out)
}

/// Suffix for a `constraint_N` definition, reflecting the pilout row domain the
/// constraint applies to. `EveryRow` / `FirstRow` / `LastRow` carry no payload;
/// `EveryFrame` carries `(offsetMin, offsetMax)` so we encode both into the name
/// to keep siblings distinct when an AIR emits multiple frames.
fn constraint_kind_suffix(kind: &ConstraintKind) -> String {
    match kind {
        ConstraintKind::EveryRow(_) => "every_row".to_string(),
        ConstraintKind::FirstRow(_) => "first_row".to_string(),
        ConstraintKind::LastRow(_) => "last_row".to_string(),
        ConstraintKind::EveryFrame(ef) => {
            format!("every_frame_{}_{}", ef.offset_min, ef.offset_max)
        }
    }
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

    // Permutation/lookup constraints mix `F`-typed witness cells with
    // `ExtF`-typed challenges and exposed values. Lean cannot synthesize
    // `HMul F ExtF _` without a coercion (and openvm-fv's extractor leaves
    // these as comments rather than emitting an ill-typed `def`). We do the
    // same: detect `Challenge`/`AirValue`/`AirGroupValue` references and
    // skip-stub the constraint. The named-constraint layer (Airs/) provides
    // a hand-written replacement using `OperationBusEntry`.
    if expr_uses_extf(pilout, air, expr_idx)? {
        bail!(
            "constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry"
        );
    }

    let rendered = render_expr_by_idx(pilout, air, expr_idx)?;
    let suffix = constraint_kind_suffix(kind);
    out.push_str("  @[simp]\n");
    out.push_str(&format!(
        "  def constraint_{}_{} {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=\n",
        idx, suffix
    ));
    if let Some(line) = debug_line.as_deref().filter(|s| !s.is_empty()) {
        out.push_str(&format!("    -- {}\n", line));
    }
    out.push_str(&format!("    ({}) = 0\n\n", rendered));
    Ok(())
}

/// Walk an expression tree (via the pilout expression pool) and report
/// whether any operand is an `ExtF`-typed reference (Challenge, AirValue,
/// AirGroupValue). These cannot be mixed with witness cells in a single
/// constraint definition without explicit coercions.
fn expr_uses_extf(pilout: &PilOut, air: &Air, idx: usize) -> Result<bool> {
    let expr = air
        .expressions
        .get(idx)
        .ok_or_else(|| anyhow!("expression index {} out of range", idx))?;
    let op = expr
        .operation
        .as_ref()
        .ok_or_else(|| anyhow!("expression has no operation"))?;
    match op {
        ExprOp::Add(e) => {
            Ok(operand_uses_extf(pilout, air, e.lhs.as_ref())?
                || operand_uses_extf(pilout, air, e.rhs.as_ref())?)
        }
        ExprOp::Sub(e) => {
            Ok(operand_uses_extf(pilout, air, e.lhs.as_ref())?
                || operand_uses_extf(pilout, air, e.rhs.as_ref())?)
        }
        ExprOp::Mul(e) => {
            Ok(operand_uses_extf(pilout, air, e.lhs.as_ref())?
                || operand_uses_extf(pilout, air, e.rhs.as_ref())?)
        }
        ExprOp::Neg(e) => operand_uses_extf(pilout, air, e.value.as_ref()),
    }
}

fn operand_uses_extf(pilout: &PilOut, air: &Air, operand: Option<&Operand>) -> Result<bool> {
    let operand = operand.ok_or_else(|| anyhow!("operand missing"))?;
    let kind = operand
        .operand
        .as_ref()
        .ok_or_else(|| anyhow!("operand has no kind"))?;
    match kind {
        OperandKind::Challenge(_) | OperandKind::AirValue(_) | OperandKind::AirGroupValue(_) => {
            Ok(true)
        }
        OperandKind::Expression(e) => expr_uses_extf(pilout, air, e.idx as usize),
        _ => Ok(false),
    }
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
        OperandKind::WitnessCol(w) => {
            if w.row_offset < 0 {
                bail!(
                    "WitnessCol with negative rowOffset {} not yet supported (Circuit.main rotation is ℕ); the named-constraint layer should rebind this cell explicitly",
                    w.row_offset
                );
            }
            Ok(format!(
                "(Circuit.main c (id := {}) (column := {}) (row := row) (rotation := {}))",
                /* airgroup-level id used by openvm-fv is the stage index here: */
                w.stage,
                w.col_idx,
                w.row_offset,
            ))
        }
        OperandKind::Expression(e) => render_expr_by_idx(pilout, air, e.idx as usize),
        OperandKind::FixedCol(f) => {
            if f.row_offset < 0 {
                bail!(
                    "FixedCol with negative rowOffset {} not yet supported (Circuit.preprocessed rotation is ℕ)",
                    f.row_offset
                );
            }
            Ok(format!(
                "(Circuit.preprocessed c (column := {}) (row := row) (rotation := {}))",
                f.idx, f.row_offset,
            ))
        }
        OperandKind::Challenge(ch) => {
            let flat = flatten_challenge_index(pilout, ch.stage, ch.idx)?;
            Ok(format!("(Circuit.challenge c (index := {}))", flat))
        }
        OperandKind::AirValue(av) => Ok(format!(
            "(Circuit.exposed c (index := {}))",
            av.idx,
        )),
        // AirGroupValue is shared across the AIRs of a group (e.g. bus
        // accumulators carried between Main and BinaryAdd). LeanZKCircuit's
        // OpenVM circuit class doesn't differentiate these from AIR-local
        // exposed values, so we share the `Circuit.exposed` accessor and rely
        // on the named-constraint layer (Airs/Constraints) to pick distinct
        // identifiers. Index spaces overlap with AirValue — see
        // docs/fv/extractor-notes.md.
        OperandKind::AirGroupValue(av) => Ok(format!(
            "(Circuit.exposed c (index := {}))",
            av.idx,
        )),
        OperandKind::PeriodicCol(_)
        | OperandKind::ProofValue(_)
        | OperandKind::PublicValue(_)
        | OperandKind::CustomCol(_) => bail!(
            "operand kind {:?} not yet supported by zisk-pil-extract",
            kind
        ),
    }
}

/// Flatten a pilout `Challenge { stage, idx }` into the linear index expected by
/// `LeanZKCircuit.OpenVM.Circuit.challenge`. PIL2 numbers challenges by the
/// stage at which they become *available* (1-based: stage 1 is the first
/// witness commit), while `pilout.num_challenges[s]` lists challenges drawn
/// during stage `s+1` and made available at stage `s+2`. So a `Challenge { stage
/// = K }` references `num_challenges[K - 1]`. The flat index for the Lean
/// `Circuit.challenge` accessor lays the challenges out
/// `[available@stage1 ++ available@stage2 ++ …]`.
fn flatten_challenge_index(pilout: &PilOut, stage: u32, idx: u32) -> Result<usize> {
    if stage == 0 {
        bail!("challenge stage 0 is invalid (no challenges are available before stage 1)");
    }
    let stage_idx = (stage - 1) as usize;
    let per_stage = &pilout.num_challenges;
    if stage_idx >= per_stage.len() {
        bail!(
            "challenge references stage {} but pilout num_challenges only covers up to stage {}",
            stage,
            per_stage.len()
        );
    }
    let width = per_stage[stage_idx] as usize;
    let idx = idx as usize;
    if idx >= width {
        bail!(
            "challenge idx {} out of range for stage {} (width {})",
            idx, stage, width
        );
    }
    let base: usize = per_stage.iter().take(stage_idx).map(|w| *w as usize).sum();
    Ok(base + idx)
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

    #[test]
    fn constraint_kind_suffix_every_row() {
        let k = ConstraintKind::EveryRow(pilout::constraint::EveryRow::default());
        assert_eq!(constraint_kind_suffix(&k), "every_row");
    }

    #[test]
    fn constraint_kind_suffix_first_row() {
        let k = ConstraintKind::FirstRow(pilout::constraint::FirstRow::default());
        assert_eq!(constraint_kind_suffix(&k), "first_row");
    }

    #[test]
    fn constraint_kind_suffix_last_row() {
        let k = ConstraintKind::LastRow(pilout::constraint::LastRow::default());
        assert_eq!(constraint_kind_suffix(&k), "last_row");
    }

    #[test]
    fn constraint_kind_suffix_every_frame_encodes_bounds() {
        let ef = pilout::constraint::EveryFrame {
            expression_idx: None,
            offset_min: 2,
            offset_max: 5,
            debug_line: None,
        };
        assert_eq!(
            constraint_kind_suffix(&ConstraintKind::EveryFrame(ef)),
            "every_frame_2_5"
        );
    }

    #[test]
    fn flatten_challenge_index_single_stage() {
        // num_challenges array index `s - 1` carries the count of
        // `Challenge { stage = s }` challenges. Length 1 covers stage 1 only.
        let pilout = PilOut {
            num_challenges: vec![3],
            ..Default::default()
        };
        assert_eq!(flatten_challenge_index(&pilout, 1, 0).unwrap(), 0);
        assert_eq!(flatten_challenge_index(&pilout, 1, 2).unwrap(), 2);
    }

    #[test]
    fn flatten_challenge_index_later_stage_offsets() {
        // num_challenges = [2, 1, 4] declares 2 stage-1, 1 stage-2, 4 stage-3
        // challenges. A `Challenge { stage = 3, idx = 0 }` skips past the
        // stage-1 + stage-2 challenges (2 + 1 = 3).
        let pilout = PilOut {
            num_challenges: vec![2, 1, 4],
            ..Default::default()
        };
        assert_eq!(flatten_challenge_index(&pilout, 3, 0).unwrap(), 3);
        assert_eq!(flatten_challenge_index(&pilout, 3, 3).unwrap(), 6);
    }

    #[test]
    fn flatten_challenge_index_zisk_pilout_shape() {
        // Regression: ZisK's pilout has num_challenges = [0, 2] and
        // BinaryAdd's permutation argument references Challenge { stage: 2 }.
        // Verify the (stage 2, idx 0/1) → (flat 0/1) mapping holds.
        let pilout = PilOut {
            num_challenges: vec![0, 2],
            ..Default::default()
        };
        assert_eq!(flatten_challenge_index(&pilout, 2, 0).unwrap(), 0);
        assert_eq!(flatten_challenge_index(&pilout, 2, 1).unwrap(), 1);
    }

    #[test]
    fn flatten_challenge_index_out_of_range_errors() {
        let pilout = PilOut {
            num_challenges: vec![2],
            ..Default::default()
        };
        // Stage 0 is never legal — challenges must be drawn after at least one
        // committed stage.
        assert!(flatten_challenge_index(&pilout, 0, 0).is_err());
        // idx ≥ width.
        assert!(flatten_challenge_index(&pilout, 2, 2).is_err());
        // Stage exceeds num_challenges.len().
        assert!(flatten_challenge_index(&pilout, 3, 0).is_err());
    }

    #[test]
    fn find_air_exact_name_disambiguates_substring_sibling() {
        // Regression: ZisK's pilout declares both `Arith` and `ArithEq` —
        // pre-fix, substring matching found 3 airs ("Arith", "ArithEq",
        // "ArithEq384") and aborted. Exact name "Arith" now resolves
        // unambiguously to the Zisk::Arith AIR.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".to_string()),
                airs: vec![
                    Air { name: Some("Arith".to_string()), ..Default::default() },
                    Air { name: Some("ArithEq".to_string()), ..Default::default() },
                    Air { name: Some("ArithEq384".to_string()), ..Default::default() },
                ],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Arith").expect("exact-name Arith should resolve");
        assert_eq!(hit.air.name.as_deref(), Some("Arith"));
    }
}