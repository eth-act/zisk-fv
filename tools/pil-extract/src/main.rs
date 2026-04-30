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
    constraint::Constraint as ConstraintKind, expression::Operation as ExprOp, hint_field,
    operand::Operand as OperandKind, Air, Constraint, Expression, Hint, HintField,
    HintFieldArray, Operand, PilOut, SymbolType,
};

#[derive(Parser, Debug)]
#[command(
    name = "pil-extract",
    about = "Emit Lean4 constraint definitions for a single AIR from a ZisK pilout."
)]
struct Cli {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match). Required unless `--list` or `--airs`
    /// is passed.
    #[arg(long, default_value = "")]
    air: String,

    /// Comma-separated list of AIR names (exact match preferred, falls
    /// back to substring) for multi-AIR `--bus-emissions` mode. When
    /// supplied, `--air` is ignored. The output file contains one
    /// `bus_emission_<AIR>_<idx>` definition per matching emission, all
    /// in the same `ZiskFv.Extraction.Buses` namespace.
    #[arg(long, value_delimiter = ',')]
    airs: Vec<String>,

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

    /// Emit bus-emission specs (extracted from `gsum_debug_data` hints)
    /// instead of constraint definitions. When set, the tool walks the
    /// pilout-level hints filtered by the resolved AIR and renders each
    /// `gsum_debug_data` entry whose busid matches `--bus-id` (default
    /// 5000 = OPERATION_BUS_ID) as a Lean `BusEmissionSpec` definition.
    #[arg(long)]
    bus_emissions: bool,

    /// Bus ID filter for `--bus-emissions`. Defaults to ZisK's
    /// `OPERATION_BUS_ID = 5000` (`zisk/pil/opids.pil:2`). Set to
    /// `0` to emit every gsum_debug_data hint for the AIR.
    #[arg(long, default_value_t = 5000)]
    bus_id: u64,
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

    let rendered = if cli.bus_emissions && !cli.airs.is_empty() {
        let mut hits = Vec::with_capacity(cli.airs.len());
        for needle in &cli.airs {
            hits.push(find_air(&pilout, needle)?);
        }
        render_bus_emissions_multi(&pilout, &hits, cli.bus_id)?
    } else {
        let hit = find_air(&pilout, &cli.air)?;
        if cli.bus_emissions {
            render_bus_emissions(&pilout, &hit, cli.bus_id)?
        } else {
            let opts = RenderOpts {
                skip_unsupported: cli.skip_unsupported,
                only: if cli.only.is_empty() {
                    None
                } else {
                    Some(cli.only.iter().copied().collect())
                },
            };
            render_air(&pilout, hit, &opts)?
        }
    };

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
            // `Circuit.main` rotation is `ℕ` in LeanZKCircuit, so we cannot pass
            // a negative offset as `rotation`. PIL's `'`-prefixed cell (row -k)
            // at evaluation row `R` is definitionally the same field element as
            // the cell at row `R - k` with rotation 0. We emit the latter form.
            //
            // Soundness note for `R < k`: Lean's `ℕ` subtraction saturates at 0,
            // so `row - k` wraps to 0 when `row < k`. Every PIL constraint that
            // uses a negative rotation gates itself with `(1 - SEGMENT_L1)`
            // (a fixed column that is 1 on the first row of a segment and 0
            // elsewhere), so the misrendered cell at `row = 0` is multiplied
            // by zero and the constraint remains vacuously true. This is why
            // the named-constraint layer can reason about constraint 20 (the
            // PC handshake) without ever applying it at row 0.
            if w.row_offset > 0 {
                bail!(
                    "WitnessCol with positive rowOffset {} not yet supported (PIL typically only uses `'` postfix for row -1)",
                    w.row_offset
                );
            }
            let row_expr = if w.row_offset < 0 {
                let k = w.row_offset.unsigned_abs();
                format!("row - {}", k)
            } else {
                "row".to_string()
            };
            Ok(format!(
                "(Circuit.main c (id := {}) (column := {}) (row := {}) (rotation := 0))",
                /* airgroup-level id used by openvm-fv is the stage index here: */
                w.stage,
                w.col_idx,
                row_expr,
            ))
        }
        OperandKind::Expression(e) => render_expr_by_idx(pilout, air, e.idx as usize),
        OperandKind::FixedCol(f) => {
            // Same `row - k` rewrite as the WitnessCol arm above; see that
            // comment for the SEGMENT_L1 soundness argument.
            if f.row_offset > 0 {
                bail!(
                    "FixedCol with positive rowOffset {} not yet supported (PIL typically only uses `'` postfix for row -1)",
                    f.row_offset
                );
            }
            let row_expr = if f.row_offset < 0 {
                let k = f.row_offset.unsigned_abs();
                format!("row - {}", k)
            } else {
                "row".to_string()
            };
            Ok(format!(
                "(Circuit.preprocessed c (column := {}) (row := {}) (rotation := 0))",
                f.idx, row_expr,
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
            "operand kind {:?} not yet supported by pil-extract",
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

// ----------------------------------------------------------------------
// Bus-emission extraction
// ----------------------------------------------------------------------
//
// PIL2's `lookup_assumes` / `lookup_proves` / `permutation_assumes` /
// `permutation_proves` macros compile bus-tuple emissions into:
//   * one or more "every-row" `Constraint` entries that mix witness cells
//     with `Challenge` operands (the running-product update of the
//     permutation argument);
//   * one `gsum_debug_data` `Hint` per emission that records the tuple
//     structurally — its busid, multiplicity expression, per-slot
//     expressions, and (string-form) human-readable names.
//
// The hint is the structurally clean rendering target. We resolve each
// slot's `Expression` operand via the existing constraint renderer
// (`render_expr_by_idx`). All slots in ZisK's operation-bus emissions
// reference only witness cells and constants (no challenges), so the
// renderer types cleanly over `F`.

/// One bus emission resolved from a `gsum_debug_data` hint. The fields
/// mirror the hint payload's named slots — see the inline doc comment
/// above and `examples/probe_buses.rs` for the discovery path.
struct BusEmission {
    /// `Permutation` / `Lookup` / `Direct` / `Range Check` etc. — the PIL2
    /// PIOP family the tuple participates in. Operation-bus emissions are
    /// `Permutation` (Main↔BinaryAdd) or `Lookup` when stratified.
    name_piop: String,
    /// `1` = "proves"-side (the secondary state machine emits the tuple),
    /// `0` (often encoded as empty `Const.bytes = []`) = "assumes"-side
    /// (Main side that consumes / matches the tuple).
    type_piop: bool,
    busid: u64,
    /// Rendered Lean expression for the tuple's multiplicity (often the
    /// gating selector — e.g. `is_external_op` for Main's operation-bus).
    multiplicity: String,
    /// Per-slot rendered Lean expressions and human-readable names. Length
    /// matches the original PIL macro's tuple width — typically 8 for the
    /// operation bus (`[op, a_lo, a_hi, b_lo, b_hi, c_lo, c_hi, flag]`).
    slots: Vec<(String, String)>,
}

/// Parse a `Const` operand's bytes as a u64 (big-endian, leading-zero
/// stripped — same convention as `format_basefield`). Returns `None` if
/// the bytes don't correspond to a `Const` operand.
fn const_operand_to_u64(op: &Operand) -> Option<u64> {
    match op.operand.as_ref()? {
        OperandKind::Constant(c) => {
            let mut acc: u64 = 0;
            for &b in c.value.iter() {
                acc = acc.checked_mul(256)?.checked_add(b as u64)?;
            }
            Some(acc)
        }
        _ => None,
    }
}

fn const_to_u64(op: &Operand) -> Result<u64> {
    const_operand_to_u64(op).ok_or_else(|| anyhow!("expected a Constant operand for u64 read"))
}

/// Look up a hint's named field, asserting that exactly one matches.
fn hint_field_by_name<'a>(fields: &'a [HintField], name: &str) -> Option<&'a HintField> {
    fields.iter().find(|f| f.name.as_deref() == Some(name))
}

/// Render a hint slot's `Operand` value uniformly. `Const`s are emitted as
/// their decimal value, `Expression`s recurse via the existing constraint
/// renderer. All other operand kinds produce an error — bus tuples in
/// ZisK's pilout never reference challenges or fixed columns directly.
fn render_hint_operand(pilout: &PilOut, air: &Air, op: &Operand) -> Result<String> {
    let kind = op
        .operand
        .as_ref()
        .ok_or_else(|| anyhow!("hint operand has no kind"))?;
    match kind {
        OperandKind::Constant(c) => Ok(format_basefield(&c.value)),
        OperandKind::Expression(e) => render_expr_by_idx(pilout, air, e.idx as usize),
        _ => bail!(
            "hint operand kind {:?} not supported in bus-emission extraction",
            kind
        ),
    }
}

/// Walk a `gsum_debug_data` hint's outer field array and report whether
/// any embedded operand resolves to an `ExtF`-typed reference. Used to
/// detect `direct_global_update_*` emissions (gated by `Circuit.exposed`
/// or `Challenge` operands) that we render as inert stubs.
fn hint_uses_extf(pilout: &PilOut, air: &Air, hint: &Hint) -> Result<bool> {
    fn check_operand(pilout: &PilOut, air: &Air, op: &Operand) -> Result<bool> {
        let kind = op
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
    fn walk_fields(pilout: &PilOut, air: &Air, fields: &[HintField]) -> Result<bool> {
        for f in fields {
            let Some(v) = f.value.as_ref() else { continue };
            match v {
                hint_field::Value::Operand(op) => {
                    if check_operand(pilout, air, op)? {
                        return Ok(true);
                    }
                }
                hint_field::Value::HintFieldArray(a) => {
                    if walk_fields(pilout, air, &a.hint_fields)? {
                        return Ok(true);
                    }
                }
                _ => {}
            }
        }
        Ok(false)
    }
    walk_fields(pilout, air, &hint.hint_fields)
}

/// Convert a `gsum_debug_data` hint into a structured `BusEmission`. The
/// hint layout (8 named fields wrapped in a `HintFieldArray`) is fixed by
/// PIL2's runtime — see `pil2-proofman/.../std/permutation.pil` upstream
/// and the `probe_buses` example for the empirical schema.
fn parse_bus_emission(pilout: &PilOut, air: &Air, hint: &Hint) -> Result<BusEmission> {
    if hint.name != "gsum_debug_data" {
        bail!("expected gsum_debug_data hint, got {}", hint.name);
    }
    let outer = hint
        .hint_fields
        .first()
        .ok_or_else(|| anyhow!("hint has no fields"))?;
    let array = match outer.value.as_ref() {
        Some(hint_field::Value::HintFieldArray(a)) => &a.hint_fields,
        _ => bail!("gsum_debug_data outer field is not a HintFieldArray"),
    };

    let name_piop = match hint_field_by_name(array, "name_piop")
        .and_then(|f| f.value.as_ref())
    {
        Some(hint_field::Value::StringValue(s)) => s.clone(),
        _ => bail!("missing or non-string name_piop"),
    };
    let type_piop = match hint_field_by_name(array, "type_piop")
        .and_then(|f| f.value.as_ref())
    {
        Some(hint_field::Value::Operand(op)) => const_to_u64(op)? != 0,
        _ => bail!("missing or non-operand type_piop"),
    };
    let busid = match hint_field_by_name(array, "busid")
        .and_then(|f| f.value.as_ref())
    {
        Some(hint_field::Value::Operand(op)) => const_to_u64(op)?,
        _ => bail!("missing or non-operand busid"),
    };
    let multiplicity = match hint_field_by_name(array, "num_reps")
        .and_then(|f| f.value.as_ref())
    {
        Some(hint_field::Value::Operand(op)) => render_hint_operand(pilout, air, op)?,
        _ => bail!("missing or non-operand num_reps"),
    };

    let names_arr = match hint_field_by_name(array, "name_exprs")
        .and_then(|f| f.value.as_ref())
    {
        Some(hint_field::Value::HintFieldArray(a)) => &a.hint_fields,
        _ => bail!("missing or non-array name_exprs"),
    };
    let exprs_arr = match hint_field_by_name(array, "expressions")
        .and_then(|f| f.value.as_ref())
    {
        Some(hint_field::Value::HintFieldArray(a)) => &a.hint_fields,
        _ => bail!("missing or non-array expressions"),
    };
    if names_arr.len() != exprs_arr.len() {
        bail!(
            "name_exprs / expressions length mismatch ({} vs {})",
            names_arr.len(),
            exprs_arr.len()
        );
    }

    let mut slots = Vec::with_capacity(names_arr.len());
    for (n, e) in names_arr.iter().zip(exprs_arr.iter()) {
        let nm = match n.value.as_ref() {
            Some(hint_field::Value::StringValue(s)) => s.clone(),
            _ => bail!("name_exprs slot is not a string"),
        };
        let rendered = match e.value.as_ref() {
            Some(hint_field::Value::Operand(op)) => render_hint_operand(pilout, air, op)?,
            _ => bail!("expressions slot is not an operand"),
        };
        slots.push((nm, rendered));
    }
    Ok(BusEmission {
        name_piop,
        type_piop,
        busid,
        multiplicity,
        slots,
    })
}

/// Emit the file-level prelude (imports + namespace + `BusEmissionSlot` /
/// `BusEmissionSpec` structure declarations + extraction docstring). Used
/// by both single-AIR (`render_bus_emissions`) and multi-AIR
/// (`render_bus_emissions_multi`) paths.
fn write_bus_emissions_prelude(out: &mut String, scope_doc: &str, bus_id: u64) {
    out.push_str("import Mathlib\n\n");
    out.push_str("import LeanZKCircuit.OpenVM.Circuit\n\n");
    out.push_str("set_option linter.all false\n\n");
    out.push_str("namespace ZiskFv.Extraction.Buses\n\n");
    out.push_str(&format!(
        "/-! Bus-emission specs auto-extracted from `gsum_debug_data` hints\n\
         attached to {}. Filter: bus_id = {}.\n\
         Each `BusEmissionSpec` mirrors one PIL2 `lookup_*` / `permutation_*`\n\
         macro: `multiplicity` is the gating selector and `slots` is the\n\
         tuple, in the same order PIL2 emits it. -/\n\n",
        scope_doc, bus_id
    ));

    out.push_str("/-- One slot of a bus emission tuple. `name` is a debug\n");
    out.push_str("    string (verbatim from the PIL macro call site); `value`\n");
    out.push_str("    is the rendered Lean expression. -/\n");
    out.push_str("structure BusEmissionSlot {C : Type → Type → Type} {F ExtF : Type}\n");
    out.push_str("    [Field F] [Field ExtF] [Circuit F ExtF C] where\n");
    out.push_str("  name : String\n");
    out.push_str("  value : C F ExtF → ℕ → F\n\n");

    out.push_str("/-- One bus emission rule. `bus_id` selects the bus (e.g.\n");
    out.push_str("    `5000 = OPERATION_BUS_ID`); `is_proves = true` marks\n");
    out.push_str("    the proves-side (secondary state machine), `false` the\n");
    out.push_str("    assumes-side (the consumer, typically Main). -/\n");
    out.push_str("structure BusEmissionSpec {C : Type → Type → Type} {F ExtF : Type}\n");
    out.push_str("    [Field F] [Field ExtF] [Circuit F ExtF C] where\n");
    out.push_str("  bus_id : ℕ\n");
    out.push_str("  is_proves : Bool\n");
    out.push_str("  piop : String\n");
    out.push_str("  multiplicity : C F ExtF → ℕ → F\n");
    out.push_str("  slots : List (BusEmissionSlot (C := C) (F := F) (ExtF := ExtF))\n\n");
}

/// Walk the pilout's `gsum_debug_data` hints attached to one AIR and
/// append one `bus_emission_<AIR>_<n>` definition per matching emission to
/// `out`. Renders every emission whose busid equals `bus_id` (or all if
/// `bus_id == 0`).
fn write_bus_emissions_for_air(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    bus_id: u64,
    out: &mut String,
) -> Result<()> {
    let air_name = hit
        .air
        .name
        .clone()
        .ok_or_else(|| anyhow!("air has no name"))?;
    let sanitized = sanitize(&air_name);

    let matching: Vec<(usize, &Hint)> = pilout
        .hints
        .iter()
        .enumerate()
        .filter(|(_, h)| h.name == "gsum_debug_data")
        .filter(|(_, h)| h.air_group_id == Some(hit.airgroup_idx as u32))
        .filter(|(_, h)| h.air_id == Some(hit.air_idx as u32))
        .filter(|(_, h)| {
            if bus_id == 0 {
                return true;
            }
            // Decode the hint's busid without rendering, so we can filter
            // before any expensive walk.
            let outer = match h.hint_fields.first().and_then(|f| f.value.as_ref()) {
                Some(hint_field::Value::HintFieldArray(a)) => &a.hint_fields,
                _ => return false,
            };
            let bus_field = match hint_field_by_name(outer, "busid").and_then(|f| f.value.as_ref())
            {
                Some(hint_field::Value::Operand(op)) => op,
                _ => return false,
            };
            const_operand_to_u64(bus_field) == Some(bus_id)
        })
        .collect();

    out.push_str(&format!(
        "-- ----------------------------------------------------------------\n\
         -- AIR `{}` (group {}, air idx {})\n\
         -- ----------------------------------------------------------------\n\n",
        air_name, hit.airgroup_idx, hit.air_idx
    ));

    if matching.is_empty() {
        out.push_str(&format!(
            "-- No matching bus emissions for AIR `{}` and bus_id {}.\n\n",
            air_name, bus_id
        ));
    }

    for (n, (i, h)) in matching.iter().enumerate() {
        // Probe the hint payload for ExtF references (challenges / exposed
        // values / air-group values). Some PIL macros — notably the
        // `direct_global_update_*` emissions used for chip-init bookkeeping
        // — gate themselves with an `exposed` value, which is `ExtF`-typed.
        // We can't render those into our `BusEmissionSpec`'s `F`-typed
        // slots without coercions, so we emit a commented stub instead and
        // continue. These emissions never participate in opcode-level
        // bus-shape reasoning (they fire once per program, not per row).
        let uses_extf = hint_uses_extf(pilout, hit.air, h).unwrap_or(true);
        if uses_extf {
            // Decode just enough metadata for the SKIPPED comment without
            // calling `parse_bus_emission` (which would itself error on the
            // ExtF operands).
            let outer = h.hint_fields.first().and_then(|f| f.value.as_ref());
            let (piop_name, is_proves, busid_val) = match outer {
                Some(hint_field::Value::HintFieldArray(a)) => {
                    let piop = match hint_field_by_name(&a.hint_fields, "name_piop")
                        .and_then(|f| f.value.as_ref())
                    {
                        Some(hint_field::Value::StringValue(s)) => s.clone(),
                        _ => "?".to_string(),
                    };
                    let proves = match hint_field_by_name(&a.hint_fields, "type_piop")
                        .and_then(|f| f.value.as_ref())
                    {
                        Some(hint_field::Value::Operand(op)) => {
                            const_operand_to_u64(op).unwrap_or(0) != 0
                        }
                        _ => false,
                    };
                    let bid = match hint_field_by_name(&a.hint_fields, "busid")
                        .and_then(|f| f.value.as_ref())
                    {
                        Some(hint_field::Value::Operand(op)) => {
                            const_operand_to_u64(op).unwrap_or(0)
                        }
                        _ => 0,
                    };
                    (piop, proves, bid)
                }
                _ => ("?".to_string(), false, 0),
            };
            out.push_str(&format!(
                "-- gsum_debug_data #{} ({} {}; bus_id {})\n",
                i,
                piop_name,
                if is_proves { "proves" } else { "assumes" },
                busid_val
            ));
            out.push_str(&format!(
                "-- SKIPPED: bus_emission_{}_{} references ExtF-typed challenges /\n\
                 -- exposed values (typical for `direct_global_update_*` emissions\n\
                 -- gated by global selectors). Emit a placeholder def so callers\n\
                 -- depending on the indexed name still typecheck; the body has\n\
                 -- multiplicity 0 and an empty slot list, which is sound because\n\
                 -- this emission is irrelevant to opcode-level bus-shape proofs.\n",
                sanitized, n
            ));
            out.push_str(&format!(
                "@[simp]\ndef bus_emission_{}_{} {{C : Type → Type → Type}} {{F ExtF : Type}}\n",
                sanitized, n
            ));
            out.push_str(
                "    [Field F] [Field ExtF] [Circuit F ExtF C]\n\
                 : @BusEmissionSpec C F ExtF _ _ _ :=\n",
            );
            out.push_str(&format!("  {{ bus_id := {}\n", busid_val));
            out.push_str(&format!("    is_proves := {}\n", is_proves));
            out.push_str(&format!(
                "    piop := \"{}\"\n",
                piop_name.replace('\\', "\\\\").replace('\"', "\\\"")
            ));
            out.push_str("    multiplicity := fun _ _ => 0\n");
            out.push_str("    slots := [] }\n\n");
            continue;
        }
        let em = parse_bus_emission(pilout, hit.air, h)
            .with_context(|| format!("hint #{} (AIR {})", i, air_name))?;
        out.push_str(&format!(
            "-- gsum_debug_data #{} ({} {}; bus_id {})\n",
            i,
            em.name_piop,
            if em.type_piop { "proves" } else { "assumes" },
            em.busid
        ));
        for (nm, _) in &em.slots {
            out.push_str(&format!("--   slot: {}\n", nm));
        }
        out.push_str(&format!(
            "@[simp]\ndef bus_emission_{}_{} {{C : Type → Type → Type}} {{F ExtF : Type}}\n",
            sanitized, n
        ));
        out.push_str(
            "    [Field F] [Field ExtF] [Circuit F ExtF C]\n\
             : @BusEmissionSpec C F ExtF _ _ _ :=\n",
        );
        out.push_str(&format!("  {{ bus_id := {}\n", em.busid));
        out.push_str(&format!("    is_proves := {}\n", em.type_piop));
        out.push_str(&format!(
            "    piop := \"{}\"\n",
            em.name_piop.replace('\\', "\\\\").replace('\"', "\\\"")
        ));
        out.push_str(&format!(
            "    multiplicity := fun c row => {}\n",
            em.multiplicity
        ));
        out.push_str("    slots := [\n");
        for (idx, (nm, val)) in em.slots.iter().enumerate() {
            let comma = if idx + 1 < em.slots.len() { "," } else { "" };
            out.push_str(&format!(
                "      {{ name := \"{}\", value := fun c row => {} }}{}\n",
                nm.replace('\\', "\\\\").replace('\"', "\\\""),
                val,
                comma
            ));
        }
        out.push_str("    ] }\n\n");
    }
    Ok(())
}

/// Render every operation-bus emission attached to the given AIR as a Lean
/// file under `ZiskFv.Extraction.Buses`. Only `gsum_debug_data` hints
/// matching the requested `bus_id` are emitted.
fn render_bus_emissions(pilout: &PilOut, hit: &AirHit<'_>, bus_id: u64) -> Result<String> {
    let air_name = hit
        .air
        .name
        .clone()
        .ok_or_else(|| anyhow!("air has no name"))?;
    let scope_doc = format!(
        "AIR `{}` (group {}, air idx {})",
        air_name, hit.airgroup_idx, hit.air_idx
    );
    let mut out = String::new();
    write_bus_emissions_prelude(&mut out, &scope_doc, bus_id);
    write_bus_emissions_for_air(pilout, hit, bus_id, &mut out)?;
    out.push_str("end ZiskFv.Extraction.Buses\n");
    Ok(out)
}

/// Multi-AIR variant of `render_bus_emissions`. Emits one combined Lean
/// file under `ZiskFv.Extraction.Buses`, with one `bus_emission_<AIR>_<n>`
/// definition per matching emission across the requested AIRs. Used by
/// the Phase-6 Track-O bus-shape extraction (Main + Arith + Binary +
/// BinaryAdd cover the operation-bus emissions for RV64IM).
fn render_bus_emissions_multi(
    pilout: &PilOut,
    hits: &[AirHit<'_>],
    bus_id: u64,
) -> Result<String> {
    let names: Vec<String> = hits
        .iter()
        .map(|h| {
            h.air
                .name
                .clone()
                .unwrap_or_else(|| format!("[{},{}]", h.airgroup_idx, h.air_idx))
        })
        .collect();
    let scope_doc = format!("AIRs {{{}}}", names.join(", "));
    let mut out = String::new();
    write_bus_emissions_prelude(&mut out, &scope_doc, bus_id);
    for hit in hits {
        write_bus_emissions_for_air(pilout, hit, bus_id, &mut out)?;
    }
    out.push_str("end ZiskFv.Extraction.Buses\n");
    Ok(out)
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

    /// Build a minimal `Air` whose sole expression references a single witness
    /// cell at `(stage, col_idx, row_offset)`. Used by the negative-row-offset
    /// render tests below.
    fn single_witness_expr_air(stage: u32, col_idx: u32, row_offset: i32) -> Air {
        Air {
            expressions: vec![Expression {
                operation: Some(ExprOp::Add(pilout::expression::Add {
                    lhs: Some(Operand {
                        operand: Some(OperandKind::WitnessCol(pilout::operand::WitnessCol {
                            stage,
                            col_idx,
                            row_offset,
                        })),
                    }),
                    rhs: Some(Operand {
                        operand: Some(OperandKind::Constant(pilout::operand::Constant {
                            value: vec![0x00],
                        })),
                    }),
                })),
            }],
            ..Default::default()
        }
    }

    #[test]
    fn render_operand_witness_col_negative_offset_rewrites_to_row_sub_k() {
        // Regression (Phase 2.5 D2): PIL's `'`-postfix cell (row -1) was
        // previously a hard error. We now emit `(row := row - 1)` with
        // `rotation := 0`, which is definitionally the same cell. SEGMENT_L1
        // gating in PIL guarantees ℕ saturation at row 0 is vacuous.
        let pilout = PilOut::default();
        let air = single_witness_expr_air(1, 7, -1);
        let rendered = render_expr_by_idx(&pilout, &air, 0).expect("should render");
        assert_eq!(
            rendered,
            "((Circuit.main c (id := 1) (column := 7) (row := row - 1) (rotation := 0)) + 0)"
        );
    }

    #[test]
    fn render_operand_witness_col_row_offset_zero_unchanged() {
        // The default (non-rotated) rendering form is unchanged.
        let pilout = PilOut::default();
        let air = single_witness_expr_air(1, 7, 0);
        let rendered = render_expr_by_idx(&pilout, &air, 0).expect("should render");
        assert_eq!(
            rendered,
            "((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) + 0)"
        );
    }

    #[test]
    fn render_operand_witness_col_positive_offset_still_errors() {
        // PIL2 doesn't use positive rotations in ZisK's pilout; keep them
        // failing loudly so we don't silently misrender a future use.
        let pilout = PilOut::default();
        let air = single_witness_expr_air(1, 7, 1);
        assert!(render_expr_by_idx(&pilout, &air, 0).is_err());
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

    fn const_operand(bytes: Vec<u8>) -> Operand {
        Operand {
            operand: Some(OperandKind::Constant(pilout::operand::Constant { value: bytes })),
        }
    }

    #[test]
    fn const_operand_to_u64_decodes_big_endian() {
        // 0x1388 = 5000 — the operation-bus id.
        assert_eq!(const_operand_to_u64(&const_operand(vec![0x13, 0x88])), Some(5000));
        // Empty bytes = 0 (PIL2 strips leading zeros).
        assert_eq!(const_operand_to_u64(&const_operand(vec![])), Some(0));
        // 0x0a = 10 = OP_ADD opcode literal.
        assert_eq!(const_operand_to_u64(&const_operand(vec![0x0a])), Some(10));
    }

    #[test]
    fn const_operand_to_u64_rejects_non_constant() {
        let op = Operand {
            operand: Some(OperandKind::WitnessCol(pilout::operand::WitnessCol {
                stage: 1,
                col_idx: 0,
                row_offset: 0,
            })),
        };
        assert_eq!(const_operand_to_u64(&op), None);
    }

    /// Build the minimal `gsum_debug_data` hint shape the PIL2 runtime
    /// emits: an outer field wrapping a `HintFieldArray` of named slots
    /// (`name_piop`, `type_piop`, `busid`, `num_reps`, `name_exprs`,
    /// `expressions`, `deg_expr`, `deg_sel`).
    fn make_hint(name_piop: &str, type_piop_byte: u8, busid: u64, num_reps: Operand,
                 slots: Vec<(String, Operand)>) -> Hint {
        let busid_bytes = if busid == 0 { vec![] } else {
            let mut b = busid.to_be_bytes().to_vec();
            while b.first().copied() == Some(0) { b.remove(0); }
            b
        };
        let names_arr = HintFieldArray {
            hint_fields: slots.iter().map(|(n, _)| HintField {
                name: None,
                value: Some(hint_field::Value::StringValue(n.clone())),
            }).collect(),
        };
        let exprs_arr = HintFieldArray {
            hint_fields: slots.iter().map(|(_, op)| HintField {
                name: None,
                value: Some(hint_field::Value::Operand(op.clone())),
            }).collect(),
        };
        let outer = HintFieldArray {
            hint_fields: vec![
                HintField { name: Some("name_piop".into()),
                    value: Some(hint_field::Value::StringValue(name_piop.into())) },
                HintField { name: Some("type_piop".into()),
                    value: Some(hint_field::Value::Operand(const_operand(
                        if type_piop_byte == 0 { vec![] } else { vec![type_piop_byte] }))) },
                HintField { name: Some("busid".into()),
                    value: Some(hint_field::Value::Operand(const_operand(busid_bytes))) },
                HintField { name: Some("num_reps".into()),
                    value: Some(hint_field::Value::Operand(num_reps)) },
                HintField { name: Some("name_exprs".into()),
                    value: Some(hint_field::Value::HintFieldArray(names_arr)) },
                HintField { name: Some("expressions".into()),
                    value: Some(hint_field::Value::HintFieldArray(exprs_arr)) },
            ],
        };
        Hint {
            name: "gsum_debug_data".into(),
            hint_fields: vec![HintField {
                name: None,
                value: Some(hint_field::Value::HintFieldArray(outer)),
            }],
            air_group_id: Some(0),
            air_id: Some(0),
        }
    }

    #[test]
    fn parse_bus_emission_extracts_assumes_side_lookup() {
        let hint = make_hint(
            "Lookup",
            0, // type_piop = false (assumes)
            5000,
            const_operand(vec![1]),
            vec![
                ("op".into(), const_operand(vec![10])),
                ("a[0]".into(), const_operand(vec![0xaa])),
            ],
        );
        let pilout = PilOut::default();
        let air = Air::default();
        let em = parse_bus_emission(&pilout, &air, &hint).expect("parse should succeed");
        assert_eq!(em.name_piop, "Lookup");
        assert!(!em.type_piop);
        assert_eq!(em.busid, 5000);
        assert_eq!(em.multiplicity, "1");
        assert_eq!(em.slots.len(), 2);
        assert_eq!(em.slots[0].0, "op");
        assert_eq!(em.slots[0].1, "10");
        assert_eq!(em.slots[1].0, "a[0]");
        assert_eq!(em.slots[1].1, "170"); // 0xaa
    }

    #[test]
    fn parse_bus_emission_handles_proves_side() {
        let hint = make_hint("Permutation", 1, 5000, const_operand(vec![1]), vec![]);
        let pilout = PilOut::default();
        let air = Air::default();
        let em = parse_bus_emission(&pilout, &air, &hint).expect("parse should succeed");
        assert!(em.type_piop, "type_piop = 1 byte should decode as proves-side");
    }

    #[test]
    fn parse_bus_emission_rejects_wrong_hint_name() {
        let mut h = make_hint("Lookup", 0, 5000, const_operand(vec![1]), vec![]);
        h.name = "im_col".into();
        assert!(parse_bus_emission(&PilOut::default(), &Air::default(), &h).is_err());
    }

    // ============================================================
    // Expression / operand rendering — full coverage of ExprOp and
    // OperandKind variants. The pre-existing tests cover only Add +
    // WitnessCol/Constant; the additions below exercise Sub, Mul, Neg,
    // and the FixedCol/AirValue/AirGroupValue/Challenge/Expression
    // operand kinds the real pilout uses.
    // ============================================================

    fn witness_operand(stage: u32, col_idx: u32, row_offset: i32) -> Operand {
        Operand {
            operand: Some(OperandKind::WitnessCol(pilout::operand::WitnessCol {
                stage,
                col_idx,
                row_offset,
            })),
        }
    }

    fn fixed_col_operand(idx: u32, row_offset: i32) -> Operand {
        Operand {
            operand: Some(OperandKind::FixedCol(pilout::operand::FixedCol {
                idx,
                row_offset,
            })),
        }
    }

    fn challenge_operand(stage: u32, idx: u32) -> Operand {
        Operand {
            operand: Some(OperandKind::Challenge(pilout::operand::Challenge { stage, idx })),
        }
    }

    fn air_value_operand(idx: u32) -> Operand {
        Operand {
            operand: Some(OperandKind::AirValue(pilout::operand::AirValue { idx })),
        }
    }

    fn air_group_value_operand(idx: u32) -> Operand {
        Operand {
            operand: Some(OperandKind::AirGroupValue(pilout::operand::AirGroupValue {
                idx,
            })),
        }
    }

    fn expr_ref_operand(idx: u32) -> Operand {
        Operand {
            operand: Some(OperandKind::Expression(pilout::operand::Expression { idx })),
        }
    }

    fn add_expr(lhs: Operand, rhs: Operand) -> Expression {
        Expression {
            operation: Some(ExprOp::Add(pilout::expression::Add {
                lhs: Some(lhs),
                rhs: Some(rhs),
            })),
        }
    }

    fn sub_expr(lhs: Operand, rhs: Operand) -> Expression {
        Expression {
            operation: Some(ExprOp::Sub(pilout::expression::Sub {
                lhs: Some(lhs),
                rhs: Some(rhs),
            })),
        }
    }

    fn mul_expr(lhs: Operand, rhs: Operand) -> Expression {
        Expression {
            operation: Some(ExprOp::Mul(pilout::expression::Mul {
                lhs: Some(lhs),
                rhs: Some(rhs),
            })),
        }
    }

    fn neg_expr(value: Operand) -> Expression {
        Expression {
            operation: Some(ExprOp::Neg(pilout::expression::Neg {
                value: Some(value),
            })),
        }
    }

    fn every_row_constraint(idx: u32) -> Constraint {
        Constraint {
            constraint: Some(ConstraintKind::EveryRow(pilout::constraint::EveryRow {
                expression_idx: Some(pilout::operand::Expression { idx }),
                debug_line: None,
            })),
        }
    }

    #[test]
    fn render_expr_sub_emits_subtraction() {
        let air = Air {
            expressions: vec![sub_expr(
                witness_operand(1, 0, 0),
                witness_operand(1, 1, 0),
            )],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert_eq!(
            r,
            "((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))"
        );
    }

    #[test]
    fn render_expr_mul_emits_multiplication() {
        let air = Air {
            expressions: vec![mul_expr(
                const_operand(vec![3]),
                witness_operand(1, 7, 0),
            )],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert_eq!(
            r,
            "(3 * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))"
        );
    }

    #[test]
    fn render_expr_neg_emits_negation() {
        let air = Air {
            expressions: vec![neg_expr(witness_operand(1, 4, 0))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert_eq!(
            r,
            "(-(Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))"
        );
    }

    #[test]
    fn render_expr_nested_via_expression_pool() {
        // expr 0 = a + b, expr 1 = (expr 0) * c. Tests that an `Expression`
        // operand kind chains back into the pool and renders the referenced
        // sub-tree in place.
        let air = Air {
            expressions: vec![
                add_expr(witness_operand(1, 0, 0), witness_operand(1, 1, 0)),
                mul_expr(expr_ref_operand(0), witness_operand(1, 2, 0)),
            ],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 1).expect("render");
        assert_eq!(
            r,
            "(((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))"
        );
    }

    #[test]
    fn render_operand_fixed_col_zero_offset() {
        let air = Air {
            expressions: vec![add_expr(fixed_col_operand(3, 0), const_operand(vec![]))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert!(
            r.contains("(Circuit.preprocessed c (column := 3) (row := row) (rotation := 0))"),
            "unexpected render: {}",
            r
        );
    }

    #[test]
    fn render_operand_fixed_col_negative_offset_rewrites_row_sub_k() {
        // Same `'`-postfix → `row - k` rewrite as WitnessCol — covers the
        // SEGMENT_L1-gated soundness case for fixed columns.
        let air = Air {
            expressions: vec![add_expr(fixed_col_operand(3, -2), const_operand(vec![]))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert!(
            r.contains("(Circuit.preprocessed c (column := 3) (row := row - 2) (rotation := 0))"),
            "unexpected render: {}",
            r
        );
    }

    #[test]
    fn render_operand_fixed_col_positive_offset_errors() {
        let air = Air {
            expressions: vec![add_expr(fixed_col_operand(3, 1), const_operand(vec![]))],
            ..Default::default()
        };
        assert!(render_expr_by_idx(&PilOut::default(), &air, 0).is_err());
    }

    #[test]
    fn render_operand_air_value_emits_exposed() {
        let air = Air {
            expressions: vec![add_expr(air_value_operand(7), const_operand(vec![]))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert!(
            r.contains("(Circuit.exposed c (index := 7))"),
            "unexpected render: {}",
            r
        );
    }

    #[test]
    fn render_operand_air_group_value_shares_exposed_accessor() {
        // AirGroupValue and AirValue share `Circuit.exposed`. The named-
        // constraint layer is responsible for distinguishing them — the
        // extractor treats them identically by design.
        let av_air = Air {
            expressions: vec![add_expr(air_value_operand(11), const_operand(vec![]))],
            ..Default::default()
        };
        let agv_air = Air {
            expressions: vec![add_expr(air_group_value_operand(11), const_operand(vec![]))],
            ..Default::default()
        };
        let av = render_expr_by_idx(&PilOut::default(), &av_air, 0).unwrap();
        let agv = render_expr_by_idx(&PilOut::default(), &agv_air, 0).unwrap();
        assert_eq!(av, agv, "AirValue and AirGroupValue should render identically");
    }

    #[test]
    fn render_operand_challenge_uses_flat_index() {
        // num_challenges = [2, 3] → stage-1 challenges 0..1 (flat 0..1),
        // stage-2 challenges 0..2 (flat 2..4). Challenge { stage=2, idx=1 }
        // flattens to base 2 + 1 = 3.
        let pilout = PilOut {
            num_challenges: vec![2, 3],
            ..Default::default()
        };
        let air = Air {
            expressions: vec![add_expr(challenge_operand(2, 1), const_operand(vec![]))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&pilout, &air, 0).expect("render");
        assert!(
            r.contains("(Circuit.challenge c (index := 3))"),
            "unexpected render: {}",
            r
        );
    }

    #[test]
    fn render_operand_periodic_col_unsupported_errors() {
        let pc = Operand {
            operand: Some(OperandKind::PeriodicCol(pilout::operand::PeriodicCol {
                idx: 0,
                row_offset: 0,
            })),
        };
        let air = Air {
            expressions: vec![add_expr(pc, const_operand(vec![]))],
            ..Default::default()
        };
        // PeriodicCol/ProofValue/PublicValue/CustomCol fall through to the
        // explicit `bail!` arm. ZisK's pilout doesn't use them; if it ever
        // does, this test fails loudly so the extractor gets explicit
        // support rather than silently producing junk Lean.
        assert!(render_expr_by_idx(&PilOut::default(), &air, 0).is_err());
    }

    #[test]
    fn expr_uses_extf_pure_witness_arithmetic_is_false() {
        let air = Air {
            expressions: vec![mul_expr(
                witness_operand(1, 0, 0),
                witness_operand(1, 1, 0),
            )],
            ..Default::default()
        };
        assert!(!expr_uses_extf(&PilOut::default(), &air, 0).unwrap());
    }

    #[test]
    fn expr_uses_extf_challenge_in_subexpression_bubbles_up() {
        // expr 0 references a challenge; expr 1 wraps expr 0 inside an Add.
        // The walker must recurse into the Expression-pool reference and see
        // the Challenge — otherwise it would emit a constraint that mixes
        // F (witness) with ExtF (challenge), which Lean cannot typecheck.
        let pilout = PilOut {
            num_challenges: vec![1],
            ..Default::default()
        };
        let air = Air {
            expressions: vec![
                mul_expr(challenge_operand(1, 0), witness_operand(1, 0, 0)),
                add_expr(witness_operand(1, 1, 0), expr_ref_operand(0)),
            ],
            ..Default::default()
        };
        assert!(
            expr_uses_extf(&pilout, &air, 1).unwrap(),
            "challenge inside a referenced sub-expression should bubble up"
        );
    }

    #[test]
    fn expr_uses_extf_air_value_is_true() {
        let air = Air {
            expressions: vec![add_expr(air_value_operand(0), witness_operand(1, 0, 0))],
            ..Default::default()
        };
        assert!(expr_uses_extf(&PilOut::default(), &air, 0).unwrap());
    }

    #[test]
    fn witness_column_names_scalar_symbol_maps_stage_id_to_name() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![Air {
                    name: Some("Demo".into()),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            symbols: vec![pilout::Symbol {
                name: "carry_chain_0".to_string(),
                air_group_id: Some(0),
                air_id: Some(0),
                r#type: SymbolType::WitnessCol as i32,
                id: 5,
                stage: Some(1),
                dim: 0,
                lengths: vec![],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        let m = witness_column_names(&pilout, &hit);
        assert_eq!(m.get(&(1, 5)), Some(&"carry_chain_0".to_string()));
        assert_eq!(m.len(), 1, "scalar symbol should map exactly one cell");
    }

    #[test]
    fn witness_column_names_array_symbol_expands_indexed() {
        // dim=1, lengths=[3], base id=10 → chunk[0..2] at ids 10..12.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![Air {
                    name: Some("Demo".into()),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            symbols: vec![pilout::Symbol {
                name: "chunk".to_string(),
                air_group_id: Some(0),
                air_id: Some(0),
                r#type: SymbolType::WitnessCol as i32,
                id: 10,
                stage: Some(1),
                dim: 1,
                lengths: vec![3],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        let m = witness_column_names(&pilout, &hit);
        assert_eq!(m.get(&(1, 10)), Some(&"chunk[0]".to_string()));
        assert_eq!(m.get(&(1, 11)), Some(&"chunk[1]".to_string()));
        assert_eq!(m.get(&(1, 12)), Some(&"chunk[2]".to_string()));
        assert_eq!(m.len(), 3);
    }

    #[test]
    fn witness_column_names_skips_other_air_symbols() {
        // A symbol bound to (group 0, air 1) must not appear in the names
        // for (group 0, air 0). Caught a real issue in early development
        // where the extractor leaked sibling-AIR column names into Demo's
        // header.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![
                    Air {
                        name: Some("Demo".into()),
                        ..Default::default()
                    },
                    Air {
                        name: Some("Other".into()),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            }],
            symbols: vec![pilout::Symbol {
                name: "should_not_appear".to_string(),
                air_group_id: Some(0),
                air_id: Some(1),
                r#type: SymbolType::WitnessCol as i32,
                id: 0,
                stage: Some(1),
                dim: 0,
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        assert!(witness_column_names(&pilout, &hit).is_empty());
    }

    #[test]
    fn find_air_no_match_errors_with_helpful_message() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![Air {
                    name: Some("Foo".into()),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let err = find_air(&pilout, "Bar")
            .err()
            .expect("expected no-match error")
            .to_string();
        assert!(err.contains("no AIR matches"), "got: {}", err);
        assert!(err.contains("--list"), "should suggest --list, got: {}", err);
    }

    #[test]
    fn find_air_ambiguous_substring_no_exact_match_errors() {
        // "Mem" is a substring of two AIR names but not exactly any one.
        // Without an exact-match shortcut, the substring search returns 2
        // and aborts.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![
                    Air {
                        name: Some("MemAlign".into()),
                        ..Default::default()
                    },
                    Air {
                        name: Some("MemAlignByte".into()),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            }],
            ..Default::default()
        };
        let err = find_air(&pilout, "Mem")
            .err()
            .expect("expected ambiguity error")
            .to_string();
        assert!(err.contains("2 AIRs match"), "got: {}", err);
    }

    #[test]
    fn find_air_substring_with_no_exact_returns_unique_match() {
        // Substring with exactly one hit (and no exact) succeeds.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![Air {
                    name: Some("BinaryAdd".into()),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Add").expect("substring 'Add' should hit BinaryAdd");
        assert_eq!(hit.air.name.as_deref(), Some("BinaryAdd"));
    }

    // ============================================================
    // End-to-end render_air snapshot tests on synthetic AIRs. These
    // catch silent mistranslations that are well-typed Lean but
    // structurally wrong (a missing constraint, a reordered operand,
    // a header that doesn't match the witness layout) — a class of
    // bug that neither `lake build` nor the `--list` fingerprint
    // would catch.
    // ============================================================

    #[test]
    fn render_air_minimal_constraint_snapshot() {
        // Boolean constraint `x * (1 - x) = 0` on a single witness column.
        // expr 0 holds the `(1 - x)` sub-tree; expr 1 is the top-level
        // `x * (expr 0)`. The constraint targets expr 1.
        let air = Air {
            name: Some("Demo".into()),
            expressions: vec![
                sub_expr(const_operand(vec![1]), witness_operand(1, 0, 0)),
                mul_expr(witness_operand(1, 0, 0), expr_ref_operand(0)),
            ],
            constraints: vec![every_row_constraint(1)],
            num_rows: Some(8),
            ..Default::default()
        };
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![air],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        let opts = RenderOpts {
            skip_unsupported: false,
            only: None,
        };
        let out = render_air(&pilout, hit, &opts).expect("render");

        assert!(out.starts_with("import Mathlib\n"));
        assert!(out.contains("import LeanZKCircuit.OpenVM.Circuit"));
        assert!(out.contains("namespace Demo.extraction"));
        assert!(
            out.contains("-- airgroup: Zisk (id 0)  air: Demo (id 0)"),
            "header missing airgroup/air metadata:\n{}",
            out
        );
        assert!(out.contains("def constraint_0_every_row"));
        // The boolean shape `x * (1 - x) = 0` should appear with the witness
        // cell on both sides of the multiplication.
        assert!(
            out.matches("(column := 0)").count() >= 2,
            "expected witness column 0 to appear twice (once each side of `x * (1-x)`):\n{}",
            out
        );
        assert!(out.contains(") = 0\n"));
        assert!(out.trim_end().ends_with("end Demo.extraction"));
    }

    #[test]
    fn render_air_skip_unsupported_emits_stub_for_extf_constraint() {
        // A constraint mixing a witness cell with a Challenge is ExtF-
        // typed; without --skip-unsupported the renderer aborts. With it,
        // a comment stub replaces the def — the named-constraint layer
        // takes over for these.
        let pilout = PilOut {
            num_challenges: vec![1],
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Demo".into()),
                    expressions: vec![mul_expr(
                        witness_operand(1, 0, 0),
                        challenge_operand(1, 0),
                    )],
                    constraints: vec![every_row_constraint(0)],
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };

        // First confirm the strict path aborts:
        {
            let hit = find_air(&pilout, "Demo").unwrap();
            let strict = RenderOpts {
                skip_unsupported: false,
                only: None,
            };
            assert!(render_air(&pilout, hit, &strict).is_err());
        }

        // Then confirm the lenient path emits a stub instead:
        let hit = find_air(&pilout, "Demo").unwrap();
        let lenient = RenderOpts {
            skip_unsupported: true,
            only: None,
        };
        let out = render_air(&pilout, hit, &lenient).expect("should not abort under skip");
        assert!(
            out.contains("constraint_0_every_row skipped:"),
            "expected skip stub for ExtF constraint, got:\n{}",
            out
        );
        assert!(
            !out.contains("def constraint_0_every_row"),
            "skipped constraint should not emit a def"
        );
    }

    #[test]
    fn render_air_only_filter_drops_excluded_constraints() {
        // --only [0] keeps constraint 0 and silently drops constraint 1.
        let air = Air {
            name: Some("Demo".into()),
            expressions: vec![
                add_expr(witness_operand(1, 0, 0), const_operand(vec![])),
                add_expr(witness_operand(1, 1, 0), const_operand(vec![])),
            ],
            constraints: vec![every_row_constraint(0), every_row_constraint(1)],
            ..Default::default()
        };
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![air],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        let opts = RenderOpts {
            skip_unsupported: false,
            only: Some(std::collections::BTreeSet::from([0])),
        };
        let out = render_air(&pilout, hit, &opts).expect("render");
        assert!(out.contains("def constraint_0_every_row"));
        assert!(
            !out.contains("def constraint_1_every_row"),
            "constraint 1 should be filtered by --only [0], got:\n{}",
            out
        );
    }

    #[test]
    fn render_air_includes_witness_column_name_header() {
        // When pilout symbols name the witness columns, render_air emits a
        // sorted `-- stage S col C: name` block. The named-constraint
        // layer reads these to bind human-readable accessors.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Demo".into()),
                    expressions: vec![add_expr(witness_operand(1, 0, 0), const_operand(vec![]))],
                    constraints: vec![every_row_constraint(0)],
                    ..Default::default()
                }],
                ..Default::default()
            }],
            symbols: vec![pilout::Symbol {
                name: "x".to_string(),
                air_group_id: Some(0),
                air_id: Some(0),
                r#type: SymbolType::WitnessCol as i32,
                id: 0,
                stage: Some(1),
                dim: 0,
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        let opts = RenderOpts {
            skip_unsupported: false,
            only: None,
        };
        let out = render_air(&pilout, hit, &opts).expect("render");
        assert!(
            out.contains("-- witness column names:")
                && out.contains("--   stage 1 col 0: x"),
            "header missing column-name block:\n{}",
            out
        );
    }

    #[test]
    fn render_air_sanitizes_air_name_for_namespace() {
        // PIL2 lets AIR names contain `::` and other punctuation. The
        // sanitizer maps them to `_` so the output is a valid Lean
        // namespace + register_simp_attr identifier.
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Foo::Bar".into()),
                    expressions: vec![add_expr(witness_operand(1, 0, 0), const_operand(vec![]))],
                    constraints: vec![every_row_constraint(0)],
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Foo::Bar").unwrap();
        let opts = RenderOpts {
            skip_unsupported: false,
            only: None,
        };
        let out = render_air(&pilout, hit, &opts).expect("render");
        assert!(out.contains("namespace Foo__Bar.extraction"));
        assert!(out.contains("register_simp_attr Foo__Bar_air_simplification"));
        // The original name still appears verbatim in the metadata comment.
        assert!(out.contains("air: Foo::Bar"));
    }

    // ============================================================
    // format_basefield property check: cross-validate against u128
    // for byte vectors fitting in 16 bytes (u128 covers the entire
    // domain of any single Goldilocks limb plus headroom). Hand-
    // picked critical patterns plus 200 LCG-deterministic random
    // vectors. Extends the original 7 hand-coded cases.
    // ============================================================

    #[test]
    fn format_basefield_matches_u128_decimal_for_bytes_up_to_16() {
        fn check(bytes: &[u8]) {
            assert!(bytes.len() <= 16);
            let mut padded = [0u8; 16];
            padded[16 - bytes.len()..].copy_from_slice(bytes);
            let n = u128::from_be_bytes(padded);
            let got = format_basefield(bytes);
            assert_eq!(
                got,
                n.to_string(),
                "format_basefield({:?}) = {:?}; u128 BE decode = {}",
                bytes,
                got,
                n
            );
        }

        let critical: &[&[u8]] = &[
            &[],
            &[0],
            &[0, 0, 0],
            &[1],
            &[0xFF],
            &[0xFF, 0xFF],
            &[1, 0, 0, 0],
            &[1, 0, 0, 0, 0],
            &[1, 0, 0, 0, 0, 0, 0, 0],
            &[0xFF; 8],
            &[1, 0, 0, 0, 0, 0, 0, 0, 0],
            &[0xFF; 16],
            &[0, 0, 1, 2, 3, 4, 5, 6, 7],
            &[0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0],
        ];
        for b in critical {
            check(b);
        }

        // Deterministic LCG (no `rand` dep). Constants from Knuth's MMIX.
        let mut state: u64 = 0xdead_beef_cafe_f00d;
        let mut next = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state
        };
        for _ in 0..200 {
            let len = (next() >> 56) as usize % 17; // 0..=16
            let mut bytes = vec![0u8; len];
            for b in &mut bytes {
                *b = (next() >> 56) as u8;
            }
            check(&bytes);
        }
    }
}