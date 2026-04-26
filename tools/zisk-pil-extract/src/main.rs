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

    /// Emit bus-emission specs (extracted from `gsum_debug_data` hints)
    /// instead of constraint definitions. When set, the tool walks the
    /// pilout-level hints filtered by the resolved AIR and renders each
    /// `gsum_debug_data` entry whose busid matches `--bus-id` (default
    /// 5000 = OPERATION_BUS_ID) as a Lean `BusEmissionSpec` definition.
    #[arg(long)]
    bus_emissions: bool,

    /// Bus ID filter for `--bus-emissions`. Defaults to ZisK's
    /// `OPERATION_BUS_ID = 5000` (`vendor/zisk/pil/opids.pil:2`). Set to
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

    let hit = find_air(&pilout, &cli.air)?;
    let rendered = if cli.bus_emissions {
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

/// Render every operation-bus emission attached to the given AIR as a Lean
/// file under `ZiskFv.Extraction.Buses`. Only `gsum_debug_data` hints
/// matching the requested `bus_id` are emitted.
fn render_bus_emissions(pilout: &PilOut, hit: &AirHit<'_>, bus_id: u64) -> Result<String> {
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

    let mut out = String::new();
    out.push_str("import Mathlib\n\n");
    out.push_str("import LeanZKCircuit.OpenVM.Circuit\n\n");
    out.push_str("set_option linter.all false\n\n");
    out.push_str("namespace ZiskFv.Extraction.Buses\n\n");
    out.push_str(&format!(
        "/-! Bus-emission specs auto-extracted from `gsum_debug_data` hints\n\
         attached to AIR `{}` (group {}, air idx {}). Filter: bus_id = {}.\n\
         Each `BusEmissionSpec` mirrors one PIL2 `lookup_*` / `permutation_*`\n\
         macro: `multiplicity` is the gating selector and `slots` is the\n\
         tuple, in the same order PIL2 emits it. -/\n\n",
        air_name, hit.airgroup_idx, hit.air_idx, bus_id
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

    if matching.is_empty() {
        out.push_str(&format!(
            "-- No matching bus emissions for AIR `{}` and bus_id {}.\n\n",
            air_name, bus_id
        ));
    }

    for (n, (i, h)) in matching.iter().enumerate() {
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
        out.push_str(&format!("    piop := \"{}\"\n", em.name_piop.replace('\\', "\\\\").replace('\"', "\\\"")));
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
}