use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, Parser, Subcommand};
use prost::Message;

mod arith_table;
mod clean_component;

pub mod pilout {
    include!(concat!(env!("OUT_DIR"), "/pilout.rs"));
}

use pilout::{
    constraint::Constraint as ConstraintKind, expression::Operation as ExprOp, hint_field,
    operand::Operand as OperandKind, Air, Constraint, Expression, Hint, HintField, Operand, PilOut,
    SymbolType,
};

#[derive(Parser, Debug)]
#[command(
    name = "pil-extract",
    about = "Emit Lean4 definitions extracted from upstream ZisK artifacts."
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Emit the small circuit typeclass shim used by generated extraction files.
    CircuitShim(CircuitShimCmd),
    /// Emit Lean4 constraint definitions for a single AIR (or list AIRs).
    Air(AirCmd),
    /// Emit bus-emission specs extracted from `gsum_debug_data` hints.
    BusEmissions(BusEmissionsCmd),
    /// Parse `arith_table_data.rs` and emit `Extraction.ArithTable`.
    ArithTable(ArithTableCmd),
    /// Emit the Clean `Air.Flat.Component` source for one AIR — the `Row`
    /// `ProvableStruct` and the `main` do-block (assertZero constraints +
    /// the operation-bus `OpBusChannel.push`). Plan step C0g / D-EXT.
    CleanComponent(CleanComponentCmd),
    /// Emit an audit report for the Mem AIR facts needed by
    /// `MemTableGeneratedAirFacts`.
    MemAirFacts(MemAirFactsCmd),
    /// Emit the typed Lean wrapper for the Mem generated-artifact contract.
    MemGeneratedArtifact(MemGeneratedArtifactCmd),
    /// Emit the generated bridge from `Extraction.Mem` to ProverData-backed
    /// Mem generated-artifact sources.
    MemGeneratedConstraintBridge(MemGeneratedConstraintBridgeCmd),
}

#[derive(Args, Debug)]
struct CircuitShimCmd {
    /// Output path for the generated Lean module. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct AirCmd {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match). Required unless `--list` is passed.
    #[arg(long, default_value = "")]
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

#[derive(Args, Debug)]
struct BusEmissionsCmd {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match). Required unless `--airs` is passed.
    #[arg(long, default_value = "")]
    air: String,

    /// Comma-separated list of AIR names (exact match preferred, falls
    /// back to substring). When supplied, `--air` is ignored. The output
    /// file contains one `bus_emission_<AIR>_<idx>` definition per
    /// matching emission, all in a single `Extraction.<Module>` namespace
    /// (the namespace is derived from the output file's basename).
    #[arg(long, value_delimiter = ',')]
    airs: Vec<String>,

    /// Output path for the generated .lean file. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,

    /// Bus ID filter. Defaults to ZisK's `OPERATION_BUS_ID = 5000`
    /// (`zisk/pil/opids.pil:2`). Set to `0` to emit every
    /// `gsum_debug_data` hint for the AIR.
    #[arg(long, default_value_t = 5000)]
    bus_id: u64,
}

#[derive(Args, Debug)]
struct ArithTableCmd {
    /// Path to upstream `state-machines/arith/src/arith_table_data.rs`.
    #[arg(long)]
    rust_source: PathBuf,

    /// Output path for the generated .lean file. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct CleanComponentCmd {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match; exact-name preferred).
    #[arg(long)]
    air: String,

    /// Output path for the generated `Row.lean`. If omitted (along with
    /// `--constraints-output`), both files are printed to stdout with a
    /// separator banner.
    #[arg(long)]
    row_output: Option<PathBuf>,

    /// Output path for the generated `Constraints.lean`.
    #[arg(long)]
    constraints_output: Option<PathBuf>,

    /// Operation-bus id whose proves-side `gsum_debug_data` hint supplies
    /// the `OpBusChannel.push` tuple. Defaults to ZisK's
    /// `OPERATION_BUS_ID = 5000` (`zisk/pil/opids.pil:2`).
    #[arg(long, default_value_t = 5000)]
    bus_id: u64,

    /// Channel shape for the proves-side `push`. `op-bus` (default) is
    /// the 11-slot `OpBusChannel` (BinaryAdd-family providers, C0g).
    /// `mem-align-bus` is accepted for compatibility and emits the unified
    /// 6-slot `MemBusChannel` for memory-bus providers (`bus_id = 10`) —
    /// `[mem_op, ptr, timestamp, width, value_0, value_1]`.
    #[arg(long, default_value = "op-bus")]
    channel: String,
}

#[derive(Args, Debug)]
struct MemAirFactsCmd {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match; exact-name preferred).
    #[arg(long, default_value = "Mem")]
    air: String,

    /// Optional path to `state-machines/mem/pil/mem.pil`. Pilout symbols do
    /// not carry `bits(N)` declarations, so this source file is the current
    /// authority for bit-width/range provenance.
    #[arg(long)]
    pil_source: Option<PathBuf>,

    /// Output path for the Markdown report. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct MemGeneratedArtifactCmd {
    /// Path to the .pilout file.
    #[arg(long)]
    pilout: PathBuf,

    /// AIR name (substring match; exact-name preferred).
    #[arg(long, default_value = "Mem")]
    air: String,

    /// Output path for the generated Lean module. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Args, Debug)]
struct MemGeneratedConstraintBridgeCmd {
    /// Output path for the generated Lean module. If omitted, prints to stdout.
    #[arg(long)]
    output: Option<PathBuf>,
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

    match cli.cmd {
        Cmd::ArithTable(args) => {
            let rendered = arith_table::run(&args.rust_source, args.output.as_deref())?;
            if args.output.is_none() {
                print!("{}", rendered);
            }
            Ok(())
        }
        Cmd::CircuitShim(args) => run_circuit_shim(args),
        Cmd::Air(args) => run_air(args),
        Cmd::BusEmissions(args) => run_bus_emissions(args),
        Cmd::CleanComponent(args) => run_clean_component(args),
        Cmd::MemAirFacts(args) => run_mem_air_facts(args),
        Cmd::MemGeneratedArtifact(args) => run_mem_generated_artifact(args),
        Cmd::MemGeneratedConstraintBridge(args) => run_mem_generated_constraint_bridge(args),
    }
}

/// Emit the generated-only circuit interface consumed by old per-AIR
/// extraction files.
fn run_circuit_shim(args: CircuitShimCmd) -> Result<()> {
    let rendered = render_extraction_circuit_module();
    write_output(args.output.as_deref(), &rendered)
}

/// Emit the extractor-facing source report for the Lean
/// `MemTableGeneratedAirFacts` package.
fn run_mem_air_facts(args: MemAirFactsCmd) -> Result<()> {
    let bytes = fs::read(&args.pilout)
        .with_context(|| format!("failed to read pilout {}", args.pilout.display()))?;
    let pilout = PilOut::decode(bytes.as_slice()).context("failed to decode pilout protobuf")?;
    let hit = find_air(&pilout, &args.air)?;
    let rendered = render_mem_air_facts_report(&pilout, &hit, args.pil_source.as_deref())?;
    write_output(args.output.as_deref(), &rendered)
}

/// Emit the typed Lean wrapper for the Mem generated-artifact contract.
fn run_mem_generated_artifact(args: MemGeneratedArtifactCmd) -> Result<()> {
    let bytes = fs::read(&args.pilout)
        .with_context(|| format!("failed to read pilout {}", args.pilout.display()))?;
    let pilout = PilOut::decode(bytes.as_slice()).context("failed to decode pilout protobuf")?;
    let hit = find_air(&pilout, &args.air)?;
    let rendered = render_mem_generated_artifact_module(&hit)?;
    write_output(args.output.as_deref(), &rendered)
}

fn run_mem_generated_constraint_bridge(args: MemGeneratedConstraintBridgeCmd) -> Result<()> {
    let rendered = render_mem_generated_constraint_bridge_module();
    write_output(args.output.as_deref(), &rendered)
}

/// Emit the Clean `Air.Flat.Component` source for one AIR (plan step C0g).
/// Writes `Row.lean` / `Constraints.lean` to the requested paths, or prints
/// both to stdout with a banner when no paths are given.
fn run_clean_component(args: CleanComponentCmd) -> Result<()> {
    let bytes = fs::read(&args.pilout)
        .with_context(|| format!("failed to read pilout {}", args.pilout.display()))?;
    let pilout = PilOut::decode(bytes.as_slice()).context("failed to decode pilout protobuf")?;

    let channel_kind = clean_component::ChannelKind::from_flag(&args.channel)?;
    let (row, constraints) =
        clean_component::run(&pilout, &args.air, args.bus_id, channel_kind)?;

    match (args.row_output.as_deref(), args.constraints_output.as_deref()) {
        (None, None) => {
            print!("-- ===== Row.lean =====\n{}", row);
            print!("\n-- ===== Constraints.lean =====\n{}", constraints);
        }
        _ => {
            if let Some(path) = args.row_output.as_deref() {
                write_output(Some(path), &row)?;
            }
            if let Some(path) = args.constraints_output.as_deref() {
                write_output(Some(path), &constraints)?;
            }
        }
    }
    Ok(())
}

fn run_air(args: AirCmd) -> Result<()> {
    let bytes = fs::read(&args.pilout)
        .with_context(|| format!("failed to read pilout {}", args.pilout.display()))?;
    let pilout = PilOut::decode(bytes.as_slice()).context("failed to decode pilout protobuf")?;

    if args.list {
        list_airs(&pilout);
        return Ok(());
    }

    let hit = find_air(&pilout, &args.air)?;
    let opts = RenderOpts {
        skip_unsupported: args.skip_unsupported,
        only: if args.only.is_empty() {
            None
        } else {
            Some(args.only.iter().copied().collect())
        },
    };
    let rendered = render_air(&pilout, hit, &opts)?;
    write_output(args.output.as_deref(), &rendered)
}

fn run_bus_emissions(args: BusEmissionsCmd) -> Result<()> {
    let bytes = fs::read(&args.pilout)
        .with_context(|| format!("failed to read pilout {}", args.pilout.display()))?;
    let pilout = PilOut::decode(bytes.as_slice()).context("failed to decode pilout protobuf")?;

    let module = bus_module_name_from_output(args.output.as_deref());

    let rendered = if !args.airs.is_empty() {
        let mut hits = Vec::with_capacity(args.airs.len());
        for needle in &args.airs {
            hits.push(find_air(&pilout, needle)?);
        }
        render_bus_emissions_multi(&pilout, &hits, args.bus_id, &module)?
    } else {
        let hit = find_air(&pilout, &args.air)?;
        render_bus_emissions(&pilout, &hit, args.bus_id, &module)?
    };
    write_output(args.output.as_deref(), &rendered)
}

fn write_output(output: Option<&std::path::Path>, rendered: &str) -> Result<()> {
    match output {
        Some(path) => {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).ok();
            }
            fs::write(path, rendered)
                .with_context(|| format!("failed to write {}", path.display()))?;
            tracing::info!(path = %path.display(), "wrote extraction");
        }
        None => print!("{}", rendered),
    }
    Ok(())
}

/// Derive the Lean module suffix for `Extraction.<Module>` from the output
/// path's stem. `Buses.lean` → `Buses`; `MemoryBuses.lean` → `MemoryBuses`.
/// When the output is stdout, fall back to the historical `Buses` name so
/// ad-hoc invocations still produce a valid namespace.
fn bus_module_name_from_output(output: Option<&std::path::Path>) -> String {
    output
        .and_then(|p| p.file_stem())
        .and_then(|s| s.to_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| "Buses".to_string())
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

pub(crate) struct AirHit<'a> {
    pub(crate) airgroup_idx: usize,
    pub(crate) air_idx: usize,
    pub(crate) airgroup_name: String,
    pub(crate) air: &'a Air,
}

pub(crate) fn find_air<'a>(pilout: &'a PilOut, needle: &str) -> Result<AirHit<'a>> {
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
pub(crate) fn witness_column_names(pilout: &PilOut, hit: &AirHit<'_>) -> HashMap<(u32, u32), String> {
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

fn render_extraction_circuit_module() -> String {
    r#"import Mathlib

set_option linter.all false

/-!
# Generated Extraction Circuit Shim

This module is intentionally tiny. It is the generated-only interface used by
the old per-AIR extraction files under `build/extraction/Extraction/`.
It avoids the deleted root `ZiskFv.Circuit` API and also avoids colliding with
Clean's root `Circuit` monad by living under the `Extraction` namespace.
-/

namespace Extraction

class Circuit (F ExtF : Type) (C : Type → Type → Sort u) [Field F] [Field ExtF] where
  main : C F ExtF → (id column row rotation : ℕ) → F
  preprocessed : C F ExtF → (column row rotation : ℕ) → F
  challenge : C F ExtF → (index : ℕ) → ExtF
  exposed : C F ExtF → (index : ℕ) → ExtF

end Extraction
"#
    .to_string()
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
    out.push_str("import Extraction.Circuit\n\n");
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

    // Permutation/lookup constraints mix witness cells with challenges and
    // exposed values. The general `Circuit F ExtF C` form cannot typecheck
    // those expressions without a coercion from `F` into `ExtF`, but the active
    // ZisK validators are single-field (`F = ExtF`). Emit these constraints in
    // that specialized form so the generated layer still records the PIL fact.
    let uses_extf = expr_uses_extf(pilout, air, expr_idx)?;
    let rendered = render_expr_by_idx(pilout, air, expr_idx)?;
    let suffix = constraint_kind_suffix(kind);
    out.push_str("  @[simp]\n");
    if uses_extf {
        out.push_str("  -- Mixed witness/challenge constraint emitted for single-field circuits.\n");
        out.push_str(&format!(
            "  def constraint_{}_{} {{C : Type → Type → Sort u}} {{F : Type}} [Field F] [Extraction.Circuit F F C] (c : C F F) (row: ℕ) :=\n",
            idx, suffix
        ));
    } else {
        out.push_str(&format!(
            "  def constraint_{}_{} {{C : Type → Type → Sort u}} {{F ExtF : Type}} [Field F] [Field ExtF] [Extraction.Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=\n",
            idx, suffix
        ));
    }
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
pub(crate) fn expr_uses_extf(pilout: &PilOut, air: &Air, idx: usize) -> Result<bool> {
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
            // signed offsets as `rotation`. A PIL cell at evaluation row `R`
            // with row offset `k` is rendered as the same field element at
            // row `R + k` or `R - k`, with rotation 0.
            //
            // Soundness note for `R < k`: Lean's `ℕ` subtraction saturates at 0,
            // so `row - k` wraps to 0 when `row < k`. Every PIL constraint that
            // uses a negative rotation gates itself with `(1 - SEGMENT_L1)`
            // (a fixed column that is 1 on the first row of a segment and 0
            // elsewhere), so the misrendered cell at `row = 0` is multiplied
            // by zero and the constraint remains vacuously true. This is why
            // the named-constraint layer can reason about constraint 20 (the
            // PC handshake) without ever applying it at row 0.
            let row_expr = if w.row_offset < 0 {
                let k = w.row_offset.unsigned_abs();
                format!("row - {}", k)
            } else if w.row_offset > 0 {
                format!("row + {}", w.row_offset)
            } else {
                "row".to_string()
            };
            Ok(format!(
                "(Extraction.Circuit.main c (id := {}) (column := {}) (row := {}) (rotation := 0))",
                /* airgroup-level id used by openvm-fv is the stage index here: */
                w.stage,
                w.col_idx,
                row_expr,
            ))
        }
        OperandKind::Expression(e) => render_expr_by_idx(pilout, air, e.idx as usize),
        OperandKind::FixedCol(f) => {
            // Same signed-offset rewrite as the WitnessCol arm above.
            let row_expr = if f.row_offset < 0 {
                let k = f.row_offset.unsigned_abs();
                format!("row - {}", k)
            } else if f.row_offset > 0 {
                format!("row + {}", f.row_offset)
            } else {
                "row".to_string()
            };
            Ok(format!(
                "(Extraction.Circuit.preprocessed c (column := {}) (row := {}) (rotation := 0))",
                f.idx, row_expr,
            ))
        }
        OperandKind::Challenge(ch) => {
            let flat = flatten_challenge_index(pilout, ch.stage, ch.idx)?;
            Ok(format!("(Extraction.Circuit.challenge c (index := {}))", flat))
        }
        OperandKind::AirValue(av) => Ok(format!(
            "(Extraction.Circuit.exposed c (index := {}))",
            av.idx,
        )),
        // AirGroupValue is shared across the AIRs of a group (e.g. bus
        // accumulators carried between Main and BinaryAdd). LeanZKCircuit's
        // OpenVM circuit class doesn't differentiate these from AIR-local
        // exposed values, so we share the `Circuit.exposed` accessor and rely
        // on the named-constraint layer (Airs/Constraints) to pick distinct
        // identifiers. Index spaces overlap with AirValue — see
        // docs/extraction/extractor-notes.md.
        OperandKind::AirGroupValue(av) => Ok(format!(
            "(Extraction.Circuit.exposed c (index := {}))",
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
pub(crate) fn format_basefield(bytes: &[u8]) -> String {
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

pub(crate) fn sanitize(s: &str) -> String {
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
pub(crate) fn const_operand_to_u64(op: &Operand) -> Option<u64> {
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
pub(crate) fn hint_field_by_name<'a>(fields: &'a [HintField], name: &str) -> Option<&'a HintField> {
    fields.iter().find(|f| f.name.as_deref() == Some(name))
}

/// Render a hint slot's `Operand` value uniformly. `Const`s are emitted as
/// their decimal value, `Expression`s recurse via the existing constraint
/// renderer. ExtF-typed operands (Challenge / AirValue / AirGroupValue,
/// directly or transitively under an Expression) are stubbed to `0`: the
/// `BusEmissionSpec.value` field is `F`-typed, so we can't emit an
/// `ExtF`-coerced expression there. Stubbed slots are still indexed, so
/// downstream code that references the surrounding bus emission's
/// well-typed slots (or its multiplicity) continues to work.
fn render_hint_operand(pilout: &PilOut, air: &Air, op: &Operand) -> Result<String> {
    if operand_uses_extf(pilout, air, Some(op))? {
        return Ok("0".to_string());
    }
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

/// Emit the file-level prelude (imports + namespace + `BusEmissionSlot` /
/// `BusEmissionSpec` structure declarations + extraction docstring). Used
/// by both single-AIR (`render_bus_emissions`) and multi-AIR
/// (`render_bus_emissions_multi`) paths.
fn write_bus_emissions_prelude(out: &mut String, scope_doc: &str, bus_id: u64, module: &str) {
    out.push_str("import Mathlib\n\n");
    out.push_str("import Extraction.Circuit\n");
    // The `Buses` module owns the canonical `BusEmissionSpec` /
    // `BusEmissionSlot` declarations. Secondary bus files (memory bus,
    // future per-bus projections) import them from there to avoid
    // duplicate (and definitionally-distinct) structure declarations.
    if module != "Buses" {
        out.push_str("import Extraction.Buses\n");
    }
    out.push('\n');
    out.push_str("set_option linter.all false\n\n");
    out.push_str(&format!("namespace Extraction.{}\n\n", module));
    if module != "Buses" {
        out.push_str("open Extraction.Buses\n\n");
    }
    out.push_str(&format!(
        "/-! Bus-emission specs auto-extracted from `gsum_debug_data` hints\n\
         attached to {}. Filter: bus_id = {}.\n\
         Each `BusEmissionSpec` mirrors one PIL2 `lookup_*` / `permutation_*`\n\
         macro: `multiplicity` is the gating selector and `slots` is the\n\
         tuple, in the same order PIL2 emits it. -/\n\n",
        scope_doc, bus_id
    ));

    if module == "Buses" {
        out.push_str("/-- One slot of a bus emission tuple. `name` is a debug\n");
        out.push_str("    string (verbatim from the PIL macro call site); `value`\n");
        out.push_str("    is the rendered Lean expression. -/\n");
        out.push_str("structure BusEmissionSlot {C : Type → Type → Sort u} {F ExtF : Type}\n");
        out.push_str("    [Field F] [Field ExtF] [Extraction.Circuit F ExtF C] where\n");
        out.push_str("  name : String\n");
        out.push_str("  value : C F ExtF → ℕ → F\n\n");

        out.push_str("/-- One bus emission rule. `bus_id` selects the bus (e.g.\n");
        out.push_str("    `5000 = OPERATION_BUS_ID`); `is_proves = true` marks\n");
        out.push_str("    the proves-side (secondary state machine), `false` the\n");
        out.push_str("    assumes-side (the consumer, typically Main). -/\n");
        out.push_str("structure BusEmissionSpec {C : Type → Type → Sort u} {F ExtF : Type}\n");
        out.push_str("    [Field F] [Field ExtF] [Extraction.Circuit F ExtF C] where\n");
        out.push_str("  bus_id : ℕ\n");
        out.push_str("  is_proves : Bool\n");
        out.push_str("  piop : String\n");
        out.push_str("  multiplicity : C F ExtF → ℕ → F\n");
        out.push_str("  slots : List (BusEmissionSlot (C := C) (F := F) (ExtF := ExtF))\n\n");
    }
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
        // ExtF detection is now per-slot, inside `render_hint_operand`:
        // any slot (or the multiplicity) whose operand resolves to a
        // Challenge / AirValue / AirGroupValue is rendered as the F-typed
        // literal `0` instead of an ill-typed Lean expression. This lets
        // partially-clean emissions (e.g. AIR Main's operation-bus tuple,
        // whose 9th slot `STEP * is_precompiled` references AirValue but
        // whose other 10 slots are pure witness arithmetic) emit their
        // F-clean slots verbatim while stubbing only the ExtF-tainted
        // ones. Emissions whose multiplicity itself is ExtF degrade
        // gracefully to multiplicity-0, matching the semantics of the
        // pre-V2 hint-level skip.
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
            "@[simp]\ndef bus_emission_{}_{} {{C : Type → Type → Sort u}} {{F ExtF : Type}}\n",
            sanitized, n
        ));
        out.push_str(
            "    [Field F] [Field ExtF] [Extraction.Circuit F ExtF C]\n\
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

/// Render every bus emission attached to the given AIR as a Lean file
/// under `Extraction.<module>`. Only `gsum_debug_data` hints matching the
/// requested `bus_id` are emitted.
fn render_bus_emissions(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    bus_id: u64,
    module: &str,
) -> Result<String> {
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
    write_bus_emissions_prelude(&mut out, &scope_doc, bus_id, module);
    write_bus_emissions_for_air(pilout, hit, bus_id, &mut out)?;
    out.push_str(&format!("end Extraction.{}\n", module));
    Ok(out)
}

/// Multi-AIR variant of `render_bus_emissions`. Emits one combined Lean
/// file with one `bus_emission_<AIR>_<n>` definition per matching emission
/// across the requested AIRs.
fn render_bus_emissions_multi(
    pilout: &PilOut,
    hits: &[AirHit<'_>],
    bus_id: u64,
    module: &str,
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
    write_bus_emissions_prelude(&mut out, &scope_doc, bus_id, module);
    for hit in hits {
        write_bus_emissions_for_air(pilout, hit, bus_id, &mut out)?;
    }
    out.push_str(&format!("end Extraction.{}\n", module));
    Ok(out)
}

// ----------------------------------------------------------------------
// Mem AIR fact source report
// ----------------------------------------------------------------------

/// Emit the reproducible Lean wrapper for the generated Mem artifact.
///
/// This module is intentionally a typed contract and constructor wrapper. It
/// does not manufacture `FullWitnessMemAirSourceProverDataWitnessFacts`; the
/// generated proof artifact must provide that value. Keeping this wrapper
/// generated makes the timeline-constructor signature part of the pinned
/// extraction output, beside the Markdown source manifest.
fn render_mem_generated_artifact_module(hit: &AirHit<'_>) -> Result<String> {
    let air_name = hit
        .air
        .name
        .clone()
        .ok_or_else(|| anyhow!("air has no name"))?;

    let mut out = String::new();
    writeln!(out, "import ZiskFv.AirsClean.FullEnsemble.Balance").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "set_option linter.all false").unwrap();
    writeln!(out).unwrap();
    writeln!(
        out,
        "/-!\n\
         # Mem Generated Artifact Contract\n\n\
         AUTO-GENERATED by `pil-extract mem-generated-artifact` from AIR `{}` \
         (group `{}`, group id {}, air id {}).\n\n\
         This module is the typed Lean side of `MemAirFacts.md`: generated \
         proof code supplies `WitnessFacts witness`, or raw `RawFacts witness` \
         adapted through `buildWitnessFactsFromRawFacts`, and this wrapper \
         feeds those facts to \
         `fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`.\n\
         -/",
        lean_escape(&air_name),
        lean_escape(&hit.airgroup_name),
        hit.airgroup_idx,
        hit.air_idx
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "namespace Extraction.MemGeneratedArtifact").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "open Goldilocks").unwrap();
    writeln!(out, "open Air.Flat").unwrap();
    writeln!(out, "open ZiskFv.AirsClean.ZiskInstructionRom (Program)").unwrap();
    writeln!(out, "open ZiskFv.AirsClean.FullEnsemble").unwrap();
    writeln!(out).unwrap();
    writeln!(
        out,
        "abbrev FullWitness {{length : ℕ}} (program : Program length) : Type 1 :="
    )
    .unwrap();
    writeln!(
        out,
        "  EnsembleWitness (fullRv64imEnsemble length program).ensemble"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev MemOfProverData").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(
        out,
        "    (table : Table FGL) : ZiskFv.Airs.Mem.Valid_Mem FGL FGL :="
    )
    .unwrap();
    writeln!(out, "  memOfTable table").unwrap();
    writeln!(out, "    (memSidecarGsumOfProverData witness.data)").unwrap();
    writeln!(out, "    (memSidecarIm0OfProverData witness.data)").unwrap();
    writeln!(out, "    (memSidecarIm1OfProverData witness.data)").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev SegmentOfProverData").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(
        out,
        "    (witness : FullWitness program) : ZiskFv.Airs.Mem.SegmentColumns FGL :="
    )
    .unwrap();
    writeln!(
        out,
        "  segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data)"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev PermutationOfProverData").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(
        out,
        "    (witness : FullWitness program) : ZiskFv.Airs.Mem.PermutationColumns FGL :="
    )
    .unwrap();
    writeln!(out, "  memPermutationColumnsOfProverData witness.data").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev ConstraintAssertions").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (table : Table FGL) : Type 1 :=").unwrap();
    writeln!(out, "  MemTableGeneratedConstraintAssertionFacts").unwrap();
    writeln!(out, "    table").unwrap();
    writeln!(out, "    (MemOfProverData witness table)").unwrap();
    writeln!(out, "    (SegmentOfProverData witness)").unwrap();
    writeln!(out, "    (PermutationOfProverData witness)").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev RowRangeLookups").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (table : Table FGL) : Type 1 :=").unwrap();
    writeln!(
        out,
        "  MemTableGeneratedRangeLookupFacts table (MemOfProverData witness table)"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev SegmentRangeLookups").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program) : Type 1 :=").unwrap();
    writeln!(
        out,
        "  MemSegmentGeneratedRangeLookupFacts (SegmentOfProverData witness)"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev WitnessFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program) : Type 1 :=").unwrap();
    writeln!(
        out,
        "  FullWitnessMemAirSourceProverDataWitnessFacts witness"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev RawFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program) : Type 1 :=").unwrap();
    writeln!(out, "  FullWitnessMemAirSourceProverDataFacts witness").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev RawConstraintFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (table : Table FGL) : Prop :=").unwrap();
    writeln!(out, "  MemTableGeneratedConstraintFacts").unwrap();
    writeln!(out, "    table").unwrap();
    writeln!(out, "    (MemOfProverData witness table)").unwrap();
    writeln!(out, "    (SegmentOfProverData witness)").unwrap();
    writeln!(out, "    (PermutationOfProverData witness)").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev RawRowRangeFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (table : Table FGL) : Prop :=").unwrap();
    writeln!(
        out,
        "  MemTableGeneratedRangeFacts table (MemOfProverData witness table)"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev RawSegmentRangeFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program) : Prop :=").unwrap();
    writeln!(
        out,
        "  MemSegmentGeneratedRangeFacts (SegmentOfProverData witness)"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev RawSourceFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (table : Table FGL) : Type :=").unwrap();
    writeln!(out, "  MemTableGeneratedRawSourceFacts").unwrap();
    writeln!(out, "    table").unwrap();
    writeln!(out, "    (MemOfProverData witness table)").unwrap();
    writeln!(out, "    (SegmentOfProverData witness)").unwrap();
    writeln!(out, "    (PermutationOfProverData witness)").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "@[reducible]").unwrap();
    writeln!(out, "def buildWitnessFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (constraints :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            ConstraintAssertions witness table)").unwrap();
    writeln!(out, "    (rowRanges :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RowRangeLookups witness table)").unwrap();
    writeln!(out, "    (segmentRanges :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            SegmentRangeLookups witness) :").unwrap();
    writeln!(out, "    WitnessFacts witness := by").unwrap();
    writeln!(out, "  intro table h_table h_component").unwrap();
    writeln!(out, "  exact ⟨").unwrap();
    writeln!(out, "    constraints table h_table h_component,").unwrap();
    writeln!(out, "    rowRanges table h_table h_component,").unwrap();
    writeln!(out, "    segmentRanges table h_table h_component⟩").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "@[reducible]").unwrap();
    writeln!(out, "def buildRawFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (constraints :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RawConstraintFacts witness table)").unwrap();
    writeln!(out, "    (rowRanges :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RawRowRangeFacts witness table)").unwrap();
    writeln!(out, "    (segmentRanges :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RawSegmentRangeFacts witness) :").unwrap();
    writeln!(out, "    RawFacts witness := by").unwrap();
    writeln!(out, "  intro table h_table h_component").unwrap();
    writeln!(out, "  exact {{").unwrap();
    writeln!(out, "    constraints := constraints table h_table h_component").unwrap();
    writeln!(out, "    rowRanges := rowRanges table h_table h_component").unwrap();
    writeln!(out, "    segmentRanges := segmentRanges table h_table h_component }}").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "@[reducible]").unwrap();
    writeln!(out, "def buildWitnessFactsFromRawFacts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    {{witness : FullWitness program}}").unwrap();
    writeln!(out, "    (rawFacts : RawFacts witness) :").unwrap();
    writeln!(out, "    WitnessFacts witness :=").unwrap();
    writeln!(
        out,
        "  fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts rawFacts"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "@[reducible]").unwrap();
    writeln!(out, "def buildWitnessFactsFromRawParts").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (constraints :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RawConstraintFacts witness table)").unwrap();
    writeln!(out, "    (rowRanges :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RawRowRangeFacts witness table)").unwrap();
    writeln!(out, "    (segmentRanges :").unwrap();
    writeln!(out, "      ∀ table : Table FGL,").unwrap();
    writeln!(out, "        table ∈ witness.allTables →").unwrap();
    writeln!(
        out,
        "          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →"
    )
    .unwrap();
    writeln!(out, "            RawSegmentRangeFacts witness) :").unwrap();
    writeln!(out, "    WitnessFacts witness :=").unwrap();
    writeln!(out, "  buildWitnessFactsFromRawFacts").unwrap();
    writeln!(out, "    (buildRawFacts witness constraints rowRanges segmentRanges)").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "abbrev GeneratedTimelineEvidence").unwrap();
    writeln!(
        out,
        "    (state : ZiskFv.ZiskCircuit.MemTrace.SailState)"
    )
    .unwrap();
    writeln!(
        out,
        "    (entry : Interaction.MemoryBusEntry FGL) : Type 2 :="
    )
    .unwrap();
    writeln!(out, "  FullWitnessGeneratedTimelineEvidence state entry").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "@[reducible]").unwrap();
    writeln!(out, "noncomputable def buildTimelineEvidence").unwrap();
    writeln!(out, "    {{length : ℕ}} {{program : Program length}}").unwrap();
    writeln!(out, "    (witness : FullWitness program)").unwrap();
    writeln!(out, "    (facts : WitnessFacts witness)").unwrap();
    writeln!(
        out,
        "    {{state : ZiskFv.ZiskCircuit.MemTrace.SailState}}"
    )
    .unwrap();
    writeln!(out, "    {{entry : Interaction.MemoryBusEntry FGL}}").unwrap();
    writeln!(
        out,
        "    (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)"
    )
    .unwrap();
    writeln!(
        out,
        "    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))"
    )
    .unwrap();
    writeln!(out, "    (h_traceSplit :").unwrap();
    writeln!(
        out,
        "      (fullWitnessMemAirSourceOfRawSidecars witness"
    )
    .unwrap();
    writeln!(
        out,
        "          (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts facts)).rows ="
    )
    .unwrap();
    writeln!(out, "        priorRows ++ entry :: laterRows)").unwrap();
    writeln!(out, "    (h_selectedRead :").unwrap();
    writeln!(
        out,
        "      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry ="
    )
    .unwrap();
    writeln!(
        out,
        "        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))"
    )
    .unwrap();
    writeln!(out, "    (h_initialAgreement :").unwrap();
    writeln!(
        out,
        "      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement initialState"
    )
    .unwrap();
    writeln!(
        out,
        "        (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge"
    )
    .unwrap();
    writeln!(
        out,
        "          ((fullWitnessMemAirSourceOfRawSidecars witness"
    )
    .unwrap();
    writeln!(
        out,
        "              (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts facts))"
    )
    .unwrap();
    writeln!(
        out,
        "            |>.replayBridgeOfTraceSplit h_traceSplit)).initialMemory)"
    )
    .unwrap();
    writeln!(out, "    (h_stateAtPrefix :").unwrap();
    writeln!(out, "      state =").unwrap();
    writeln!(
        out,
        "        ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows initialState priorRows) :"
    )
    .unwrap();
    writeln!(out, "    GeneratedTimelineEvidence state entry :=").unwrap();
    writeln!(
        out,
        "  fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts"
    )
    .unwrap();
    writeln!(out, "    witness").unwrap();
    writeln!(out, "    facts").unwrap();
    writeln!(out, "    initialState").unwrap();
    writeln!(out, "    priorRows").unwrap();
    writeln!(out, "    laterRows").unwrap();
    writeln!(out, "    h_traceSplit").unwrap();
    writeln!(out, "    h_selectedRead").unwrap();
    writeln!(out, "    h_initialAgreement").unwrap();
    writeln!(out, "    h_stateAtPrefix").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "end Extraction.MemGeneratedArtifact").unwrap();
    Ok(out)
}

fn render_mem_generated_constraint_bridge_module() -> String {
    r#"import Extraction.Mem
import Extraction.MemGeneratedArtifact

set_option linter.all false

/-!
# Mem Generated Constraint Bridge

AUTO-GENERATED by `pil-extract mem-generated-constraint-bridge`.

This module binds the extracted `Extraction.Mem.constraint_0..33` predicates to
the ProverData-backed Mem source used by `Extraction.MemGeneratedArtifact`.
It does not prove the constraints; generated proof code must supply the
`ExtractedConstraintFacts` fields, after which later bridge code can assemble
the raw Mem source facts consumed by the generated timeline artifact.
-/

namespace Extraction.MemGeneratedConstraintBridge

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.FullEnsemble
open Extraction.MemGeneratedArtifact

structure ProverDataMemCircuit {length : ℕ} (program : Program length) (F ExtF : Type) where
  witness : FullWitness program
  table : Table FGL

@[reducible]
def proverDataMemCircuit
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (table : Table FGL) :
    ProverDataMemCircuit program FGL FGL where
  witness := witness
  table := table

@[reducible]
def mainValue
    {length : ℕ} {program : Program length}
    (c : ProverDataMemCircuit program FGL FGL)
    (id column row rotation : ℕ) : FGL :=
  let mem := MemOfProverData c.witness c.table
  if id = 1 then
    match column with
    | 0 => mem.addr row
    | 1 => mem.step row
    | 2 => mem.sel row
    | 3 => mem.addr_changes row
    | 4 => mem.step_dual row
    | 5 => mem.sel_dual row
    | 6 => mem.value_0 row
    | 7 => mem.value_1 row
    | 8 => mem.wr row
    | 9 => mem.previous_step row
    | 10 => mem.increment_0 row
    | 11 => mem.increment_1 row
    | 12 => mem.read_same_addr row
    | _ => 0
  else if id = 2 then
    match column with
    | 0 => mem.gsum row
    | 1 => mem.im_0 row
    | 2 => mem.im_1 row
    | _ => 0
  else
    0

@[reducible]
def preprocessedValue
    {length : ℕ} {program : Program length}
    (c : ProverDataMemCircuit program FGL FGL)
    (column row rotation : ℕ) : FGL :=
  let segment := SegmentOfProverData c.witness
  let permutation := PermutationOfProverData c.witness
  match column with
  | 0 => segment.segment_l1 row
  | 1 => permutation.l1 row
  | _ => 0

@[reducible]
def challengeValue
    {length : ℕ} {program : Program length}
    (c : ProverDataMemCircuit program FGL FGL)
    (index : ℕ) : FGL :=
  let permutation := PermutationOfProverData c.witness
  match index with
  | 0 => permutation.std_alpha
  | 1 => permutation.std_gamma
  | _ => 0

@[reducible]
def exposedValue
    {length : ℕ} {program : Program length}
    (c : ProverDataMemCircuit program FGL FGL)
    (index : ℕ) : FGL :=
  let segment := SegmentOfProverData c.witness
  let permutation := PermutationOfProverData c.witness
  match index with
  | 0 => segment.segment_id
  | 1 => segment.is_first_segment
  | 2 => segment.is_last_segment
  | 3 => segment.previous_segment_value_0
  | 4 => segment.previous_segment_value_1
  | 5 => segment.previous_segment_step
  | 6 => segment.previous_segment_addr
  | 7 => segment.segment_last_value_0
  | 8 => segment.segment_last_value_1
  | 9 => segment.segment_last_step
  | 10 => segment.segment_last_addr
  | 11 => segment.distance_base_0
  | 12 => segment.distance_base_1
  | 13 => segment.distance_end_0
  | 14 => segment.distance_end_1
  | 15 => permutation.im_direct_0
  | 16 => permutation.im_direct_1
  | 17 => permutation.im_direct_2
  | 18 => permutation.im_direct_3
  | 19 => permutation.im_direct_4
  | 20 => permutation.im_direct_5
  | _ => 0

instance proverDataMemCircuitExtractionCircuit
    {length : ℕ} {program : Program length} :
    Extraction.Circuit FGL FGL (ProverDataMemCircuit program) where
  main := mainValue
  preprocessed := preprocessedValue
  challenge := challengeValue
  exposed := exposedValue

/-- Extracted Mem generated constraints `0..=33` for the ProverData-backed Mem
    circuit selected by the generated artifact wrapper. -/
structure ExtractedConstraintFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (table : Table FGL) : Prop where
  constraint_0 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_0_every_row (proverDataMemCircuit witness table) idx.val
  constraint_1 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_1_every_row (proverDataMemCircuit witness table) idx.val
  constraint_2 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_2_every_row (proverDataMemCircuit witness table) idx.val
  constraint_3 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_3_every_row (proverDataMemCircuit witness table) idx.val
  constraint_4 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_4_every_row (proverDataMemCircuit witness table) idx.val
  constraint_5 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_5_every_row (proverDataMemCircuit witness table) idx.val
  constraint_6 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_6_every_row (proverDataMemCircuit witness table) idx.val
  constraint_7 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_7_every_row (proverDataMemCircuit witness table) idx.val
  constraint_8 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_8_every_row (proverDataMemCircuit witness table) idx.val
  constraint_9 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_9_every_row (proverDataMemCircuit witness table) idx.val
  constraint_10 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_10_every_row (proverDataMemCircuit witness table) idx.val
  constraint_11 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_11_every_row (proverDataMemCircuit witness table) idx.val
  constraint_12 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_12_every_row (proverDataMemCircuit witness table) idx.val
  constraint_13 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_13_every_row (proverDataMemCircuit witness table) idx.val
  constraint_14 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_14_every_row (proverDataMemCircuit witness table) idx.val
  constraint_15 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_15_every_row (proverDataMemCircuit witness table) idx.val
  constraint_16 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_16_every_row (proverDataMemCircuit witness table) idx.val
  constraint_17 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_17_every_row (proverDataMemCircuit witness table) idx.val
  constraint_18 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_18_every_row (proverDataMemCircuit witness table) idx.val
  constraint_19 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_19_every_row (proverDataMemCircuit witness table) idx.val
  constraint_20 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_20_every_row (proverDataMemCircuit witness table) idx.val
  constraint_21 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_21_every_row (proverDataMemCircuit witness table) idx.val
  constraint_22 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_22_every_row (proverDataMemCircuit witness table) idx.val
  constraint_23 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_23_every_row (proverDataMemCircuit witness table) idx.val
  constraint_24 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_24_every_row (proverDataMemCircuit witness table) idx.val
  constraint_25 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_25_every_row (proverDataMemCircuit witness table) idx.val
  constraint_26 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_26_every_row (proverDataMemCircuit witness table) idx.val
  constraint_27 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_27_every_row (proverDataMemCircuit witness table) idx.val
  constraint_28 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_28_every_row (proverDataMemCircuit witness table) idx.val
  constraint_29 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_29_every_row (proverDataMemCircuit witness table) idx.val
  constraint_30 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_30_every_row (proverDataMemCircuit witness table) idx.val
  constraint_31 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_31_every_row (proverDataMemCircuit witness table) idx.val
  constraint_32 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_32_every_row (proverDataMemCircuit witness table) idx.val
  constraint_33 :
    ∀ idx : Fin table.table.length,
      Mem.extraction.constraint_33_every_row (proverDataMemCircuit witness table) idx.val

@[reducible]
def rawConstraintFacts_of_extractedConstraintFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : ExtractedConstraintFacts witness table) :
    RawConstraintFacts witness table where
  segmentAt := by
    intro idx
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using
      ⟨h.constraint_0 idx, h.constraint_1 idx, h.constraint_2 idx, h.constraint_3 idx,
        h.constraint_4 idx, h.constraint_5 idx, h.constraint_6 idx, h.constraint_7 idx,
        h.constraint_8 idx, h.constraint_9 idx, h.constraint_10 idx, h.constraint_11 idx,
        h.constraint_12 idx, h.constraint_13 idx, h.constraint_14 idx, h.constraint_15 idx,
        h.constraint_16 idx, h.constraint_17 idx, h.constraint_18 idx, h.constraint_19 idx,
        h.constraint_20 idx, h.constraint_21 idx, h.constraint_22 idx, h.constraint_23 idx⟩
  permutationAt := by
    intro idx
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using
      ⟨h.constraint_24 idx, h.constraint_25 idx, h.constraint_26 idx, h.constraint_27 idx,
        h.constraint_28 idx, h.constraint_29 idx, h.constraint_30 idx, h.constraint_31 idx,
        h.constraint_32 idx, h.constraint_33 idx⟩

@[reducible]
def extractedConstraintFacts_of_rawConstraintFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : RawConstraintFacts witness table) :
    ExtractedConstraintFacts witness table where
  constraint_0 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h0
  constraint_1 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h1
  constraint_2 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h2
  constraint_3 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h3
  constraint_4 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h4
  constraint_5 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h5
  constraint_6 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h6
  constraint_7 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h7
  constraint_8 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h8
  constraint_9 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h9
  constraint_10 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h10
  constraint_11 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h11
  constraint_12 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h12
  constraint_13 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h13
  constraint_14 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h14
  constraint_15 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h15
  constraint_16 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h16
  constraint_17 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h17
  constraint_18 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h18
  constraint_19 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h19
  constraint_20 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h20
  constraint_21 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h21
  constraint_22 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h22
  constraint_23 := by
    intro idx
    rcases h.segmentAt idx with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23⟩
    simpa only [ZiskFv.Airs.Mem.segment_every_row, mainValue, preprocessedValue,
      exposedValue, proverDataMemCircuit, ZiskFv.Airs.Mem.previous_row_step,
      ZiskFv.Airs.Mem.segment_previous_addr, ZiskFv.Airs.Mem.segment_previous_value_0,
      ZiskFv.Airs.Mem.segment_previous_value_1, ZiskFv.Airs.Mem.delta_step,
      ZiskFv.Airs.Mem.delta_addr] using h23
  constraint_24 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h24
  constraint_25 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h25
  constraint_26 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h26
  constraint_27 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h27
  constraint_28 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h28
  constraint_29 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h29
  constraint_30 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h30
  constraint_31 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h31
  constraint_32 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h32
  constraint_33 := by
    intro idx
    rcases h.permutationAt idx with ⟨h24, h25, h26, h27, h28, h29, h30, h31, h32, h33⟩
    simpa only [ZiskFv.Airs.Mem.permutation_every_row, mainValue, preprocessedValue,
      challengeValue, exposedValue, proverDataMemCircuit] using h33

/-- Per-table generated raw source facts: extracted Mem constraints plus the
    explicit raw range facts that are outside `Extraction.Mem.constraint_0..33`. -/
structure ExtractedRawSourceFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (table : Table FGL) : Type where
  constraints : ExtractedConstraintFacts witness table
  rowRanges : RawRowRangeFacts witness table
  segmentRanges : RawSegmentRangeFacts witness

@[reducible]
def rawSourceFacts_of_extractedRawSourceFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : ExtractedRawSourceFacts witness table) :
    RawSourceFacts witness table where
  constraints := rawConstraintFacts_of_extractedConstraintFacts h.constraints
  rowRanges := h.rowRanges
  segmentRanges := h.segmentRanges

@[reducible]
def extractedRawSourceFacts_of_rawSourceFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : RawSourceFacts witness table) :
    ExtractedRawSourceFacts witness table where
  constraints := extractedConstraintFacts_of_rawConstraintFacts h.constraints
  rowRanges := h.rowRanges
  segmentRanges := h.segmentRanges

/-- Generator-friendly range facts for the ProverData-backed Mem sidecar view.
    These are the raw bit-width/range obligations from `mem.pil`, before Lean
    repackages them as `RawRowRangeFacts` and `RawSegmentRangeFacts`. -/
structure ExtractedRangeFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (table : Table FGL) : Prop where
  increment_0 :
    ∀ idx : Fin table.table.length,
      ((MemOfProverData witness table).increment_0 idx.val).val < 2 ^ 22
  increment_1 :
    ∀ idx : Fin table.table.length,
      ((MemOfProverData witness table).increment_1 idx.val).val < 2 ^ 16
  addr :
    ∀ idx : Fin table.table.length,
      ((MemOfProverData witness table).addr idx.val).val < 2 ^ 29
  step :
    ∀ idx : Fin table.table.length,
      ((MemOfProverData witness table).step idx.val).val < 2 ^ 40
  step_dual :
    ∀ idx : Fin table.table.length,
      ((MemOfProverData witness table).step_dual idx.val).val < 2 ^ 40
  previous_step :
    ∀ idx : Fin table.table.length,
      ((MemOfProverData witness table).previous_step idx.val).val < 2 ^ 40
  dual_step_delta :
    ∀ idx : Fin table.table.length,
      (MemOfProverData witness table).sel_dual idx.val = 1 →
        ((MemOfProverData witness table).step_dual idx.val
          - (MemOfProverData witness table).step idx.val
          - (MemOfProverData witness table).wr idx.val : FGL).val < 2 ^ 24
  distance_base_0 :
    (SegmentOfProverData witness).distance_base_0.val < 2 ^ 16
  distance_base_1 :
    (SegmentOfProverData witness).distance_base_1.val < 2 ^ 16

@[reducible]
def rawRowRangeFacts_of_extractedRangeFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : ExtractedRangeFacts witness table) :
    RawRowRangeFacts witness table where
  incrementChunks := by
    intro idx
    exact ⟨h.increment_0 idx, h.increment_1 idx⟩
  addrColumns := h.addr
  stepColumns := by
    intro idx
    exact ⟨h.step idx, h.step_dual idx, h.previous_step idx⟩
  dualStepDelta := h.dual_step_delta

@[reducible]
def rawSegmentRangeFacts_of_extractedRangeFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : ExtractedRangeFacts witness table) :
    RawSegmentRangeFacts witness where
  distanceBaseChunks := ⟨h.distance_base_0, h.distance_base_1⟩

@[reducible]
def extractedRangeFacts_of_rawRangeFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (rowRanges : RawRowRangeFacts witness table)
    (segmentRanges : RawSegmentRangeFacts witness) :
    ExtractedRangeFacts witness table where
  increment_0 := by
    intro idx
    exact (rowRanges.incrementChunks idx).1
  increment_1 := by
    intro idx
    exact (rowRanges.incrementChunks idx).2
  addr := rowRanges.addrColumns
  step := by
    intro idx
    exact (rowRanges.stepColumns idx).1
  step_dual := by
    intro idx
    exact (rowRanges.stepColumns idx).2.1
  previous_step := by
    intro idx
    exact (rowRanges.stepColumns idx).2.2
  dual_step_delta := rowRanges.dualStepDelta
  distance_base_0 := segmentRanges.distanceBaseChunks.1
  distance_base_1 := segmentRanges.distanceBaseChunks.2

/-- Single generated target in source-level terms: extracted constraints plus
    explicit bit-width/range facts for the ProverData-backed Mem sidecar view. -/
structure ExtractedSidecarFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (table : Table FGL) : Type where
  constraints : ExtractedConstraintFacts witness table
  ranges : ExtractedRangeFacts witness table

@[reducible]
def extractedRawSourceFacts_of_extractedSidecarFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : ExtractedSidecarFacts witness table) :
    ExtractedRawSourceFacts witness table where
  constraints := h.constraints
  rowRanges := rawRowRangeFacts_of_extractedRangeFacts h.ranges
  segmentRanges := rawSegmentRangeFacts_of_extractedRangeFacts h.ranges

@[reducible]
def extractedSidecarFacts_of_rawSourceFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    {table : Table FGL}
    (h : RawSourceFacts witness table) :
    ExtractedSidecarFacts witness table where
  constraints := extractedConstraintFacts_of_rawConstraintFacts h.constraints
  ranges := extractedRangeFacts_of_rawRangeFacts h.rowRanges h.segmentRanges

@[reducible]
def buildRawFactsFromExtractedConstraintsAndRawRanges
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (constraints :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedConstraintFacts witness table)
    (rowRanges :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            RawRowRangeFacts witness table)
    (segmentRanges :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            RawSegmentRangeFacts witness) :
    RawFacts witness :=
  buildRawFacts
    witness
    (fun table h_table h_component =>
      rawConstraintFacts_of_extractedConstraintFacts (constraints table h_table h_component))
    rowRanges
    segmentRanges

@[reducible]
def buildWitnessFactsFromExtractedConstraintsAndRawRanges
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (constraints :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedConstraintFacts witness table)
    (rowRanges :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            RawRowRangeFacts witness table)
    (segmentRanges :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            RawSegmentRangeFacts witness) :
    WitnessFacts witness :=
  buildWitnessFactsFromRawFacts
    (buildRawFactsFromExtractedConstraintsAndRawRanges
      witness
      constraints
      rowRanges
      segmentRanges)

@[reducible]
def buildRawFactsFromExtractedRawSourceFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (facts :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedRawSourceFacts witness table) :
    RawFacts witness := by
  intro table h_table h_component
  exact rawSourceFacts_of_extractedRawSourceFacts (facts table h_table h_component)

@[reducible]
def buildWitnessFactsFromExtractedRawSourceFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (facts :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedRawSourceFacts witness table) :
    WitnessFacts witness :=
  buildWitnessFactsFromRawFacts
    (buildRawFactsFromExtractedRawSourceFacts witness facts)

@[reducible]
def buildRawFactsFromExtractedSidecarFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (facts :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedSidecarFacts witness table) :
    RawFacts witness :=
  buildRawFactsFromExtractedRawSourceFacts
    witness
    (fun table h_table h_component =>
      extractedRawSourceFacts_of_extractedSidecarFacts (facts table h_table h_component))

@[reducible]
def buildWitnessFactsFromExtractedSidecarFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (facts :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedSidecarFacts witness table) :
    WitnessFacts witness :=
  buildWitnessFactsFromRawFacts
    (buildRawFactsFromExtractedSidecarFacts witness facts)

@[reducible]
def buildExtractedSidecarFactsFromRawFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    (rawFacts : RawFacts witness) :
    ∀ table : Table FGL,
      table ∈ witness.allTables →
        table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
          ExtractedSidecarFacts witness table := by
  intro table h_table h_component
  exact extractedSidecarFacts_of_rawSourceFacts (rawFacts table h_table h_component)

@[reducible]
def buildWitnessFactsFromRawFactsViaExtractedSidecarFacts
    {length : ℕ} {program : Program length}
    {witness : FullWitness program}
    (rawFacts : RawFacts witness) :
    WitnessFacts witness :=
  buildWitnessFactsFromExtractedSidecarFacts
    witness
    (buildExtractedSidecarFactsFromRawFacts rawFacts)

@[reducible]
noncomputable def buildTimelineEvidenceFromExtractedSidecarFacts
    {length : ℕ} {program : Program length}
    (witness : FullWitness program)
    (facts :
      ∀ table : Table FGL,
        table ∈ witness.allTables →
          table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
            ExtractedSidecarFacts witness table)
    {state : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {entry : Interaction.MemoryBusEntry FGL}
    (initialState : ZiskFv.ZiskCircuit.MemTrace.SailState)
    (priorRows laterRows : List (Interaction.MemoryBusEntry FGL))
    (h_traceSplit :
      (fullWitnessMemAirSourceOfRawSidecars witness
          (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
            (buildWitnessFactsFromExtractedSidecarFacts witness facts))).rows =
        priorRows ++ entry :: laterRows)
    (h_selectedRead :
      ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow entry =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read entry))
    (h_initialAgreement :
      ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement initialState
        (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          ((fullWitnessMemAirSourceOfRawSidecars witness
              (fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
                (buildWitnessFactsFromExtractedSidecarFacts witness facts)))
            |>.replayBridgeOfTraceSplit h_traceSplit)).initialMemory)
    (h_stateAtPrefix :
      state =
        ZiskFv.ZiskCircuit.MemTrace.stateAfterMemoryBusRows initialState priorRows) :
    GeneratedTimelineEvidence state entry :=
  buildTimelineEvidence
    witness
    (buildWitnessFactsFromExtractedSidecarFacts witness facts)
    initialState
    priorRows
    laterRows
    h_traceSplit
    h_selectedRead
    h_initialAgreement
    h_stateAtPrefix

end Extraction.MemGeneratedConstraintBridge
"#
    .to_string()
}

/// Extractor-side report for the Lean `MemTableGeneratedAirFacts` package.
///
/// This intentionally emits an audit document, not Lean proof terms. The
/// current pilout carries the generated constraint expressions, fixed-column
/// values, witness-column names, and `gsum_debug_data` hints, but not the
/// original `bits(N)` declaration metadata. When `--pil-source` is supplied we
/// quote the relevant source lines so the remaining Lean source obligation is
/// anchored to a concrete extractor surface instead of a replay-soundness
/// placeholder.
fn render_mem_air_facts_report(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    pil_source: Option<&std::path::Path>,
) -> Result<String> {
    let air_name = hit
        .air
        .name
        .clone()
        .ok_or_else(|| anyhow!("air has no name"))?;
    let witness_cols = witness_column_names(pilout, hit);
    let fixed_cols = fixed_column_names(pilout, hit);
    let air_values = air_value_names(pilout, hit);
    let challenges = challenge_names(pilout);
    let range_hints = mem_air_gsum_hints(pilout, hit, Some("Range Check"))?;
    let other_hints = mem_air_gsum_hints(pilout, hit, None)?
        .into_iter()
        .filter(|(_, em)| em.name_piop != "Range Check")
        .collect::<Vec<_>>();
    let source_lines = pil_source
        .map(mem_pil_source_lines)
        .transpose()?;

    let mut out = String::new();
    writeln!(out, "# Mem AIR Facts Source Report\n").unwrap();
    writeln!(
        out,
        "- AIR: `{}` (group `{}`, group id {}, air id {})",
        md_escape(&air_name),
        md_escape(&hit.airgroup_name),
        hit.airgroup_idx,
        hit.air_idx
    )
    .unwrap();
    writeln!(
        out,
        "- Pilout `num_rows` field: `{}`",
        hit.air.num_rows.unwrap_or(0)
    )
    .unwrap();
    writeln!(out, "- Constraints: `{}`", hit.air.constraints.len()).unwrap();
    writeln!(out).unwrap();

    writeln!(out, "## Lean Package Mapping\n").unwrap();
    writeln!(
        out,
        "- `MemTableGeneratedConstraintFacts.segmentAt` is sourced from \
         `segment_every_row`; `.permutationAt` is sourced from \
         `permutation_every_row`. Lean recombines them into \
         `MemTableGeneratedAirFacts.generatedAt`."
    )
    .unwrap();
    writeln!(
        out,
        "- Expected Mem generated constraint groups: `segment_every_row` \
         constraints `0..=23`; `permutation_every_row` constraints `24..=33`."
    )
    .unwrap();
    writeln!(
        out,
        "- Generated Lean code should build `MemTableGeneratedRawSourceSidecar` \
         values for mutable Mem tables and expose them through a \
         `FullWitnessMemAirSourceRawSidecars` callback. When the sidecar \
         columns live in Clean `ProverData`, supply \
         `FullWitnessMemAirSourceProverDataWitnessFacts` for the named keys \
         below and pass it to \
         `fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`; \
         `FullWitnessGeneratedTimelineEvidence` is the checked generated \
         timeline wrapper, `fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts` \
         builds its inner timeline evidence, \
         `fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts` is the \
         sidecar packager, and `FullWitnessMemAirSourceProverDataFacts` is the \
         raw-facts fallback. \
         Lean stores that sidecar callback on `FullWitnessMemoryTimelineEvidence`; \
         `exists_fullWitnessMemAirSource_of_rawSidecars` selects the concrete \
         replay source, and `fullWitnessMemoryTimelineEvidence_of_rawSidecars` \
         feeds the compliance timeline boundary from sidecars plus the residual \
         Sail timeline facts. \
         Use `memTableGeneratedAirSource_of_witnessFacts` only for a concrete \
         table-level source with explicit Clean assertion/lookup witnesses."
    )
    .unwrap();
    writeln!(
        out,
        "- `MemTableGeneratedAirFacts.rowRanges` and `.segmentRanges` require \
         explicit range-check source facts; these are represented in pilout as \
         `gsum_debug_data` hints with `name_piop = \"Range Check\"`."
    )
    .unwrap();
    writeln!(
        out,
        "- Pilout symbols do not encode `bits(N)` declarations; use \
         `--pil-source` to attach the authoritative `mem.pil` source lines."
    )
    .unwrap();
    writeln!(out).unwrap();

    writeln!(out, "## Generated Lean Artifact Contract\n").unwrap();
    writeln!(
        out,
        "The generated artifact should expose a value of \
         `FullWitnessMemAirSourceProverDataWitnessFacts witness` and feed it \
         to `fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`."
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(out, "For each mutable Mem table, the callback must return:").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "| Obligation | Source |").unwrap();
    writeln!(out, "|---|---|").unwrap();
    writeln!(
        out,
        "| `MemTableGeneratedConstraintAssertionFacts` | Clean assertion witnesses \
         for `segment_every_row` constraints `0..=23` and \
         `permutation_every_row` constraints `24..=33` over the ProverData \
         sidecar columns |"
    )
    .unwrap();
    writeln!(
        out,
        "| `MemTableGeneratedRangeLookupFacts` | Clean range-lookup witnesses for \
         row-local range facts over the same ProverData-backed Mem view |"
    )
    .unwrap();
    writeln!(
        out,
        "| `MemSegmentGeneratedRangeLookupFacts` | Clean range-lookup witnesses \
         for segment-global range facts over \
         `segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data)` |"
    )
    .unwrap();
    writeln!(out).unwrap();
    writeln!(
        out,
        "Generated modules that prove raw `segment_every_row`, \
         `permutation_every_row`, and range propositions directly may instead \
         target \
         `Extraction.MemGeneratedConstraintBridge.ExtractedSidecarFacts` for \
         each mutable Mem table. The generated bridge checks both maps: \
         extracted `constraint_0..33` facts to raw split constraints, and \
         bit-width/range inequalities to raw row/segment range facts, then \
         feeds the resulting source facts through \
         `buildWitnessFactsFromExtractedSidecarFacts`. Lower-level modules may \
         still target `ExtractedRawSourceFacts`, expose \
         `FullWitnessMemAirSourceProverDataFacts witness`, and use the checked adapter \
         `fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts`."
    )
    .unwrap();
    writeln!(out).unwrap();

    writeln!(out, "## Witness Columns\n").unwrap();
    writeln!(out, "| Stage | Column | Name |").unwrap();
    writeln!(out, "|---:|---:|---|").unwrap();
    let mut witness_entries: Vec<_> = witness_cols.iter().collect();
    witness_entries.sort_by_key(|((stage, id), _)| (*stage, *id));
    for ((stage, id), name) in witness_entries {
        writeln!(out, "| {} | {} | `{}` |", stage, id, md_escape(name)).unwrap();
    }
    writeln!(out).unwrap();

    writeln!(out, "## Fixed Columns\n").unwrap();
    if fixed_cols.is_empty() {
        writeln!(out, "_No fixed-column symbols were named in pilout._").unwrap();
    } else {
        writeln!(out, "| Column | Name | First Values |").unwrap();
        writeln!(out, "|---:|---|---|").unwrap();
        for (idx, name) in &fixed_cols {
            let first_values = hit
                .air
                .fixed_cols
                .get(*idx as usize)
                .map(|col| {
                    col.values
                        .iter()
                        .take(8)
                        .map(|v| format_basefield(v))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_else(|| "<missing fixed col payload>".to_string());
            writeln!(
                out,
                "| {} | `{}` | `{}` |",
                idx,
                md_escape(name),
                md_escape(&first_values)
            )
            .unwrap();
        }
    }
    writeln!(out).unwrap();

    writeln!(out, "## Sidecar Source Map\n").unwrap();
    write_mem_air_sidecar_source_map(
        &mut out,
        &witness_cols,
        &fixed_cols,
        &air_values,
        &challenges,
    );
    writeln!(out).unwrap();

    writeln!(out, "## Constraint Inventory\n").unwrap();
    writeln!(out, "| Index | Domain | Lean Group | Debug Line |").unwrap();
    writeln!(out, "|---:|---|---|---|").unwrap();
    for (idx, c) in hit.air.constraints.iter().enumerate() {
        let (domain, debug_line) = constraint_domain_and_debug(c);
        let lean_group = match idx {
            0..=23 => "`segment_every_row`",
            24..=33 => "`permutation_every_row`",
            _ => "_outside named Mem package_",
        };
        writeln!(
            out,
            "| {} | `{}` | {} | {} |",
            idx,
            domain,
            lean_group,
            debug_line
                .as_deref()
                .map(|s| format!("`{}`", md_escape(s)))
                .unwrap_or_else(|| "".to_string())
        )
        .unwrap();
    }
    writeln!(out).unwrap();

    writeln!(out, "## Range-Check Hints\n").unwrap();
    write_mem_air_hint_table(&mut out, &range_hints);
    writeln!(out).unwrap();

    writeln!(out, "## Lean Range-Fact Coverage\n").unwrap();
    write_mem_air_range_fact_coverage(&mut out, &range_hints, source_lines.as_deref());
    writeln!(out).unwrap();

    writeln!(out, "## Other `gsum_debug_data` Hints\n").unwrap();
    write_mem_air_hint_table(&mut out, &other_hints);
    writeln!(out).unwrap();

    if let Some(source_lines) = source_lines {
        writeln!(out, "## `mem.pil` Source Lines\n").unwrap();
        if source_lines.is_empty() {
            writeln!(
                out,
                "_No relevant `bits`, `SEGMENT_L1`, or `range_check` lines found._"
            )
            .unwrap();
        } else {
            writeln!(out, "| Line | Source |").unwrap();
            writeln!(out, "|---:|---|").unwrap();
            for (line, text) in source_lines {
                writeln!(out, "| {} | `{}` |", line, md_escape(&text)).unwrap();
            }
        }
        writeln!(out).unwrap();
    }

    Ok(out)
}

fn scoped_symbol_names(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    ty: SymbolType,
) -> Vec<(u32, u32, String)> {
    let mut out = Vec::new();
    for sym in &pilout.symbols {
        let sym_ty = SymbolType::try_from(sym.r#type).unwrap_or(SymbolType::WitnessCol);
        if sym_ty != ty {
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
            out.push((stage, sym.id, sym.name.clone()));
        } else {
            let total: u32 = sym.lengths.iter().product();
            for k in 0..total {
                out.push((stage, sym.id + k, format!("{}[{}]", sym.name, k)));
            }
        }
    }
    out.sort_by_key(|(stage, id, _)| (*stage, *id));
    out
}

fn air_value_names(pilout: &PilOut, hit: &AirHit<'_>) -> Vec<(u32, u32, String)> {
    scoped_symbol_names(pilout, hit, SymbolType::AirValue)
}

fn challenge_names(pilout: &PilOut) -> Vec<(u32, u32, String)> {
    let mut out = Vec::new();
    for sym in &pilout.symbols {
        let ty = SymbolType::try_from(sym.r#type).unwrap_or(SymbolType::WitnessCol);
        if ty != SymbolType::Challenge {
            continue;
        }
        out.push((sym.stage.unwrap_or(0), sym.id, sym.name.clone()));
    }
    out.sort_by_key(|(stage, id, _)| (*stage, *id));
    out
}

fn fixed_column_names(pilout: &PilOut, hit: &AirHit<'_>) -> Vec<(u32, String)> {
    let mut out = Vec::new();
    for sym in &pilout.symbols {
        let ty = SymbolType::try_from(sym.r#type).unwrap_or(SymbolType::WitnessCol);
        if ty != SymbolType::FixedCol {
            continue;
        }
        if sym.air_group_id != Some(hit.airgroup_idx as u32) {
            continue;
        }
        if sym.air_id != Some(hit.air_idx as u32) {
            continue;
        }
        if sym.dim == 0 {
            out.push((sym.id, sym.name.clone()));
        } else {
            let total: u32 = sym.lengths.iter().product();
            for k in 0..total {
                out.push((sym.id + k, format!("{}[{}]", sym.name, k)));
            }
        }
    }
    out.sort_by_key(|(idx, _)| *idx);
    out
}

fn constraint_domain_and_debug(c: &Constraint) -> (String, Option<String>) {
    match c.constraint.as_ref() {
        Some(ConstraintKind::EveryRow(er)) => ("every_row".to_string(), er.debug_line.clone()),
        Some(ConstraintKind::FirstRow(fr)) => ("first_row".to_string(), fr.debug_line.clone()),
        Some(ConstraintKind::LastRow(lr)) => ("last_row".to_string(), lr.debug_line.clone()),
        Some(ConstraintKind::EveryFrame(ef)) => (
            format!("every_frame({},{})", ef.offset_min, ef.offset_max),
            ef.debug_line.clone(),
        ),
        None => ("<missing>".to_string(), None),
    }
}

fn mem_air_gsum_hints(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    piop_filter: Option<&str>,
) -> Result<Vec<(usize, BusEmission)>> {
    let mut out = Vec::new();
    for (idx, hint) in pilout.hints.iter().enumerate() {
        if hint.name != "gsum_debug_data" {
            continue;
        }
        if hint.air_group_id != Some(hit.airgroup_idx as u32) {
            continue;
        }
        if hint.air_id != Some(hit.air_idx as u32) {
            continue;
        }
        let em = parse_bus_emission(pilout, hit.air, hint).with_context(|| {
            format!(
                "hint #{} (AIR {})",
                idx,
                hit.air.name.clone().unwrap_or_default()
            )
        })?;
        if piop_filter.is_none_or(|filter| em.name_piop == filter) {
            out.push((idx, em));
        }
    }
    Ok(out)
}

fn witness_source(witness_cols: &HashMap<(u32, u32), String>, stage: u32, id: u32) -> String {
    match witness_cols.get(&(stage, id)) {
        Some(name) => format!("stage {} witness col {} `{}`", stage, id, md_escape(name)),
        None => format!("stage {} witness col {} `<missing symbol>`", stage, id),
    }
}

fn fixed_source(fixed_cols: &[(u32, String)], id: u32) -> String {
    match fixed_cols.iter().find(|(idx, _)| *idx == id) {
        Some((_, name)) => format!("fixed col {} `{}`", id, md_escape(name)),
        None => format!("fixed col {} `<missing symbol>`", id),
    }
}

fn air_value_source(air_values: &[(u32, u32, String)], stage: u32, id: u32) -> String {
    match air_values.iter().find(|(s, idx, _)| *s == stage && *idx == id) {
        Some((_, _, name)) => format!("stage {} AIR_VALUE {} `{}`", stage, id, md_escape(name)),
        None => format!("stage {} AIR_VALUE {} `<missing symbol>`", stage, id),
    }
}

fn challenge_source(challenges: &[(u32, u32, String)], stage: u32, id: u32) -> String {
    match challenges.iter().find(|(s, idx, _)| *s == stage && *idx == id) {
        Some((_, _, name)) => format!("challenge stage {} idx {} `{}`", stage, id, md_escape(name)),
        None => format!("challenge stage {} idx {} `<missing symbol>`", stage, id),
    }
}

fn write_mem_air_sidecar_source_map(
    out: &mut String,
    witness_cols: &HashMap<(u32, u32), String>,
    fixed_cols: &[(u32, String)],
    air_values: &[(u32, u32, String)],
    challenges: &[(u32, u32, String)],
) {
    let mut rows: Vec<(String, String, String, String)> = vec![
        (
            "`sidecar.gsum row`".into(),
            "`Mem.sidecar.gsum`".into(),
            witness_source(witness_cols, 2, 0),
            "stage-2 accumulator column".into(),
        ),
        (
            "`sidecar.im0 row`".into(),
            "`Mem.sidecar.im0`".into(),
            witness_source(witness_cols, 2, 1),
            "stage-2 intermediate product".into(),
        ),
        (
            "`sidecar.im1 row`".into(),
            "`Mem.sidecar.im1`".into(),
            witness_source(witness_cols, 2, 2),
            "stage-2 intermediate product".into(),
        ),
        (
            "`(segmentWithFixedL1 sidecar.segment).segment_l1 row`".into(),
            "`Mem.sidecar.segment.segment_l1`".into(),
            fixed_source(fixed_cols, 0),
            "deterministic segment boundary fixed column".into(),
        ),
        (
            "`sidecar.permutation.l1 row`".into(),
            "`Mem.sidecar.permutation.l1`".into(),
            fixed_source(fixed_cols, 1),
            "permutation final-row fixed column".into(),
        ),
        (
            "`sidecar.segment.segment_id`".into(),
            "`Mem.sidecar.segment.segment_id`".into(),
            air_value_source(air_values, 1, 0),
            "segment direct source".into(),
        ),
        (
            "`sidecar.segment.is_first_segment`".into(),
            "`Mem.sidecar.segment.is_first_segment`".into(),
            air_value_source(air_values, 1, 1),
            "segment selector".into(),
        ),
        (
            "`sidecar.segment.is_last_segment`".into(),
            "`Mem.sidecar.segment.is_last_segment`".into(),
            air_value_source(air_values, 1, 2),
            "segment selector".into(),
        ),
        (
            "`sidecar.segment.previous_segment_value_0`".into(),
            "`Mem.sidecar.segment.previous_segment_value_0`".into(),
            air_value_source(air_values, 1, 3),
            "previous segment carried value".into(),
        ),
        (
            "`sidecar.segment.previous_segment_value_1`".into(),
            "`Mem.sidecar.segment.previous_segment_value_1`".into(),
            air_value_source(air_values, 1, 4),
            "previous segment carried value".into(),
        ),
        (
            "`sidecar.segment.previous_segment_step`".into(),
            "`Mem.sidecar.segment.previous_segment_step`".into(),
            air_value_source(air_values, 1, 5),
            "previous segment carried step".into(),
        ),
        (
            "`sidecar.segment.previous_segment_addr`".into(),
            "`Mem.sidecar.segment.previous_segment_addr`".into(),
            air_value_source(air_values, 1, 6),
            "previous segment carried address".into(),
        ),
        (
            "`sidecar.segment.segment_last_value_0`".into(),
            "`Mem.sidecar.segment.segment_last_value_0`".into(),
            air_value_source(air_values, 1, 7),
            "segment carry-out value".into(),
        ),
        (
            "`sidecar.segment.segment_last_value_1`".into(),
            "`Mem.sidecar.segment.segment_last_value_1`".into(),
            air_value_source(air_values, 1, 8),
            "segment carry-out value".into(),
        ),
        (
            "`sidecar.segment.segment_last_step`".into(),
            "`Mem.sidecar.segment.segment_last_step`".into(),
            air_value_source(air_values, 1, 9),
            "segment carry-out step".into(),
        ),
        (
            "`sidecar.segment.segment_last_addr`".into(),
            "`Mem.sidecar.segment.segment_last_addr`".into(),
            air_value_source(air_values, 1, 10),
            "segment carry-out address".into(),
        ),
        (
            "`sidecar.segment.distance_base_0`".into(),
            "`Mem.sidecar.segment.distance_base_0`".into(),
            air_value_source(air_values, 1, 11),
            "segment range chunk".into(),
        ),
        (
            "`sidecar.segment.distance_base_1`".into(),
            "`Mem.sidecar.segment.distance_base_1`".into(),
            air_value_source(air_values, 1, 12),
            "segment range chunk".into(),
        ),
        (
            "`sidecar.segment.distance_end_0`".into(),
            "`Mem.sidecar.segment.distance_end_0`".into(),
            air_value_source(air_values, 1, 13),
            "segment range chunk".into(),
        ),
        (
            "`sidecar.segment.distance_end_1`".into(),
            "`Mem.sidecar.segment.distance_end_1`".into(),
            air_value_source(air_values, 1, 14),
            "segment range chunk".into(),
        ),
        (
            "`sidecar.permutation.std_alpha`".into(),
            "`Mem.sidecar.permutation.std_alpha`".into(),
            challenge_source(challenges, 2, 0),
            "permutation compression challenge".into(),
        ),
        (
            "`sidecar.permutation.std_gamma`".into(),
            "`Mem.sidecar.permutation.std_gamma`".into(),
            challenge_source(challenges, 2, 1),
            "permutation compression challenge".into(),
        ),
    ];

    for idx in 0..6 {
        rows.push((
            format!("`sidecar.permutation.im_direct_{}`", idx),
            format!("`Mem.sidecar.permutation.im_direct_{}`", idx),
            air_value_source(air_values, 2, 15 + idx),
            "direct-update inverse source".into(),
        ));
    }

    writeln!(
        out,
        "| Lean sidecar field | ProverData key | Pilout source | Role |"
    )
    .unwrap();
    writeln!(out, "|---|---|---|---|").unwrap();
    for (lean, key, source, role) in rows {
        writeln!(out, "| {} | {} | {} | {} |", lean, key, source, role).unwrap();
    }
}

fn write_mem_air_hint_table(out: &mut String, hints: &[(usize, BusEmission)]) {
    if hints.is_empty() {
        writeln!(out, "_No matching hints._").unwrap();
        return;
    }
    writeln!(
        out,
        "| Hint | PIOP | Side | Bus ID | Multiplicity | Slots |"
    )
    .unwrap();
    writeln!(out, "|---:|---|---|---:|---|---|").unwrap();
    for (idx, em) in hints {
        let slots = em
            .slots
            .iter()
            .map(|(name, value)| format!("`{} = {}`", md_escape(name), md_escape(value)))
            .collect::<Vec<_>>()
            .join("<br>");
        writeln!(
            out,
            "| {} | `{}` | `{}` | {} | `{}` | {} |",
            idx,
            md_escape(&em.name_piop),
            if em.type_piop { "proves" } else { "assumes" },
            em.busid,
            md_escape(&em.multiplicity),
            slots
        )
        .unwrap();
    }
}

fn write_mem_air_range_fact_coverage(
    out: &mut String,
    range_hints: &[(usize, BusEmission)],
    source_lines: Option<&[(usize, String)]>,
) {
    let source_supplied = source_lines.is_some();
    let hint_has = |needle: &str| {
        range_hints.iter().any(|(_, em)| {
            em.slots
                .iter()
                .any(|(name, value)| name.contains(needle) || value.contains(needle))
        })
    };
    let source_has = |needle: &str| {
        source_lines.is_some_and(|lines| {
            lines
                .iter()
                .any(|(_, text)| text.contains(needle))
        })
    };
    let status = |hints_ok: bool, source_ok: bool, source_required: bool| {
        if !hints_ok {
            "missing range hint"
        } else if source_required && !source_supplied {
            "hint present; rerun with `--pil-source` for bit-width provenance"
        } else if source_required && !source_ok {
            "missing `mem.pil` source line"
        } else {
            "present"
        }
    };

    let increment_hints = hint_has("l_increment") && hint_has("h_increment");
    let increment_source =
        source_has("range_check(expression: l_increment")
          && source_has("range_check(expression: h_increment");
    let addr_source = source_has("col witness bits(29) addr");
    let step_source =
        source_has("col witness bits(MEM_STEP_BITS) step")
          && source_has("col witness bits(MEM_STEP_BITS) air.step_dual")
          && source_has("col witness bits(40) air.previous_step");
    let dual_delta_hint = hint_has("(step_dual - step) - wr");
    let dual_delta_source = source_has("range_check(expression: step_dual - step - wr");
    let distance_base_hints =
        hint_has("Mem.distance_base[0]") && hint_has("Mem.distance_base[1]");
    let distance_base_source =
        source_has("range_check(expression: distance_base[0]")
          && source_has("range_check(expression: distance_base[1]");

    writeln!(out, "| Lean fact field | Extractor source | Status |").unwrap();
    writeln!(out, "|---|---|---|").unwrap();
    writeln!(
        out,
        "| `MemTableGeneratedRangeFacts.incrementChunks` | \
         `l_increment` / `h_increment` range hints plus `mem.pil:384-385` | `{}` |",
        status(increment_hints, increment_source, true)
    )
    .unwrap();
    writeln!(
        out,
        "| `MemTableGeneratedRangeFacts.addrColumns` | \
         `col witness bits(29) addr` (`mem.pil:109`) | `{}` |",
        status(true, addr_source, true)
    )
    .unwrap();
    writeln!(
        out,
        "| `MemTableGeneratedRangeFacts.stepColumns` | \
         `step`, `step_dual`, and `previous_step` bit declarations \
         (`mem.pil:110,122,365`) | `{}` |",
        status(true, step_source, true)
    )
    .unwrap();
    writeln!(
        out,
        "| `MemTableGeneratedRangeFacts.dualStepDelta` | \
         `step_dual - step - wr` range hint gated by `sel_dual` plus \
         `mem.pil:397` | `{}` |",
        status(dual_delta_hint, dual_delta_source, true)
    )
    .unwrap();
    writeln!(
        out,
        "| `MemSegmentGeneratedRangeFacts.distanceBaseChunks` | \
         `Mem.distance_base[0]` / `[1]` range hints plus `mem.pil:267-268` | `{}` |",
        status(distance_base_hints, distance_base_source, true)
    )
    .unwrap();
}

fn mem_pil_source_lines(path: &std::path::Path) -> Result<Vec<(usize, String)>> {
    let source = fs::read_to_string(path)
        .with_context(|| format!("failed to read PIL source {}", path.display()))?;
    let mut out = Vec::new();
    for (idx, line) in source.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.contains("col fixed SEGMENT_L1")
            || trimmed.contains("col witness bits(")
            || trimmed.contains("range_check(")
        {
            out.push((idx + 1, trimmed.to_string()));
        }
    }
    Ok(out)
}

fn md_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('|', "\\|")
        .replace('`', "\\`")
        .replace('\n', " ")
}

fn lean_escape(s: &str) -> String {
    s.replace("-/", "- /").replace('\n', " ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pilout::HintFieldArray;

    #[test]
    fn extraction_circuit_shim_is_namespaced() {
        let out = render_extraction_circuit_module();
        assert!(
            out.contains("namespace Extraction")
                && out.contains("class Circuit")
                && out.contains("main : C F ExtF → (id column row rotation : ℕ) → F")
                && out.contains("challenge : C F ExtF → (index : ℕ) → ExtF"),
            "shim should expose the generated-only circuit interface:\n{}",
            out
        );
        assert!(
            !out.contains("namespace Circuit"),
            "shim should not create or open a root Circuit namespace:\n{}",
            out
        );
    }

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
            "((Extraction.Circuit.main c (id := 1) (column := 7) (row := row - 1) (rotation := 0)) + 0)"
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
            "((Extraction.Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) + 0)"
        );
    }

    #[test]
    fn render_operand_witness_col_positive_offset_rewrites_to_row_add_k() {
        // Positive row offsets are rendered by shifting the row argument,
        // matching the negative-offset `row - k` rewrite above.
        let pilout = PilOut::default();
        let air = single_witness_expr_air(1, 7, 1);
        let rendered = render_expr_by_idx(&pilout, &air, 0).expect("should render");
        assert_eq!(
            rendered,
            "((Extraction.Circuit.main c (id := 1) (column := 7) (row := row + 1) (rotation := 0)) + 0)"
        );
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
            "((Extraction.Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) - (Extraction.Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))"
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
            "(3 * (Extraction.Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))"
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
            "(-(Extraction.Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))"
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
            "(((Extraction.Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + (Extraction.Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Extraction.Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))"
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
            r.contains("(Extraction.Circuit.preprocessed c (column := 3) (row := row) (rotation := 0))"),
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
            r.contains("(Extraction.Circuit.preprocessed c (column := 3) (row := row - 2) (rotation := 0))"),
            "unexpected render: {}",
            r
        );
    }

    #[test]
    fn render_operand_fixed_col_positive_offset_rewrites_row_add_k() {
        let air = Air {
            expressions: vec![add_expr(fixed_col_operand(3, 1), const_operand(vec![]))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert!(
            r.contains("(Extraction.Circuit.preprocessed c (column := 3) (row := row + 1) (rotation := 0))"),
            "unexpected render: {}",
            r
        );
    }

    #[test]
    fn render_operand_air_value_emits_exposed() {
        let air = Air {
            expressions: vec![add_expr(air_value_operand(7), const_operand(vec![]))],
            ..Default::default()
        };
        let r = render_expr_by_idx(&PilOut::default(), &air, 0).expect("render");
        assert!(
            r.contains("(Extraction.Circuit.exposed c (index := 7))"),
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
            r.contains("(Extraction.Circuit.challenge c (index := 3))"),
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
    fn air_value_names_array_symbol_expands_indexed() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                airs: vec![Air {
                    name: Some("Demo".into()),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            symbols: vec![pilout::Symbol {
                name: "Mem.im_direct".to_string(),
                air_group_id: Some(0),
                air_id: Some(0),
                r#type: SymbolType::AirValue as i32,
                id: 15,
                stage: Some(2),
                dim: 1,
                lengths: vec![3],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Demo").unwrap();
        let names = air_value_names(&pilout, &hit);
        assert_eq!(
            names,
            vec![
                (2, 15, "Mem.im_direct[0]".to_string()),
                (2, 16, "Mem.im_direct[1]".to_string()),
                (2, 17, "Mem.im_direct[2]".to_string()),
            ]
        );
    }

    #[test]
    fn challenge_names_reads_global_symbols() {
        let pilout = PilOut {
            symbols: vec![pilout::Symbol {
                name: "std_gamma".to_string(),
                r#type: SymbolType::Challenge as i32,
                id: 1,
                stage: Some(2),
                ..Default::default()
            }],
            ..Default::default()
        };
        assert_eq!(challenge_names(&pilout), vec![(2, 1, "std_gamma".to_string())]);
    }

    #[test]
    fn mem_air_facts_report_names_sidecars_as_stored_boundary() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Mem".into()),
                    num_rows: Some(16),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Mem").unwrap();
        let out = render_mem_air_facts_report(&pilout, &hit, None).unwrap();
        assert!(
            out.contains(
                "Lean stores that sidecar callback on `FullWitnessMemoryTimelineEvidence`"
            ),
            "report should name sidecars as the stored boundary:\n{}",
            out
        );
        assert!(
            out.contains("`fullWitnessMemoryTimelineEvidence_of_rawSidecars`"),
            "report should name the sidecar timeline constructor:\n{}",
            out
        );
        assert!(
            !out.contains("Lean converts that sidecar callback"),
            "report should not describe sidecars as raw-facts adapter plumbing:\n{}",
            out
        );
    }

    #[test]
    fn mem_air_facts_report_lists_prover_data_sidecar_keys() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Mem".into()),
                    num_rows: Some(16),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Mem").unwrap();
        let out = render_mem_air_facts_report(&pilout, &hit, None).unwrap();
        assert!(
            out.contains("| Lean sidecar field | ProverData key | Pilout source | Role |"),
            "report should include the ProverData key column:\n{}",
            out
        );
        assert!(
            out.contains("`Mem.sidecar.gsum`"),
            "report should name the stage-2 accumulator key:\n{}",
            out
        );
        assert!(
            out.contains("`Mem.sidecar.segment.previous_segment_addr`"),
            "report should name carried segment keys:\n{}",
            out
        );
        assert!(
            out.contains("`Mem.sidecar.permutation.im_direct_5`"),
            "report should name all direct-update inverse keys:\n{}",
            out
        );
        assert!(
            out.contains("`FullWitnessMemAirSourceProverDataWitnessFacts`")
                && out.contains("`FullWitnessGeneratedTimelineEvidence`")
                && out.contains(
                    "`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`"
                )
                && out.contains(
                    "`fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts`"
                )
                && out.contains(
                    "`fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts`"
                ),
            "report should point generated code at the ProverData witness target:\n{}",
            out
        );
        assert!(
            out.contains("`fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts`")
                && out.contains(
                    "`Extraction.MemGeneratedConstraintBridge.ExtractedSidecarFacts`"
                )
                && out.contains(
                    "`buildWitnessFactsFromExtractedSidecarFacts`"
                ),
            "report should point raw ProverData facts at checked raw assembly adapters:\n{}",
            out
        );
    }

    #[test]
    fn mem_air_facts_report_lists_generated_artifact_contract() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Mem".into()),
                    num_rows: Some(16),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Mem").unwrap();
        let out = render_mem_air_facts_report(&pilout, &hit, None).unwrap();
        assert!(
            out.contains("## Generated Lean Artifact Contract"),
            "report should include a generated artifact contract section:\n{}",
            out
        );
        assert!(
            out.contains("`MemTableGeneratedConstraintAssertionFacts`")
                && out.contains("`MemTableGeneratedRangeLookupFacts`")
                && out.contains("`MemSegmentGeneratedRangeLookupFacts`"),
            "report should list all per-table witness fact obligations:\n{}",
            out
        );
        assert!(
            out.contains("`segment_every_row` constraints `0..=23`")
                && out.contains("`permutation_every_row` constraints `24..=33`")
                && out.contains(
                    "`segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data)`"
                ),
            "report should identify the exact generated constraint/range sources:\n{}",
            out
        );
    }

    #[test]
    fn mem_generated_artifact_module_wraps_current_timeline_constructor() {
        let pilout = PilOut {
            air_groups: vec![pilout::AirGroup {
                name: Some("Zisk".into()),
                airs: vec![Air {
                    name: Some("Mem".into()),
                    num_rows: Some(16),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        let hit = find_air(&pilout, "Mem").unwrap();
        let out = render_mem_generated_artifact_module(&hit).unwrap();
        assert!(
            out.contains("namespace Extraction.MemGeneratedArtifact")
                && out.contains("abbrev WitnessFacts")
                && out.contains("abbrev ConstraintAssertions")
                && out.contains("abbrev RowRangeLookups")
                && out.contains("abbrev SegmentRangeLookups")
                && out.contains("abbrev RawFacts")
                && out.contains("abbrev RawConstraintFacts")
                && out.contains("abbrev RawRowRangeFacts")
                && out.contains("abbrev RawSegmentRangeFacts")
                && out.contains("abbrev RawSourceFacts")
                && out.contains("def buildWitnessFacts")
                && out.contains("def buildRawFacts")
                && out.contains("def buildWitnessFactsFromRawFacts")
                && out.contains("def buildWitnessFactsFromRawParts")
                && out.contains("FullWitnessMemAirSourceProverDataWitnessFacts witness"),
            "generated module should expose the typed witness-facts contract:\n{}",
            out
        );
        assert!(
            out.contains("MemOfProverData witness table")
                && out.contains("SegmentOfProverData witness")
                && out.contains("PermutationOfProverData witness"),
            "generated module should name the ProverData-backed table sources:\n{}",
            out
        );
        assert!(
            out.contains("abbrev GeneratedTimelineEvidence")
                && out.contains("FullWitnessGeneratedTimelineEvidence state entry")
                && out.contains("fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts"),
            "generated module should wrap the checked generated timeline constructor:\n{}",
            out
        );
        assert!(
            out.contains("fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts facts")
                && out.contains("replayBridgeOfTraceSplit h_traceSplit"),
            "generated module should use the ProverData sidecar path for replay evidence:\n{}",
            out
        );
        assert!(
            out.contains("FullWitnessMemAirSourceProverDataFacts witness")
                && out.contains("MemTableGeneratedRawSourceFacts")
                && out.contains("buildRawFacts witness constraints rowRanges segmentRanges")
                && out.contains("fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts rawFacts"),
            "generated module should expose the raw-facts adapter path:\n{}",
            out
        );
    }

    #[test]
    fn mem_generated_constraint_bridge_names_extracted_constraint_surface() {
        let out = render_mem_generated_constraint_bridge_module();
        assert!(
            out.contains("namespace Extraction.MemGeneratedConstraintBridge")
                && out.contains("structure ProverDataMemCircuit")
                && out.contains("instance proverDataMemCircuitExtractionCircuit")
                && out.contains("structure ExtractedConstraintFacts"),
            "bridge should expose the ProverData-backed extracted constraint surface:\n{}",
            out
        );
        assert!(
            out.contains("Mem.extraction.constraint_0_every_row")
                && out.contains("Mem.extraction.constraint_23_every_row")
                && out.contains("Mem.extraction.constraint_24_every_row")
                && out.contains("Mem.extraction.constraint_33_every_row"),
            "bridge should name the full Mem constraint range:\n{}",
            out
        );
        assert!(
            out.contains("MemOfProverData c.witness c.table")
                && out.contains("SegmentOfProverData c.witness")
                && out.contains("PermutationOfProverData c.witness"),
            "bridge should use the same ProverData-backed sources as the wrapper:\n{}",
            out
        );
        assert!(
            out.contains("def rawConstraintFacts_of_extractedConstraintFacts")
                && out.contains("def extractedConstraintFacts_of_rawConstraintFacts")
                && out.contains("RawConstraintFacts witness table")
                && out.contains("segmentAt := by")
                && out.contains("permutationAt := by"),
            "bridge should adapt extracted constraints to raw split Mem constraints:\n{}",
            out
        );
        assert!(
            out.contains("def buildRawFactsFromExtractedConstraintsAndRawRanges")
                && out.contains("def buildWitnessFactsFromExtractedConstraintsAndRawRanges")
                && out.contains("buildWitnessFactsFromRawFacts")
                && out.contains("RawRowRangeFacts witness table")
                && out.contains("RawSegmentRangeFacts witness"),
            "bridge should build witness facts from extracted constraints plus raw ranges:\n{}",
            out
        );
        assert!(
            out.contains("structure ExtractedRawSourceFacts")
                && out.contains("def rawSourceFacts_of_extractedRawSourceFacts")
                && out.contains("def extractedRawSourceFacts_of_rawSourceFacts")
                && out.contains("def buildRawFactsFromExtractedRawSourceFacts")
                && out.contains("def buildWitnessFactsFromExtractedRawSourceFacts"),
            "bridge should expose one raw source target for generated code:\n{}",
            out
        );
        assert!(
            out.contains("structure ExtractedRangeFacts")
                && out.contains("def rawRowRangeFacts_of_extractedRangeFacts")
                && out.contains("def rawSegmentRangeFacts_of_extractedRangeFacts")
                && out.contains("def extractedRangeFacts_of_rawRangeFacts")
                && out.contains("structure ExtractedSidecarFacts")
                && out.contains("def extractedSidecarFacts_of_rawSourceFacts")
                && out.contains("def buildExtractedSidecarFactsFromRawFacts")
                && out.contains("def buildWitnessFactsFromRawFactsViaExtractedSidecarFacts")
                && out.contains("def buildWitnessFactsFromExtractedSidecarFacts"),
            "bridge should expose generator-friendly range facts and sidecar builders:\n{}",
            out
        );
        assert!(
            out.contains("def buildTimelineEvidenceFromExtractedSidecarFacts")
                && out.contains("GeneratedTimelineEvidence state entry")
                && out.contains("buildTimelineEvidence"),
            "bridge should expose the checked generated timeline constructor path:\n{}",
            out
        );
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
        assert!(out.contains("import Extraction.Circuit"));
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
    fn render_air_emits_single_field_def_for_extf_constraint() {
        // A constraint mixing a witness cell with a Challenge is only
        // well-typed in Lean when the circuit uses one field for witness cells,
        // challenges, and exposed values. The renderer should keep the PIL
        // constraint as a single-field definition instead of skip-stubbing it.
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

        let hit = find_air(&pilout, "Demo").unwrap();
        let opts = RenderOpts {
            skip_unsupported: false,
            only: None,
        };
        let out = render_air(&pilout, hit, &opts).expect("render single-field mixed constraint");
        assert!(
            out.contains("Mixed witness/challenge constraint emitted for single-field circuits."),
            "expected single-field explanatory comment, got:\n{}",
            out
        );
        assert!(
            out.contains("def constraint_0_every_row {C : Type → Type → Sort u} {F : Type} [Field F] [Extraction.Circuit F F C] (c : C F F) (row: ℕ) :="),
            "expected a single-field constraint def, got:\n{}",
            out
        );
        assert!(
            out.contains("(Extraction.Circuit.challenge c (index := 0))"),
            "expected challenge operand to remain in the emitted constraint, got:\n{}",
            out
        );
        assert!(
            !out.contains("skipped:"),
            "mixed F/ExtF constraint should not be skip-stubbed"
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
