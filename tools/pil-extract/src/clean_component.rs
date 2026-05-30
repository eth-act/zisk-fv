//! Emitter for the Clean `Air.Flat.Component` source shape of an AIR.
//!
//! Plan step C0g (decision D-EXT): `pil-extract` emits, per AIR, the two
//! generated Lean files the Clean integration consumes:
//!
//!   * `Row.lean`         — the witness row as a `ProvableStruct`, plus the
//!                          `packed32` / `cPacked` reducible helpers.
//!   * `Constraints.lean` — the `main : Var <Row> FGL → Circuit FGL Unit`
//!                          do-block: one `assertZero` per F-only pilout
//!                          constraint, then the operation-bus
//!                          `OpBusChannel.push` reconstructed from the
//!                          proves-side `gsum_debug_data` hint; and the
//!                          `<air>Elaborated : ElaboratedCircuit` value.
//!
//! Faithfulness contract (D-EXT): the generated output must match the
//! hand-written reference (`ZiskFv/AirsClean/BinaryAdd/{Row,Constraints}.lean`)
//! constraint-for-constraint and field-for-field, and the op-bus emission
//! must agree slot-for-slot with `opBus_row_BinaryAdd`
//! (`ZiskFv/Airs/OperationBus/OperationBus.lean`).
//!
//! C0g is the BinaryAdd-shaped stage: this module handles the
//! `assertZero`-only constraint shape and the operation-bus `push`. Later
//! phases extend it one interaction-kind at a time (range lookups, ROM
//! lookups, memory bus, cross-row), each validated on one AIR first.

use std::collections::HashMap;

use anyhow::{anyhow, bail, Context, Result};

use crate::pilout::{
    constraint::Constraint as ConstraintKind, expression::Operation as ExprOp, hint_field,
    operand::Operand as OperandKind, Air, Expression, Hint, Operand, PilOut,
};

use crate::{
    const_operand_to_u64, expr_uses_extf, find_air, format_basefield, hint_field_by_name,
    sanitize, witness_column_names, AirHit,
};

/// One stage-1 witness column of the AIR, as it appears on the Clean row:
/// the column's stage-relative index, its Lean-safe field name, and the
/// original pilout column name (kept for the generated docstring).
struct RowField {
    col_idx: u32,
    /// Lean field identifier, e.g. `a_0` (sanitized from the pilout name
    /// `a[0]`).
    lean_name: String,
    /// The pilout column name verbatim, e.g. `a[0]`.
    pilout_name: String,
}

/// Resolve the stage-1 witness columns of `hit` into ordered `RowField`s.
///
/// Only stage-1 columns become Clean row fields: stage-2 accumulators
/// (`gsum`, the permutation intermediates) are subsumed by Clean's
/// channel-balance machinery and never constrained by the Component's
/// `main`. The result is sorted by `col_idx` so the emitted struct's field
/// order matches the witness layout.
fn row_fields(pilout: &PilOut, hit: &AirHit<'_>) -> Vec<RowField> {
    let col_names = witness_column_names(pilout, hit);
    let mut fields: Vec<RowField> = col_names
        .into_iter()
        .filter(|((stage, _), _)| *stage == 1)
        .map(|((_, col_idx), name)| RowField {
            col_idx,
            lean_name: lean_field_name(&name),
            pilout_name: name,
        })
        .collect();
    fields.sort_by_key(|f| f.col_idx);
    fields
}

/// Collect the names of the AIR's stage-2 witness columns — the
/// permutation accumulators (`gsum`) and intermediates that Clean's
/// channel-balance machinery subsumes. Listed in the generated `Row.lean`
/// docstring as the columns deliberately omitted from the typed row.
/// Deduplicated and order-stable (PIL arrays can map several indices to
/// one symbol name, e.g. BinaryAdd's `im_cluster`).
fn omitted_stage2_columns(pilout: &PilOut, hit: &AirHit<'_>) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    let mut by_idx: Vec<(u32, String)> = witness_column_names(pilout, hit)
        .into_iter()
        .filter(|((stage, _), _)| *stage == 2)
        .map(|((_, idx), name)| (idx, name))
        .collect();
    by_idx.sort_by_key(|(idx, _)| *idx);
    for (_, name) in by_idx {
        if !names.contains(&name) {
            names.push(name);
        }
    }
    names
}

/// Map a pilout column name to a Lean-safe struct field identifier.
/// `a[0]` → `a_0`, `c_chunks[3]` → `c_chunks_3`, `cout[1]` → `cout_1`.
/// Pure scalar names pass through unchanged.
fn lean_field_name(pilout_name: &str) -> String {
    pilout_name
        .chars()
        .filter(|c| *c != ']')
        .map(|c| if c == '[' { '_' } else { c })
        .collect()
}

/// A constraint-expression renderer that emits Clean `Expression FGL`
/// syntax with witness cells written as `row.<field>` projections.
///
/// This is the Clean-Component analogue of `crate::render_expr`, which
/// targets the legacy `Circuit.main c …` accessor shape. Stage-1 witness
/// cells become `row.<field>`; constants become decimal literals; the
/// arithmetic operators map straight onto `Expression`'s `Add`/`Sub`/`Mul`
/// /`Neg` instances.
struct CleanExprRenderer<'a> {
    pilout: &'a PilOut,
    air: &'a Air,
    /// stage-1 `col_idx` → Lean field name.
    col_to_field: &'a HashMap<u32, String>,
}

impl<'a> CleanExprRenderer<'a> {
    fn render_by_idx(&self, idx: usize) -> Result<String> {
        let expr = self
            .air
            .expressions
            .get(idx)
            .ok_or_else(|| anyhow!("expression index {} out of range", idx))?;
        self.render_expr(expr)
    }

    fn render_expr(&self, expr: &Expression) -> Result<String> {
        let op = expr
            .operation
            .as_ref()
            .ok_or_else(|| anyhow!("expression has no operation"))?;
        match op {
            ExprOp::Add(add) => {
                let l = self.render_operand(add.lhs.as_ref())?;
                let r = self.render_operand(add.rhs.as_ref())?;
                // Fold the additive identity. PIL2's `proves_operation`
                // macro pads pass-through bus slots as `cell + 0`; folding
                // `x + 0` / `0 + x` to `x` makes the emitted op-bus tuple
                // match `opBus_row_BinaryAdd` field-for-field. A rendered
                // operand string is literally `"0"` only for the constant
                // zero — a `row.<field>` projection never is.
                Ok(match (l.as_str(), r.as_str()) {
                    (_, "0") => l,
                    ("0", _) => r,
                    _ => format!("({} + {})", l, r),
                })
            }
            ExprOp::Sub(sub) => {
                let l = self.render_operand(sub.lhs.as_ref())?;
                let r = self.render_operand(sub.rhs.as_ref())?;
                Ok(match r.as_str() {
                    "0" => l,
                    _ => format!("({} - {})", l, r),
                })
            }
            ExprOp::Mul(mul) => {
                let l = self.render_operand(mul.lhs.as_ref())?;
                let r = self.render_operand(mul.rhs.as_ref())?;
                // Fold multiplicative identity / annihilator.
                Ok(match (l.as_str(), r.as_str()) {
                    ("0", _) | (_, "0") => "0".to_string(),
                    ("1", _) => r,
                    (_, "1") => l,
                    _ => format!("({} * {})", l, r),
                })
            }
            ExprOp::Neg(neg) => {
                let v = self.render_operand(neg.value.as_ref())?;
                Ok(format!("(-{})", v))
            }
        }
    }

    fn render_operand(&self, operand: Option<&Operand>) -> Result<String> {
        let operand = operand.ok_or_else(|| anyhow!("operand missing"))?;
        let kind = operand
            .operand
            .as_ref()
            .ok_or_else(|| anyhow!("operand has no kind"))?;
        match kind {
            OperandKind::Constant(c) => Ok(format_basefield(&c.value)),
            OperandKind::WitnessCol(w) => {
                if w.row_offset != 0 {
                    bail!(
                        "Clean-Component emission does not yet support rotated witness \
                         cells (column {} rotation {}); the C0g BinaryAdd shape is \
                         single-row. A cross-row phase must extend this.",
                        w.col_idx,
                        w.row_offset
                    );
                }
                if w.stage != 1 {
                    bail!(
                        "Clean-Component emission expects stage-1 witness cells on the \
                         row; got stage {} column {}. Stage-2 accumulators are channel-\
                         implicit and must not appear in a constraint.",
                        w.stage,
                        w.col_idx
                    );
                }
                let field = self.col_to_field.get(&w.col_idx).ok_or_else(|| {
                    anyhow!(
                        "stage-1 witness column {} has no named row field; the row \
                         struct cannot reference it",
                        w.col_idx
                    )
                })?;
                Ok(format!("row.{}", field))
            }
            OperandKind::Expression(e) => self.render_by_idx(e.idx as usize),
            other => bail!(
                "operand kind {:?} is not supported by the Clean-Component emitter \
                 (C0g handles the assertZero-only BinaryAdd shape)",
                other
            ),
        }
    }
}

/// Strip one redundant outermost paren pair: `render_expr` always wraps a
/// binary node, but `assertZero (e)` already parenthesizes its argument, so
/// the top-level wrap is noise. Matches the hand-written reference, which
/// writes `assertZero (a + b - c)` not `assertZero ((a + b) - c)` … with
/// the extra layer. Only strips when the string is a single fully-balanced
/// `(…)` group, so it never mangles `(a) + (b)`.
fn strip_outer_parens(s: &str) -> &str {
    let bytes = s.as_bytes();
    if bytes.first() != Some(&b'(') || bytes.last() != Some(&b')') {
        return s;
    }
    let mut depth = 0usize;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                // Hit depth 0 before the final char ⇒ not a single group.
                if depth == 0 && i + 1 != bytes.len() {
                    return s;
                }
            }
            _ => {}
        }
    }
    &s[1..s.len() - 1]
}

/// One operation-bus emission resolved from a proves-side `gsum_debug_data`
/// hint, with its slot values rendered against the Clean row.
struct CleanBusEmission {
    /// The bus id this push targets — recorded for provenance in the
    /// generated file's op-bus comment.
    busid: u64,
    /// Per-slot rendered Lean expression, positional (slot 0 = op, …). The
    /// names are discarded — the slot *position* fixes the `OpBusMessage`
    /// field, mirroring `OpBusMessage`'s declared field order.
    slot_values: Vec<String>,
}

/// The 11 `OpBusMessage` fields, in declared order
/// (`ZiskFv/Channels/OperationBus.lean`). The operation bus is an 11-tuple
/// (`zisk/pil/operations.pil:144`); slot `i` of the proves-side hint maps
/// to field `i` here.
const OP_BUS_MESSAGE_FIELDS: [&str; 11] = [
    "op",
    "a_lo",
    "a_hi",
    "b_lo",
    "b_hi",
    "c_lo",
    "c_hi",
    "flag",
    "main_step",
    "extended_arg",
    "extra_args_0",
];

/// The 6 `MemBusMessage` fields, in declared order
/// (`ZiskFv/Channels/MemoryBus.lean`). The MemAlign-family memory-bus
/// proves-side tuple is `[mem_op, ptr, timestamp, width, value_0, value_1]`
/// (`mem_align_byte.pil:96`, `permutation_proves`).
const MEM_BUS_MESSAGE_FIELDS: [&str; 6] =
    ["mem_op", "ptr", "timestamp", "width", "value_0", "value_1"];

/// Which Clean channel the AIR's proves-side `push` targets — selects the
/// message shape, the channel name, and which bus to resolve.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ChannelKind {
    /// The 11-slot `OpBusChannel` (operation bus, C0g BinaryAdd shape).
    OpBus,
    /// The 6-slot `MemBusChannel`; selected by legacy `mem-align-bus`.
    MemoryBus,
}

impl ChannelKind {
    /// Parse the `--channel` CLI flag.
    pub fn from_flag(flag: &str) -> Result<ChannelKind> {
        match flag {
            "op-bus" => Ok(ChannelKind::OpBus),
            "mem-align-bus" => Ok(ChannelKind::MemoryBus),
            other => bail!(
                "unknown --channel `{}`; expected `op-bus` or `mem-align-bus`",
                other
            ),
        }
    }

    /// The declared message-field names, in slot order.
    fn message_fields(self) -> &'static [&'static str] {
        match self {
            ChannelKind::OpBus => &OP_BUS_MESSAGE_FIELDS,
            ChannelKind::MemoryBus => &MEM_BUS_MESSAGE_FIELDS,
        }
    }

    /// The Clean channel value the `main` do-block pushes onto.
    fn channel_value(self) -> &'static str {
        match self {
            ChannelKind::OpBus => "OpBusChannel",
            ChannelKind::MemoryBus => "MemBusChannel",
        }
    }

    /// The `import` line for the channel's defining module.
    fn channel_import(self) -> &'static str {
        match self {
            ChannelKind::OpBus => "import ZiskFv.Channels.OperationBus",
            ChannelKind::MemoryBus => "import ZiskFv.Channels.MemoryBus",
        }
    }

    /// The `open` namespace bringing the channel value into scope.
    fn channel_open(self) -> &'static str {
        match self {
            ChannelKind::OpBus => "open ZiskFv.Channels.OperationBus (OpBusChannel)",
            ChannelKind::MemoryBus => "open ZiskFv.Channels.MemoryBus (MemBusChannel)",
        }
    }

    /// Human label for the bus, used in generated comments.
    fn bus_label(self) -> &'static str {
        match self {
            ChannelKind::OpBus => "operation bus",
            ChannelKind::MemoryBus => "memory bus",
        }
    }

    /// The `name_piop` string the proves-side `push` emission carries.
    /// ZisK's operation bus is a logUp **`Lookup`** argument
    /// (`proves_operation`); the MemAlign-family memory bus is a
    /// **`Permutation`** argument (`permutation_proves`). The other
    /// proves-side emissions on the same bus (the inert `Direct`
    /// range-check rows) are filtered out.
    fn proves_piop(self) -> &'static str {
        match self {
            ChannelKind::OpBus => "Lookup",
            ChannelKind::MemoryBus => "Permutation",
        }
    }
}

/// Resolve the AIR's single proves-side permutation `push` emission on
/// `bus_id`.
///
/// An AIR that pushes onto a bus emits a `gsum_debug_data` hint with
/// `busid = bus_id`, `type_piop = proves`, and `name_piop = "Permutation"`
/// (the `proves_operation(…)` / `permutation_proves(…)` PIL macros). The
/// matching assumes-side hints, and the inert `Direct`-mode range-check
/// emissions (`multiplicity = 0`), are skipped. Exactly one proves-side
/// **Permutation** emission must remain — that is this provider's `push`.
fn resolve_bus_push(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    bus_id: u64,
    channel: ChannelKind,
    col_to_field: &HashMap<u32, String>,
) -> Result<CleanBusEmission> {
    let air = hit.air;
    let renderer = CleanExprRenderer {
        pilout,
        air,
        col_to_field,
    };
    let want_piop = channel.proves_piop();

    let mut found: Option<CleanBusEmission> = None;
    for (hi, hint) in pilout.hints.iter().enumerate() {
        if hint.name != "gsum_debug_data" {
            continue;
        }
        if hint.air_group_id != Some(hit.airgroup_idx as u32)
            || hint.air_id != Some(hit.air_idx as u32)
        {
            continue;
        }
        let (busid, is_proves, piop, slots) = parse_op_bus_hint(&renderer, hint)
            .with_context(|| format!("gsum_debug_data hint #{}", hi))?;
        // Keep only the proves-side push of the channel's PIOP kind on
        // the target bus — the assumes-side pulls and the inert
        // `Direct` range-check emissions are not this provider's `push`.
        if busid != bus_id || !is_proves || piop != want_piop {
            continue;
        }
        if found.is_some() {
            bail!(
                "AIR `{}` has more than one proves-side `{}` emission on \
                 bus_id {}; the Clean-Component emitter expects exactly one push",
                air.name.as_deref().unwrap_or("<unnamed>"),
                want_piop,
                bus_id
            );
        }
        found = Some(CleanBusEmission {
            busid,
            slot_values: slots,
        });
    }

    found.ok_or_else(|| {
        anyhow!(
            "AIR `{}` has no proves-side `{}` emission for bus_id {}",
            air.name.as_deref().unwrap_or("<unnamed>"),
            want_piop,
            bus_id
        )
    })
}

/// Decode a `gsum_debug_data` hint into
/// `(busid, is_proves, name_piop, slot_values)`, rendering each tuple
/// slot through the Clean-row expression renderer.
fn parse_op_bus_hint(
    renderer: &CleanExprRenderer<'_>,
    hint: &Hint,
) -> Result<(u64, bool, String, Vec<String>)> {
    let outer = hint
        .hint_fields
        .first()
        .ok_or_else(|| anyhow!("hint has no fields"))?;
    let array = match outer.value.as_ref() {
        Some(hint_field::Value::HintFieldArray(a)) => &a.hint_fields,
        _ => bail!("gsum_debug_data outer field is not a HintFieldArray"),
    };

    let busid = match hint_field_by_name(array, "busid").and_then(|f| f.value.as_ref()) {
        Some(hint_field::Value::Operand(op)) => {
            const_operand_to_u64(op).ok_or_else(|| anyhow!("busid is not a constant"))?
        }
        _ => bail!("missing or non-operand busid"),
    };
    let is_proves = match hint_field_by_name(array, "type_piop").and_then(|f| f.value.as_ref()) {
        Some(hint_field::Value::Operand(op)) => {
            const_operand_to_u64(op).ok_or_else(|| anyhow!("type_piop is not a constant"))? != 0
        }
        _ => bail!("missing or non-operand type_piop"),
    };
    // `name_piop` is the PIOP kind string ("Permutation" / "Lookup" /
    // "Direct" / "Range Check"). The caller filters on it to pick the
    // channel's proves-side `push` emission.
    let name_piop = match hint_field_by_name(array, "name_piop").and_then(|f| f.value.as_ref()) {
        Some(hint_field::Value::StringValue(s)) => s.clone(),
        _ => bail!("missing or non-string name_piop"),
    };
    let exprs_arr = match hint_field_by_name(array, "expressions").and_then(|f| f.value.as_ref()) {
        Some(hint_field::Value::HintFieldArray(a)) => &a.hint_fields,
        _ => bail!("missing or non-array expressions"),
    };

    let mut slots = Vec::with_capacity(exprs_arr.len());
    for slot in exprs_arr {
        let op = match slot.value.as_ref() {
            Some(hint_field::Value::Operand(op)) => op,
            _ => bail!("operation-bus slot is not an operand"),
        };
        // Constants render directly; Expression operands recurse through
        // the Clean-row renderer after an ExtF check. A challenge / AirValue
        // (directly or under an Expression) would be an ExtF leak — fail
        // loudly, never stub: the operation bus is F-only in ZisK's pilout.
        let rendered = match op.operand.as_ref() {
            Some(OperandKind::Constant(c)) => format_basefield(&c.value),
            Some(OperandKind::Expression(e)) => {
                let idx = e.idx as usize;
                if expr_uses_extf(renderer.pilout, renderer.air, idx)? {
                    bail!(
                        "operation-bus slot references an ExtF operand (challenge / \
                         AirValue); the Clean `OpBusMessage` is F-typed and the C0g \
                         emitter will not silently stub it"
                    );
                }
                renderer.render_by_idx(idx)?
            }
            Some(OperandKind::Challenge(_))
            | Some(OperandKind::AirValue(_))
            | Some(OperandKind::AirGroupValue(_)) => bail!(
                "operation-bus slot references an ExtF operand (challenge / \
                 AirValue); the Clean `OpBusMessage` is F-typed and the C0g \
                 emitter will not silently stub it"
            ),
            other => bail!(
                "operation-bus slot operand kind {:?} not supported",
                other
            ),
        };
        slots.push(rendered);
    }
    Ok((busid, is_proves, name_piop, slots))
}

/// Render the `Row.lean` content for the AIR: the `<Air>Row` `ProvableStruct`
/// plus the `packed32` / `cPacked` reducible helpers.
///
/// C0g target: `ZiskFv/AirsClean/BinaryAdd/Row.lean`.
fn render_row_file(air_name: &str, fields: &[RowField], omitted: &[String]) -> String {
    let row_ty = format!("{}Row", air_name);
    let mut out = String::new();
    out.push_str("import Clean.Circuit.Channel\n");
    out.push_str("import Clean.Circuit.Provable\n");
    out.push_str("import Clean.Utils.Tactics.ProvableStructDeriving\n");
    out.push_str("import ZiskFv.Field.Goldilocks\n\n");

    out.push_str("/-!\n");
    out.push_str(&format!("# {} row type (Clean ProvableStruct)\n\n", air_name));
    out.push_str(&format!(
        "The stage-1 witness row layout for ZisK's {} AIR, expressed as a\n\
         `ProvableStruct` for consumption by a Clean `GeneralFormalCircuit`.\n\n\
         AUTO-GENERATED by `tools/pil-extract` (`clean-component` subcommand)\n\
         from `build/zisk.pilout` — do not hand-edit.\n\n",
        air_name
    ));
    out.push_str("Stage-1 columns (one struct field each):\n\n");
    for f in fields {
        out.push_str(&format!(
            "* `{}` — pilout column {} (`{}`)\n",
            f.lean_name, f.col_idx, f.pilout_name
        ));
    }
    if !omitted.is_empty() {
        out.push_str(&format!(
            "\nStage-2 columns ({}) are omitted: they are the permutation\n\
             accumulators / intermediates, which Clean's channel-balance\n\
             machinery subsumes. The row here is the witness-only slice the\n\
             Clean Component constrains directly.\n",
            omitted
                .iter()
                .map(|n| format!("`{}`", n))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    out.push('\n');
    out.push_str("## Trust note\n\n");
    out.push_str("No axiom added — this is a pure data definition.\n");
    out.push_str("-/\n\n");

    out.push_str(&format!("namespace ZiskFv.AirsClean.{}\n\n", air_name));
    out.push_str("open Goldilocks\n\n");

    out.push_str(&format!(
        "/-- The {}-column stage-1 witness row for {}. -/\n",
        fields.len(),
        air_name
    ));
    out.push_str(&format!("structure {} (F : Type) where\n", row_ty));
    for f in fields {
        out.push_str(&format!("  {} : F\n", f.lean_name));
    }
    out.push_str("deriving ProvableStruct\n\n");

    // The two reducible packing helpers. Their shape is fixed for the
    // BinaryAdd-style row (two 32-bit operands, four 16-bit result
    // `c_chunks` columns); emitted verbatim to match the hand-written
    // reference. They are emitted ONLY when the row actually has the
    // four `c_chunks_*` columns — a memory-bus AIR (MemAlignByte etc.)
    // has no such columns, so the helpers are skipped.
    let has_c_chunks = ["c_chunks_0", "c_chunks_1", "c_chunks_2", "c_chunks_3"]
        .iter()
        .all(|n| fields.iter().any(|f| f.lean_name == *n));
    if has_c_chunks {
        out.push_str("/-- The 32-bit packed value of a two-half lane. -/\n");
        out.push_str("@[reducible]\n");
        out.push_str("def packed32 (lo hi : FGL) : ℕ := lo.val + hi.val * 2 ^ 32\n\n");

        out.push_str("/-- The 64-bit packed value reconstructed from four 16-bit chunks. -/\n");
        out.push_str("@[reducible]\n");
        out.push_str(&format!(
            "def cPacked (row : {} FGL) : ℕ :=\n",
            row_ty
        ));
        out.push_str("  (row.c_chunks_0.val + row.c_chunks_1.val * 2 ^ 16) +\n");
        out.push_str("  (row.c_chunks_2.val + row.c_chunks_3.val * 2 ^ 16) * 2 ^ 32\n\n");
    }

    out.push_str(&format!("end ZiskFv.AirsClean.{}\n", air_name));
    out
}

/// Render the `Constraints.lean` content for the AIR: the `main` do-block
/// (`assertZero` per F-only constraint, then the op-bus `OpBusChannel.push`)
/// and the `<air>Elaborated : ElaboratedCircuit` value.
///
/// C0g target: `ZiskFv/AirsClean/BinaryAdd/Constraints.lean`.
fn render_constraints_file(
    pilout: &PilOut,
    hit: &AirHit<'_>,
    fields: &[RowField],
    bus_id: u64,
    channel: ChannelKind,
) -> Result<String> {
    let air = hit.air;
    let air_name = air
        .name
        .clone()
        .ok_or_else(|| anyhow!("air has no name"))?;
    let row_ty = format!("{}Row", air_name);
    let col_to_field: HashMap<u32, String> = fields
        .iter()
        .map(|f| (f.col_idx, f.lean_name.clone()))
        .collect();
    let renderer = CleanExprRenderer {
        pilout,
        air,
        col_to_field: &col_to_field,
    };

    // Render every F-only constraint as an `assertZero`. Constraints that
    // mix in ExtF operands (the permutation running-product updates) are
    // the bus interaction's algebraic shadow — they are *replaced* by the
    // channel `push` below, so they are skipped here, exactly as the
    // hand-written `Constraints.lean` does.
    let mut assertions: Vec<(usize, String, Option<String>)> = Vec::new();
    for (idx, c) in air.constraints.iter().enumerate() {
        let kind = c
            .constraint
            .as_ref()
            .ok_or_else(|| anyhow!("constraint #{} is empty", idx))?;
        let (expr_idx, debug_line) = match kind {
            ConstraintKind::EveryRow(er) => (er.expression_idx.as_ref(), er.debug_line.clone()),
            ConstraintKind::FirstRow(fr) => (fr.expression_idx.as_ref(), fr.debug_line.clone()),
            ConstraintKind::LastRow(lr) => (lr.expression_idx.as_ref(), lr.debug_line.clone()),
            ConstraintKind::EveryFrame(ef) => {
                (ef.expression_idx.as_ref(), ef.debug_line.clone())
            }
        };
        let expr_idx = expr_idx
            .ok_or_else(|| anyhow!("constraint #{} has no expression_idx", idx))?
            .idx as usize;
        if expr_uses_extf(pilout, air, expr_idx)? {
            // Permutation/lookup running-product constraint — represented
            // by the channel `push`, not an `assertZero`.
            continue;
        }
        let rendered = renderer.render_by_idx(expr_idx)?;
        assertions.push((
            idx,
            strip_outer_parens(&rendered).to_string(),
            debug_line.filter(|s| !s.is_empty()),
        ));
    }
    if assertions.is_empty() {
        bail!(
            "AIR `{}` produced no F-only constraints; the Clean-Component \
             emitter expects at least one assertZero",
            air_name
        );
    }

    let push = resolve_bus_push(pilout, hit, bus_id, channel, &col_to_field)?;
    let message_fields = channel.message_fields();
    if push.slot_values.len() != message_fields.len() {
        bail!(
            "AIR `{}` {} tuple has {} slots; the channel message declares \
             {} fields — the positional slot↔field mapping is broken",
            air_name,
            channel.bus_label(),
            push.slot_values.len(),
            message_fields.len()
        );
    }
    let channel_value = channel.channel_value();

    let mut out = String::new();
    out.push_str(&format!(
        "import ZiskFv.AirsClean.{}.Spec\n",
        air_name
    ));
    out.push_str("import Clean.Circuit.Basic\n");
    out.push_str(channel.channel_import());
    out.push_str("\n\n");

    out.push_str("/-!\n");
    out.push_str(&format!(
        "# {} circuit operations (the `main` field of the Component)\n\n",
        air_name
    ));
    out.push_str(&format!(
        "The constraint emissions of ZisK's {} AIR, expressed as a Clean\n\
         circuit do-block: one `assertZero` per F-only pilout constraint,\n\
         then the {} `{}.push`.\n\n\
         AUTO-GENERATED by `tools/pil-extract` (`clean-component` subcommand) —\n\
         do not hand-edit. The bus push is reconstructed from the\n\
         proves-side `gsum_debug_data` hint and is slot-for-slot faithful to\n\
         the hand-written reference.\n\n",
        air_name, channel.bus_label(), channel_value
    ));
    out.push_str("## Trust note\n\n");
    out.push_str("No axioms. Pure operational declaration.\n");
    out.push_str("-/\n\n");

    out.push_str(&format!("namespace ZiskFv.AirsClean.{}\n\n", air_name));
    out.push_str("open Goldilocks\n");
    out.push_str("open Circuit (assertZero)\n");
    out.push_str(channel.channel_open());
    out.push_str("\n\n");

    out.push_str(&format!(
        "/-- The {} F-constraints and {} push, taking the row's slot\n    \
         values as `Expression FGL`s. Returns `Unit` ({} is a pure\n    \
         assertion — no fresh witnesses introduced inside the circuit). -/\n",
        assertions.len(),
        channel.bus_label(),
        air_name
    ));
    out.push_str("@[circuit_norm]\n");
    out.push_str(&format!(
        "def main (row : Var {} FGL) : Circuit FGL Unit := do\n",
        row_ty
    ));
    for (idx, body, debug) in &assertions {
        // The pilout `debug_line` is `<file>:<line> <raw-PIL-expr>`; keep
        // only the source location — the `assertZero` line below already
        // IS the expression, so the raw dump is noise.
        match debug.as_deref().map(pil_source_location) {
            Some(loc) => out.push_str(&format!("  -- constraint {} ({})\n", idx, loc)),
            None => out.push_str(&format!("  -- constraint {}\n", idx)),
        }
        out.push_str(&format!("  assertZero ({})\n", body));
    }
    out.push_str(&format!(
        "  -- Bus emission: {} pushes its proves-side tuple onto {} {}.\n  \
         -- Reconstructed from the proves-side `gsum_debug_data` hint;\n  \
         -- slot-for-slot faithful to the hand-written reference.\n",
        air_name, channel.bus_label(), push.busid
    ));
    out.push_str(&format!("  {}.push\n", channel_value));
    let n_fields = message_fields.len();
    for (i, field) in message_fields.iter().enumerate() {
        let value = &push.slot_values[i];
        let open = if i == 0 { "    { " } else { "      " };
        let close = if i + 1 == n_fields { " }" } else { "" };
        out.push_str(&format!("{}{} := {}{}\n", open, field, value, close));
    }
    out.push('\n');

    out.push_str(&format!(
        "/-- The elaborated circuit for {}'s `main` — {} `assertZero`\n    \
         constraints + the bus push, no fresh witnesses (`localLength = 0`,\n    \
         `unit` output). Lives here (next to `main`) rather than in\n    \
         `Circuit.lean` so the completeness axiom (`Completeness.lean`, whose\n    \
         type mentions this) can be declared without an import cycle. -/\n",
        air_name,
        assertions.len()
    ));
    out.push_str("@[reducible] def ");
    out.push_str(&format!(
        "{}Elaborated : ElaboratedCircuit FGL {} unit where\n",
        lower_first(&air_name),
        row_ty
    ));
    out.push_str(&format!("  name := \"{}\"\n", air_name));
    out.push_str("  main := main\n");
    out.push_str("  localLength _ := 0\n");
    out.push_str("  output _ _ := ()\n");
    out.push_str(&format!(
        "  channelsWithRequirements := [{}.toRaw]\n\n",
        channel_value
    ));

    out.push_str(&format!("end ZiskFv.AirsClean.{}\n", air_name));
    Ok(out)
}

/// Extract the `<file>:<line>` prefix of a pilout `debug_line`. The pilout
/// records `binary/pil/binary_add.pil:19 (a[0]+b[0])-…`; the trailing raw
/// PIL expression is dropped — the emitted `assertZero` line is the
/// expression. If there is no space, the whole string is the location.
fn pil_source_location(debug_line: &str) -> &str {
    debug_line
        .split_once(' ')
        .map(|(loc, _)| loc)
        .unwrap_or(debug_line)
}

/// Lowercase the first character — `BinaryAdd` → `binaryAdd`, for the
/// `<air>Elaborated` value name.
fn lower_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_lowercase().chain(chars).collect(),
        None => String::new(),
    }
}

/// Entry point: emit the Clean `Air.Flat.Component` source for one AIR.
///
/// Returns `(row_source, constraints_source)`. The caller writes them to
/// `Row.lean` / `Constraints.lean` (or prints them).
pub fn run(
    pilout: &PilOut,
    air_needle: &str,
    bus_id: u64,
    channel: ChannelKind,
) -> Result<(String, String)> {
    let hit = find_air(pilout, air_needle)?;
    let air_name = sanitize(
        hit.air
            .name
            .as_deref()
            .ok_or_else(|| anyhow!("air has no name"))?,
    );
    let fields = row_fields(pilout, &hit);
    if fields.is_empty() {
        bail!(
            "AIR `{}` has no stage-1 witness columns; cannot build a Clean row",
            air_name
        );
    }
    let omitted = omitted_stage2_columns(pilout, &hit);
    let row = render_row_file(&air_name, &fields, &omitted);
    let constraints = render_constraints_file(pilout, &hit, &fields, bus_id, channel)?;
    Ok((row, constraints))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_field_name_indexes_become_underscores() {
        assert_eq!(lean_field_name("a[0]"), "a_0");
        assert_eq!(lean_field_name("c_chunks[3]"), "c_chunks_3");
        assert_eq!(lean_field_name("cout[1]"), "cout_1");
        assert_eq!(lean_field_name("gsum"), "gsum");
    }

    #[test]
    fn strip_outer_parens_removes_single_group() {
        assert_eq!(strip_outer_parens("(a + b)"), "a + b");
        assert_eq!(strip_outer_parens("((a + b) - c)"), "(a + b) - c");
    }

    #[test]
    fn strip_outer_parens_keeps_non_enclosing() {
        // `(a) + (b)` is not a single enclosing group — depth returns to 0
        // before the end, so the whole string is preserved.
        assert_eq!(strip_outer_parens("(a) + (b)"), "(a) + (b)");
        assert_eq!(strip_outer_parens("a + b"), "a + b");
    }

    #[test]
    fn lower_first_lowercases_initial() {
        assert_eq!(lower_first("BinaryAdd"), "binaryAdd");
        assert_eq!(lower_first("Mem"), "mem");
        assert_eq!(lower_first(""), "");
    }

    #[test]
    fn op_bus_message_field_count_is_eleven() {
        // The operation bus is an 11-tuple (zisk/pil/operations.pil:144).
        assert_eq!(OP_BUS_MESSAGE_FIELDS.len(), 11);
    }

    #[test]
    fn pil_source_location_keeps_only_file_line() {
        assert_eq!(
            pil_source_location("binary/pil/binary_add.pil:19 (a[0]+b[0])-c"),
            "binary/pil/binary_add.pil:19"
        );
        // No trailing expression — whole string is the location.
        assert_eq!(
            pil_source_location("binary_add.pil:14"),
            "binary_add.pil:14"
        );
    }

    use crate::pilout::{operand, Air, Expression, Operand, PilOut};

    fn witness(col_idx: u32) -> Operand {
        Operand {
            operand: Some(OperandKind::WitnessCol(operand::WitnessCol {
                stage: 1,
                col_idx,
                row_offset: 0,
            })),
        }
    }
    fn constant(bytes: Vec<u8>) -> Operand {
        Operand {
            operand: Some(OperandKind::Constant(operand::Constant { value: bytes })),
        }
    }
    fn add(lhs: Operand, rhs: Operand) -> Expression {
        Expression {
            operation: Some(ExprOp::Add(crate::pilout::expression::Add {
                lhs: Some(lhs),
                rhs: Some(rhs),
            })),
        }
    }
    fn mul(lhs: Operand, rhs: Operand) -> Expression {
        Expression {
            operation: Some(ExprOp::Mul(crate::pilout::expression::Mul {
                lhs: Some(lhs),
                rhs: Some(rhs),
            })),
        }
    }

    /// The identity fold makes a pass-through bus slot `cell + 0` render as
    /// the bare `row.<field>`, matching `opBus_row_BinaryAdd`.
    #[test]
    fn clean_renderer_folds_add_zero() {
        let air = Air {
            expressions: vec![add(witness(0), constant(vec![]))],
            ..Default::default()
        };
        let pilout = PilOut::default();
        let mut map = HashMap::new();
        map.insert(0u32, "a_0".to_string());
        let r = CleanExprRenderer {
            pilout: &pilout,
            air: &air,
            col_to_field: &map,
        };
        assert_eq!(r.render_by_idx(0).unwrap(), "row.a_0");
    }

    /// `cell * 1` folds; a genuine product is preserved.
    #[test]
    fn clean_renderer_folds_mul_identity_not_product() {
        let mut map = HashMap::new();
        map.insert(0u32, "a_0".to_string());
        map.insert(1u32, "b_0".to_string());
        let pilout = PilOut::default();

        let air1 = Air {
            expressions: vec![mul(witness(0), constant(vec![1]))],
            ..Default::default()
        };
        let r1 = CleanExprRenderer { pilout: &pilout, air: &air1, col_to_field: &map };
        assert_eq!(r1.render_by_idx(0).unwrap(), "row.a_0");

        let air2 = Air {
            expressions: vec![mul(witness(0), witness(1))],
            ..Default::default()
        };
        let r2 = CleanExprRenderer { pilout: &pilout, air: &air2, col_to_field: &map };
        assert_eq!(r2.render_by_idx(0).unwrap(), "(row.a_0 * row.b_0)");
    }

    /// A stage-1 witness column with no named row field is a hard error —
    /// the row struct cannot reference it.
    #[test]
    fn clean_renderer_rejects_unnamed_column() {
        let air = Air {
            expressions: vec![add(witness(5), constant(vec![1]))],
            ..Default::default()
        };
        let pilout = PilOut::default();
        let map = HashMap::new();
        let r = CleanExprRenderer { pilout: &pilout, air: &air, col_to_field: &map };
        assert!(r.render_by_idx(0).is_err());
    }
}
