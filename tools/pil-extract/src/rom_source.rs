//! Exact Rom source projection, including typed custom-commit references.
//! This deliberately does not extend the legacy Extraction.Circuit interface.
use anyhow::{anyhow, bail, Result};
use std::fmt::Write;
use crate::pilout::{Air, PilOut, Operand, HintField, hint_field,
    expression::Operation, operand::Operand as OperandKind,
    constraint::Constraint as ConstraintKind};

struct Renderer<'a> { air: &'a Air, active: Vec<usize> }
impl Renderer<'_> {
    fn expression(&mut self, index: usize) -> Result<String> {
        if self.active.contains(&index) { bail!("cyclic ROM expression {index}"); }
        let air = self.air;
        let expression = air.expressions.get(index)
            .ok_or_else(|| anyhow!("missing ROM expression {index}"))?;
        self.active.push(index);
        let result = match expression.operation.as_ref()
            .ok_or_else(|| anyhow!("empty ROM expression {index}"))? {
            Operation::Add(x) => Ok(format!("({} + {})", self.operand(x.lhs.as_ref())?, self.operand(x.rhs.as_ref())?)),
            Operation::Sub(x) => Ok(format!("({} - {})", self.operand(x.lhs.as_ref())?, self.operand(x.rhs.as_ref())?)),
            Operation::Mul(x) => Ok(format!("({} * {})", self.operand(x.lhs.as_ref())?, self.operand(x.rhs.as_ref())?)),
            Operation::Neg(x) => Ok(format!("(-{})", self.operand(x.value.as_ref())?)),
        };
        self.active.pop();
        result
    }
    fn operand(&mut self, operand: Option<&Operand>) -> Result<String> {
        match operand.and_then(|x| x.operand.as_ref()).ok_or_else(|| anyhow!("empty ROM operand"))? {
            OperandKind::Constant(x) => Ok(crate::format_basefield(&x.value)),
            OperandKind::Expression(x) => self.expression(x.idx as usize),
            OperandKind::CustomCol(x) => Ok(format!("(source.custom {} {} {} row ({}))", x.commit_id, x.stage, x.col_idx, x.row_offset)),
            OperandKind::WitnessCol(x) => Ok(format!("(source.witness {} {} row ({}))", x.stage, x.col_idx, x.row_offset)),
            OperandKind::FixedCol(x) => Ok(format!("(source.fixed {} row ({}))", x.idx, x.row_offset)),
            OperandKind::Challenge(x) => Ok(format!("(source.challenge {} {})", x.stage, x.idx)),
            OperandKind::AirValue(x) => Ok(format!("(source.airValue {})", x.idx)),
            OperandKind::AirGroupValue(x) => Ok(format!("(source.airGroupValue {})", x.idx)),
            other => bail!("unsupported ROM source operand {other:?}"),
        }
    }
}
fn field<'a>(fields: &'a [HintField], name: &str) -> Result<&'a hint_field::Value> {
    fields.iter().find(|field| field.name.as_deref() == Some(name))
        .and_then(|field| field.value.as_ref()).ok_or_else(|| anyhow!("missing ROM hint field {name}"))
}
fn array(value: &hint_field::Value) -> Result<&[HintField]> {
    match value { hint_field::Value::HintFieldArray(x) => Ok(&x.hint_fields), _ => bail!("ROM hint field is not an array") }
}
fn operand(value: &hint_field::Value) -> Result<&Operand> {
    match value { hint_field::Value::Operand(x) => Ok(x), _ => bail!("ROM hint field is not an operand") }
}
fn lean_string(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
        .replace('\n', "\\n").replace('\r', "\\r").replace('\t', "\\t")
}

pub fn render(pilout: &PilOut) -> Result<String> {
    let hit = crate::find_air(pilout, "Rom")?;
    let air = hit.air;
    let mut renderer = Renderer { air, active: Vec::new() };
    let mut out = String::from(r#"import Mathlib.Algebra.Field.Defs

/-! Generated from the Rom AIR and its lookup hint. Custom commitment identifiers,
stages, columns and signed rotations are retained, never decoded from Debug text.
This view does NOT establish public-root authentication or image-layout binding.
Signed rotations are interpreted by the source view, without Nat subtraction.
-/
namespace Extraction.RomSource

structure CommittedSource (F : Type) where
  custom : Nat → Nat → Nat → Int → Int → F
  witness : Nat → Nat → Int → Int → F
  fixed : Nat → Int → Int → F
  challenge : Nat → Nat → F
  airValue : Nat → F
  airGroupValue : Nat → F

variable {F : Type} [Field F]

"#);
    for (index, constraint) in air.constraints.iter().enumerate() {
        let kind = constraint.constraint.as_ref().ok_or_else(|| anyhow!("empty ROM constraint {index}"))?;
        let (expression, suffix) = match kind {
            ConstraintKind::EveryRow(x) => (x.expression_idx.as_ref(), "every_row"),
            ConstraintKind::FirstRow(x) => (x.expression_idx.as_ref(), "first_row"),
            ConstraintKind::LastRow(x) => (x.expression_idx.as_ref(), "last_row"),
            ConstraintKind::EveryFrame(_) => bail!("ROM EveryFrame requires explicit domain emission"),
        };
        let expression = expression.ok_or_else(|| anyhow!("ROM constraint {index} has no expression"))?;
        writeln!(out, "def polynomial_{index} (source : CommittedSource F) (row : Int) : F :=\n  {}\n", renderer.expression(expression.idx as usize)?)?;
        writeln!(out, "def sourceConstraint_{index}_{suffix} (source : CommittedSource F) (row : Int) : Prop :=\n  polynomial_{index} source row = 0\n")?;
    }
    writeln!(out, "def numRowsLog2 : Nat := {}\n",
        air.num_rows.ok_or_else(|| anyhow!("ROM AIR has no physical row count"))?)?;
    let mut commits = Vec::with_capacity(air.custom_commits.len());
    for (id, commit) in air.custom_commits.iter().enumerate() {
        let widths = commit.stage_widths.iter().map(u32::to_string).collect::<Vec<_>>().join(", ");
        let publics = commit.public_values.iter().map(|value| value.idx.to_string()).collect::<Vec<_>>().join(", ");
        commits.push(format!("({id}, [{widths}], [{publics}])"));
    }
    writeln!(out, "def commitments : List (Nat × List Nat × List Nat) := [{}]\n", commits.join(", "))?;
    let hints: Vec<_> = pilout.hints.iter().filter(|hint| hint.name == "gsum_debug_data"
        && hint.air_group_id == Some(hit.airgroup_idx as u32)
        && hint.air_id == Some(hit.air_idx as u32)).collect();
    if hints.len() != 1 { bail!("expected one ROM lookup hint, found {}", hints.len()); }
    let fields = array(hints[0].hint_fields.first().and_then(|x| x.value.as_ref())
        .ok_or_else(|| anyhow!("empty ROM hint"))?)?;
    for (definition, name) in [("busId", "busid"), ("providerKind", "type_piop"), ("multiplicity", "num_reps")] {
        writeln!(out, "def {definition} (source : CommittedSource F) (row : Int) : F :=\n  {}\n", renderer.operand(Some(operand(field(fields, name)?)?))?)?;
    }
    let slots = array(field(fields, "expressions")?)?;
    let names = array(field(fields, "name_exprs")?)?;
    if slots.len() != names.len() { bail!("ROM hint slot/name length mismatch"); }
    let piop = match field(fields, "name_piop")? {
        hint_field::Value::StringValue(value) => value,
        _ => bail!("ROM name_piop is not a string"),
    };
    writeln!(out, "def piop : String := \"{}\"\n", lean_string(piop))?;
    let slot_names = names.iter().map(|name| match name.value.as_ref() {
        Some(hint_field::Value::StringValue(value)) => Ok(format!("\"{}\"", lean_string(value))),
        _ => bail!("ROM slot name is not a string"),
    }).collect::<Result<Vec<_>>>()?;
    writeln!(out, "def slotNames : List String := [{}]\n", slot_names.join(", "))?;
    let mut expressions = Vec::with_capacity(slots.len());
    for slot in slots {
        expressions.push(renderer.operand(Some(operand(slot.value.as_ref().ok_or_else(|| anyhow!("empty ROM slot"))?)?))?);
    }
    writeln!(out, "def lookupTuple (source : CommittedSource F) (row : Int) : List F :=\n  [{}]\n", expressions.join(", "))?;
    out.push_str("end Extraction.RomSource\n");
    Ok(out)
}
