//! Public-I/O provenance from the compiled GLOBAL expression boundary.
//!
//! Debug hints identify the public tuples, but are never their proof: every
//! tuple is linked to a denominator in the actual cleared GLOBAL constraint,
//! and every signed numerator is checked against that constraint in Lean.
use std::fmt::Write as _;

use anyhow::{anyhow, bail, Result};
use crate::pilout::{self, global_expression, global_operand, hint_field, operand, HintField, PilOut};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Constant(String), Challenge(u32, u32), ProofValue(u32, u32),
    AirGroupValue(u32, u32), PublicValue(u32), PublicTableValue(u32),
    PublicTableColumn(u32, u32), Ref(u32),
    Add(Box<Expr>, Box<Expr>), Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>), Neg(Box<Expr>),
}

fn constant(bytes: &[u8]) -> Expr { Expr::Constant(crate::format_basefield(bytes)) }
fn global_operand(value: &pilout::GlobalOperand) -> Result<Expr> {
    use global_operand::Operand::*;
    Ok(match value.operand.as_ref().ok_or_else(|| anyhow!("empty GLOBAL operand"))? {
        Constant(x) => constant(&x.value),
        Challenge(x) => Expr::Challenge(x.stage, x.idx),
        ProofValue(x) => Expr::ProofValue(x.stage, x.idx),
        AirGroupValue(x) => Expr::AirGroupValue(x.air_group_id, x.idx),
        PublicValue(x) => Expr::PublicValue(x.idx),
        PublicTableAggregatedValue(x) => Expr::PublicTableValue(x.idx),
        PublicTableColumn(x) => Expr::PublicTableColumn(x.idx, x.col_idx),
        Expression(x) => Expr::Ref(x.idx),
    })
}
fn hint_operand(value: &pilout::Operand) -> Result<Expr> {
    use operand::Operand::*;
    Ok(match value.operand.as_ref().ok_or_else(|| anyhow!("empty global hint operand"))? {
        Constant(x) => constant(&x.value),
        Challenge(x) => Expr::Challenge(x.stage, x.idx),
        ProofValue(x) => Expr::ProofValue(x.stage, x.idx),
        PublicValue(x) => Expr::PublicValue(x.idx),
        Expression(x) => Expr::Ref(x.idx),
        _ => bail!("unsupported operand at GLOBAL hint boundary"),
    })
}
fn expression(value: &pilout::GlobalExpression) -> Result<Expr> {
    use global_expression::Operation::*;
    let required = |x: &Option<pilout::GlobalOperand>| global_operand(x.as_ref().ok_or_else(|| anyhow!("missing GLOBAL operand"))?);
    Ok(match value.operation.as_ref().ok_or_else(|| anyhow!("empty GLOBAL expression"))? {
        Add(x) => Expr::Add(Box::new(required(&x.lhs)?), Box::new(required(&x.rhs)?)),
        Sub(x) => Expr::Sub(Box::new(required(&x.lhs)?), Box::new(required(&x.rhs)?)),
        Mul(x) => Expr::Mul(Box::new(required(&x.lhs)?), Box::new(required(&x.rhs)?)),
        Neg(x) => Expr::Neg(Box::new(required(&x.value)?)),
    })
}
fn head<'a>(mut value: &'a Expr, expressions: &'a [Expr]) -> Result<&'a Expr> {
    let mut fuel = expressions.len() + 1;
    while let Expr::Ref(index) = value {
        if fuel == 0 { bail!("cyclic GLOBAL expression reference"); }
        fuel -= 1;
        value = expressions.get(*index as usize).ok_or_else(|| anyhow!("GLOBAL reference {index} out of bounds"))?;
    }
    Ok(value)
}
fn flatten(value: &Expr, expressions: &[Expr], multiplication: bool) -> Result<Vec<Expr>> {
    let value = head(value, expressions)?;
    let pair = match value {
        Expr::Mul(a,b) if multiplication => Some((a,b)),
        Expr::Add(a,b) if !multiplication => Some((a,b)),
        _ => None,
    };
    if let Some((a,b)) = pair {
        let mut result = flatten(a, expressions, multiplication)?;
        result.extend(flatten(b, expressions, multiplication)?);
        Ok(result)
    } else { Ok(vec![value.clone()]) }
}
fn normalize(value: &Expr, expressions: &[Expr]) -> Result<Expr> {
    let zero = Expr::Constant("0".into());
    Ok(match head(value, expressions)? {
        Expr::Add(a,b) => {
            let a = normalize(a, expressions)?; let b = normalize(b, expressions)?;
            if a == zero { b } else if b == zero { a } else { Expr::Add(Box::new(a), Box::new(b)) }
        },
        Expr::Mul(a,b) => {
            let a = normalize(a, expressions)?; let b = normalize(b, expressions)?;
            if a == zero || b == zero { zero } else { Expr::Mul(Box::new(a), Box::new(b)) }
        },
        Expr::Sub(a,b) => Expr::Sub(Box::new(normalize(a, expressions)?),Box::new(normalize(b, expressions)?)),
        Expr::Neg(a) => Expr::Neg(Box::new(normalize(a, expressions)?)),
        x => x.clone(),
    })
}
fn lean(value: &Expr) -> String {
    match value {
        Expr::Constant(n) => format!("(.constant {n})"),
        Expr::Challenge(s,i) => format!("(.challenge {s} {i})"),
        Expr::ProofValue(s,i) => format!("(.proofValue {s} {i})"),
        Expr::AirGroupValue(g,i) => format!("(.airGroupValue {g} {i})"),
        Expr::PublicValue(i) => format!("(.publicValue {i})"),
        Expr::PublicTableValue(i) => format!("(.publicTableValue {i})"),
        Expr::PublicTableColumn(t,c) => format!("(.publicTableColumn {t} {c})"),
        Expr::Ref(i) => format!("sourceExpr_{i}"),
        Expr::Add(a,b) => format!("(.add {} {})",lean(a),lean(b)),
        Expr::Sub(a,b) => format!("(.sub {} {})",lean(a),lean(b)),
        Expr::Mul(a,b) => format!("(.mul {} {})",lean(a),lean(b)),
        Expr::Neg(a) => format!("(.neg {})",lean(a)),
    }
}
fn lean_list(values: &[Expr]) -> String { format!("[{}]",values.iter().map(lean).collect::<Vec<_>>().join(", ")) }
fn array(field: &HintField) -> Result<&[HintField]> {
    match field.value.as_ref() { Some(hint_field::Value::HintFieldArray(a)) => Ok(&a.hint_fields), _ => bail!("expected global hint array") }
}
fn field<'a>(fields: &'a [HintField], name: &str) -> Result<&'a HintField> {
    fields.iter().find(|f| f.name.as_deref() == Some(name)).ok_or_else(|| anyhow!("missing global hint field {name}"))
}
fn operand_field(field: &HintField) -> Result<Expr> {
    match field.value.as_ref() { Some(hint_field::Value::Operand(o)) => hint_operand(o), _ => bail!("expected global hint operand") }
}
fn natural(value: &Expr) -> Result<u32> {
    match value { Expr::Constant(n) => Ok(n.parse()?), _ => bail!("expected natural constant at global emission boundary") }
}

pub(crate) fn render(pilout: &PilOut) -> Result<String> {
    let expressions = pilout.expressions.iter().map(expression).collect::<Result<Vec<_>>>()?;
    // Requiring a topological graph makes generated definitions acyclic too.
    fn refs_before(e: &Expr, bound: usize) -> bool {
        match e {
            Expr::Ref(i) => (*i as usize) < bound,
            Expr::Add(a,b) | Expr::Sub(a,b) | Expr::Mul(a,b) => refs_before(a,bound) && refs_before(b,bound),
            Expr::Neg(a) => refs_before(a,bound), _ => true,
        }
    }
    for (i,e) in expressions.iter().enumerate() {
        if !refs_before(e,i) { bail!("GLOBAL expression {i} is not topological"); }
    }
    let input = pilout.symbols.iter().find(|s| s.name == "inputs" && s.r#type == pilout::SymbolType::PublicValue as i32)
        .ok_or_else(|| anyhow!("missing compiled public inputs symbol"))?;
    let rom = pilout.symbols.iter().find(|s| s.name == "rom_root" && s.r#type == pilout::SymbolType::PublicValue as i32)
        .ok_or_else(|| anyhow!("missing compiled rom_root symbol"))?;
    if input.lengths.len() != 1 || rom.lengths.len() != 1 { bail!("public symbol shape changed"); }
    let mut tuples = Vec::new();
    let mut arity = None;
    for hint in &pilout.hints {
        if hint.name != "gsum_debug_data_global" && hint.name != "gsum_debug_data" { continue; }
        let Some(outer) = hint.hint_fields.first() else { continue; };
        let fields = array(outer)?;
        let Ok(bus_field) = field(fields,"busid") else { continue; };
        if natural(&operand_field(bus_field)?)? != 5000 { continue; }
        let slot_fields = array(field(fields,"expressions")?)?;
        if hint.name == "gsum_debug_data" {
            if hint.air_group_id == Some(0) && hint.air_id.and_then(|id| pilout.air_groups.first()?.airs.get(id as usize)).and_then(|a| a.name.as_deref()) == Some("Main") {
                arity = Some(slot_fields.len());
            }
            continue;
        }
        if hint.air_id.is_some() { bail!("GLOBAL hint unexpectedly attached to an AIR"); }
        let slots = slot_fields.iter().map(operand_field).collect::<Result<Vec<_>>>()?;
        let proves = natural(&operand_field(field(fields,"type_piop")?)?)?;
        let multiplicity = normalize(&operand_field(field(fields,"num_reps")?)?, &expressions)?;
        let bus = normalize(&operand_field(bus_field)?, &expressions)?;
        let slots = slots.iter().map(|e| normalize(e,&expressions)).collect::<Result<Vec<_>>>()?;
        tuples.push((bus, slots, proves, multiplicity));
    }
    let arity = arity.ok_or_else(|| anyhow!("missing compiled Main operation-bus schema"))?;
    // The current GLOBAL PIOP is one cleared direct sum. No debugLine parsing.
    if pilout.constraints.len() != 1 { bail!("GLOBAL constraint family changed"); }
    let root = Expr::Ref(pilout.constraints[0].expression_idx.as_ref().ok_or_else(|| anyhow!("missing GLOBAL root"))?.idx);
    let summands = flatten(&root,&expressions,false)?;
    let accumulator = summands.first().ok_or_else(|| anyhow!("empty GLOBAL sum"))?;
    let accumulator_factors = flatten(accumulator,&expressions,true)?;
    let (accumulator_value,denominators) = accumulator_factors.split_first().ok_or_else(|| anyhow!("empty GLOBAL accumulator product"))?;
    if denominators.len()+1 != summands.len() { bail!("GLOBAL cleared sum dimension mismatch"); }
    let mut coefficients = Vec::new();
    for (i,term) in summands[1..].iter().enumerate() {
        let factors = flatten(term,&expressions,true)?;
        let others = denominators.iter().enumerate().filter(|(j,_)| *j != i).map(|(_,d)| d.clone()).collect::<Vec<_>>();
        if !factors.ends_with(&others) { bail!("GLOBAL term {i} is not its signed omitted-denominator product"); }
        coefficients.push(factors[..factors.len()-others.len()].to_vec());
    }
    let alpha = Expr::Challenge(2,0); let gamma = Expr::Challenge(2,1);
    let normalized_denominators = denominators.iter()
        .map(|d| normalize(d, &expressions)).collect::<Result<Vec<_>>>()?;
    let mut linked = Vec::new();
    for (bus,slots,proves,mult) in &tuples {
        let mut mixed = Expr::Constant("0".into());
        for slot in slots.iter().rev() {
            mixed = normalize(&Expr::Add(Box::new(Expr::Mul(Box::new(mixed),Box::new(alpha.clone()))),Box::new(slot.clone())),&expressions)?;
        }
        mixed = normalize(&Expr::Add(Box::new(Expr::Mul(Box::new(mixed),Box::new(alpha.clone()))),Box::new(bus.clone())),&expressions)?;
        let denominator = Expr::Add(Box::new(mixed),Box::new(gamma.clone()));
        let positions = normalized_denominators.iter().enumerate()
            .filter_map(|(i,d)| (d == &denominator).then_some(i)).collect::<Vec<_>>();
        if positions.len()!=1 { bail!("public tuple has no unique actual GLOBAL denominator"); }
        let position=positions[0];
        // Unit proves has a +1 numerator, represented by the empty product.
        if *proves != 1 || *mult != Expr::Constant("1".into()) || !coefficients[position].is_empty() {
            bail!("public tuple is not a positive unit GLOBAL emission");
        }
        if linked.contains(&position) { bail!("two public hints use the same GLOBAL summand"); }
        linked.push(position);
    }
    let mut operation_positions = Vec::new();
    for (i,d) in normalized_denominators.iter().enumerate() {
        let Expr::Add(mixed,gamma) = d else { bail!("nonstandard GLOBAL denominator {i}"); };
        if gamma.as_ref() != &Expr::Challenge(2,1) { bail!("GLOBAL gamma changed at denominator {i}"); }
        let bus = match mixed.as_ref() {
            Expr::Add(_,bus) => natural(bus)?,
            bus @ Expr::Constant(_) => natural(bus)?,
            _ => bail!("GLOBAL bus tag is not a compiled constant at denominator {i}"),
        };
        if bus == 5000 { operation_positions.push(i); }
    }
    if operation_positions != linked { bail!("unaccounted or reordered actual GLOBAL operation-bus emission"); }
    let mut out = String::from("import Mathlib\n\nnamespace Extraction.PublicIo\n\ninductive Expr where\n  | constant : Nat → Expr\n  | challenge : Nat → Nat → Expr\n  | proofValue : Nat → Nat → Expr\n  | airGroupValue : Nat → Nat → Expr\n  | publicValue : Nat → Expr\n  | publicTableValue : Nat → Expr\n  | publicTableColumn : Nat → Nat → Expr\n  | add : Expr → Expr → Expr\n  | sub : Expr → Expr → Expr\n  | mul : Expr → Expr → Expr\n  | neg : Expr → Expr\n  deriving DecidableEq, Repr, Inhabited\n\ndef flattenAdd : Expr → List Expr\n  | .add a b => flattenAdd a ++ flattenAdd b\n  | e => [e]\ndef flattenMul : Expr → List Expr\n  | .mul a b => flattenMul a ++ flattenMul b\n  | e => [e]\ndef normalize : Expr → Expr\n  | .add a b => match normalize a, normalize b with\n    | .constant 0, b => b\n    | a, .constant 0 => a\n    | a, b => .add a b\n  | .mul a b => match normalize a, normalize b with\n    | .constant 0, _ => .constant 0\n    | _, .constant 0 => .constant 0\n    | a, b => .mul a b\n  | .sub a b => .sub (normalize a) (normalize b)\n  | .neg a => .neg (normalize a)\n  | e => e\ndef mix (bus alpha : Expr) (slots : List Expr) : Expr :=\n  normalize (.add (.mul (slots.foldr (fun slot acc => .add (.mul acc alpha) slot) (.constant 0)) alpha) bus)\n\n");
    writeln!(out,"def publicCellCount : Nat := {}\ndef inputBase : Nat := {}\ndef inputCellCount : Nat := {}\ndef romRootBase : Nat := {}\ndef romRootCellCount : Nat := {}\ndef operationArity : Nat := {arity}\n",pilout.num_public_values,input.id,input.lengths[0],rom.id,rom.lengths[0]).unwrap();
    for (i,e) in expressions.iter().enumerate() { writeln!(out,"def sourceExpr_{i} : Expr := {}",lean(e)).unwrap(); }
    writeln!(out,"\ndef sourceConstraint_0 : Expr := {}\ndef sourceAccumulator : Expr := {}\ndef sourceAccumulatorValue : Expr := {}\ndef sourceDenominators : List Expr := {}",lean(&root),lean(accumulator),lean(accumulator_value),lean_list(denominators)).unwrap();
    writeln!(out,"def sourceTerms : List Expr := {}\ntheorem source_terms : flattenAdd sourceConstraint_0 = sourceAccumulator :: sourceTerms := by rfl\ntheorem source_accumulator_factors : flattenMul sourceAccumulator = sourceAccumulatorValue :: sourceDenominators := by rfl",lean_list(&summands[1..])).unwrap();
    for (i,term) in summands[1..].iter().enumerate() {
        writeln!(out,"theorem source_term_{i}_factors : flattenMul {} = {} ++ sourceDenominators.eraseIdx {i} := by rfl",lean(term),lean_list(&coefficients[i])).unwrap();
    }
    writeln!(out,"\nstructure Emission where\n  bus : Expr\n  slots : List Expr\n  proves : Nat\n  multiplicity : Expr\n  termIndex : Nat\n  deriving DecidableEq, Repr, Inhabited\n\ndef publicEmissions : List Emission := [").unwrap();
    for ((bus,slots,proves,mult),position) in tuples.iter().zip(&linked) {
        writeln!(out,"  ⟨{}, {}, {proves}, {}, {position}⟩,",lean(bus),lean_list(slots),lean(mult)).unwrap();
    }
    out.push_str("]\n");
    for (i,position) in linked.iter().enumerate() {
        writeln!(out,"theorem public_emission_{i}_denominator : normalize (sourceDenominators[{position}]!) = .add (mix (publicEmissions[{i}]!).bus (.challenge 2 0) (publicEmissions[{i}]!).slots) (.challenge 2 1) := by rfl\ntheorem public_emission_{i}_positive_unit : flattenMul (sourceTerms[{position}]!) = sourceDenominators.eraseIdx {position} := by rfl").unwrap();
    }
    out.push_str("\ntheorem publicEmissions_linked (i : Fin publicEmissions.length) :\n  let e := publicEmissions[i]\n  normalize (sourceDenominators[e.termIndex]!) = .add (mix e.bus (.challenge 2 0) e.slots) (.challenge 2 1) ∧\n  flattenMul (sourceTerms[e.termIndex]!) = sourceDenominators.eraseIdx e.termIndex := by\n  fin_cases i <;> constructor <;> rfl\n");
    out.push_str("\ndef denominatorBus (e : Expr) : Option Nat :=\n  match normalize e with\n  | .add (.add _ (.constant bus)) (.challenge 2 1) => some bus\n  | .add (.constant bus) (.challenge 2 1) => some bus\n  | _ => none\n\ndef sourceOperationTermIndices : List Nat :=\n  sourceDenominators.zipIdx.filterMap fun p =>\n    if denominatorBus p.1 = some 5000 then some p.2 else none\n\ntheorem source_denominator_bus_complete :\n  none ∉ sourceDenominators.map denominatorBus := by decide\n\ntheorem source_operation_emissions_complete :\n  sourceOperationTermIndices = publicEmissions.map Emission.termIndex := by decide\n");
    out.push_str("\nend Extraction.PublicIo\n");
    Ok(out)
}
