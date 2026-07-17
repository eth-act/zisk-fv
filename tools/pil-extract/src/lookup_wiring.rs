//! Lossless, constraint-linked gsum lookup wiring extraction.
//!
//! The legacy `bus-emissions` renderer intentionally targets an `F`-valued
//! interface and therefore cannot represent challenge-mixed operands.  This
//! module has a different contract: it emits a closed syntax tree and only
//! publishes a hint tuple after an extracted constraint is definitionally the
//! corresponding standard PIOP template.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use anyhow::{anyhow, bail, Result};

use crate::{
    const_operand_to_u64, format_basefield, hint_field_by_name,
    pilout::{
        constraint::Constraint as ConstraintKind, expression::Operation as ExprOp, hint_field,
        operand::Operand as OperandKind, Air, Constraint, Hint, Operand, PilOut,
    },
};

const GOLDILOCKS_NEG_ONE: &str = "18446744069414584320";

/// AIRs for which `nix/extracted-lean.nix` currently emits a constraint file.
/// The manifest includes all AIRs and calls this out explicitly rather than
/// silently treating a missing generated file as an empty constraint family.
const GENERATED_CONSTRAINT_AIRS: &[&str] = &[
    "Main",
    "Mem",
    "MemAlign",
    "MemAlignByte",
    "MemAlignReadByte",
    "MemAlignWriteByte",
    "Arith",
    "Binary",
    "BinaryAdd",
    "BinaryExtension",
];

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Ast {
    Constant(String),
    Witness {
        stage: u32,
        column: u32,
        row_offset: i32,
    },
    Fixed {
        column: u32,
        row_offset: i32,
    },
    Challenge {
        stage: u32,
        index: u32,
    },
    AirValue(u32),
    AirGroupValue(u32),
    Opaque {
        kind: String,
        payload: String,
    },
    Add(Box<Ast>, Box<Ast>),
    Sub(Box<Ast>, Box<Ast>),
    Mul(Box<Ast>, Box<Ast>),
    Neg(Box<Ast>),
}

impl Ast {
    fn constant(value: impl Into<String>) -> Self {
        Self::Constant(value.into())
    }

    fn add(lhs: Self, rhs: Self) -> Self {
        Self::Add(Box::new(lhs), Box::new(rhs))
    }

    fn sub(lhs: Self, rhs: Self) -> Self {
        Self::Sub(Box::new(lhs), Box::new(rhs))
    }

    fn mul(lhs: Self, rhs: Self) -> Self {
        Self::Mul(Box::new(lhs), Box::new(rhs))
    }

    fn neg(value: Self) -> Self {
        Self::Neg(Box::new(value))
    }
}

#[derive(Clone)]
struct Slot {
    name: String,
    value: Ast,
}

#[derive(Clone)]
struct HintData {
    index: usize,
    piop: String,
    proves: bool,
    bus_id: Ast,
    multiplicity: Ast,
    slots: Vec<Slot>,
}

#[derive(Clone, Copy)]
enum LinkShape {
    Direct,
    Cluster2,
}

struct LinkedConstraint {
    constraint_index: usize,
    constraint: Ast,
    accumulator: Ast,
    alpha: Ast,
    gamma: Ast,
    hints: Vec<HintData>,
    shape: LinkShape,
}

#[derive(Clone)]
struct MixCandidate {
    hint: usize,
    alpha: Ast,
    gamma: Ast,
}

struct AirManifest {
    group_index: usize,
    air_index: usize,
    group_name: String,
    air_name: String,
    emitted_constraint_file: bool,
    mixed_constraint_count: usize,
    unlinked_mixed_constraint_count: usize,
    unlinked_constraints: Vec<(usize, Ast)>,
    gsum_hint_count: usize,
    links: Vec<LinkedConstraint>,
}

struct AstResolver<'a> {
    air: &'a Air,
    expressions: HashMap<usize, Ast>,
}

impl<'a> AstResolver<'a> {
    fn new(air: &'a Air) -> Self {
        Self {
            air,
            expressions: HashMap::new(),
        }
    }

    fn expression(&mut self, index: usize) -> Result<Ast> {
        if let Some(value) = self.expressions.get(&index) {
            return Ok(value.clone());
        }
        let operation = self
            .air
            .expressions
            .get(index)
            .ok_or_else(|| anyhow!("expression index {index} is out of range"))?
            .operation
            .clone()
            .ok_or_else(|| anyhow!("expression {index} has no operation"))?;
        let value = match operation {
            ExprOp::Add(value) => Ast::add(
                self.operand(value.lhs.as_ref())?,
                self.operand(value.rhs.as_ref())?,
            ),
            ExprOp::Sub(value) => Ast::sub(
                self.operand(value.lhs.as_ref())?,
                self.operand(value.rhs.as_ref())?,
            ),
            ExprOp::Mul(value) => Ast::mul(
                self.operand(value.lhs.as_ref())?,
                self.operand(value.rhs.as_ref())?,
            ),
            ExprOp::Neg(value) => Ast::neg(self.operand(value.value.as_ref())?),
        };
        self.expressions.insert(index, value.clone());
        Ok(value)
    }

    fn operand(&mut self, operand: Option<&Operand>) -> Result<Ast> {
        let operand = operand.ok_or_else(|| anyhow!("operand is missing"))?;
        let kind = operand
            .operand
            .as_ref()
            .ok_or_else(|| anyhow!("operand kind is missing"))?;
        Ok(match kind {
            OperandKind::Constant(value) => Ast::constant(format_basefield(&value.value)),
            OperandKind::WitnessCol(value) => Ast::Witness {
                stage: value.stage,
                column: value.col_idx,
                row_offset: value.row_offset,
            },
            OperandKind::FixedCol(value) => Ast::Fixed {
                column: value.idx,
                row_offset: value.row_offset,
            },
            OperandKind::Challenge(value) => Ast::Challenge {
                stage: value.stage,
                index: value.idx,
            },
            OperandKind::AirValue(value) => Ast::AirValue(value.idx),
            OperandKind::AirGroupValue(value) => Ast::AirGroupValue(value.idx),
            OperandKind::Expression(value) => self.expression(value.idx as usize)?,
            OperandKind::PeriodicCol(value) => Ast::Opaque {
                kind: "periodic".to_string(),
                payload: format!("{value:?}"),
            },
            OperandKind::ProofValue(value) => Ast::Opaque {
                kind: "proof".to_string(),
                payload: format!("{value:?}"),
            },
            OperandKind::PublicValue(value) => Ast::Opaque {
                kind: "public".to_string(),
                payload: format!("{value:?}"),
            },
            OperandKind::CustomCol(value) => Ast::Opaque {
                kind: "custom".to_string(),
                payload: format!("{value:?}"),
            },
        })
    }
}

fn expression_uses_extf(
    air: &Air,
    index: usize,
    expressions: &mut HashMap<usize, bool>,
) -> Result<bool> {
    if let Some(value) = expressions.get(&index) {
        return Ok(*value);
    }
    let operation = air
        .expressions
        .get(index)
        .ok_or_else(|| anyhow!("expression index {index} is out of range"))?
        .operation
        .clone()
        .ok_or_else(|| anyhow!("expression {index} has no operation"))?;
    let value = match operation {
        ExprOp::Add(value) => {
            operand_uses_extf(air, value.lhs.as_ref(), expressions)?
                || operand_uses_extf(air, value.rhs.as_ref(), expressions)?
        }
        ExprOp::Sub(value) => {
            operand_uses_extf(air, value.lhs.as_ref(), expressions)?
                || operand_uses_extf(air, value.rhs.as_ref(), expressions)?
        }
        ExprOp::Mul(value) => {
            operand_uses_extf(air, value.lhs.as_ref(), expressions)?
                || operand_uses_extf(air, value.rhs.as_ref(), expressions)?
        }
        ExprOp::Neg(value) => operand_uses_extf(air, value.value.as_ref(), expressions)?,
    };
    expressions.insert(index, value);
    Ok(value)
}

fn operand_uses_extf(
    air: &Air,
    operand: Option<&Operand>,
    expressions: &mut HashMap<usize, bool>,
) -> Result<bool> {
    let operand = operand.ok_or_else(|| anyhow!("operand is missing"))?;
    let kind = operand
        .operand
        .as_ref()
        .ok_or_else(|| anyhow!("operand kind is missing"))?;
    match kind {
        OperandKind::Challenge(_) | OperandKind::AirValue(_) | OperandKind::AirGroupValue(_) => Ok(true),
        OperandKind::Expression(value) => expression_uses_extf(air, value.idx as usize, expressions),
        _ => Ok(false),
    }
}

/// Render a closed Lean manifest. The generated `rfl` examples are intentional:
/// Rust finds a candidate, but the kernel also checks the exact template link.
pub(crate) fn render(pilout: &PilOut) -> Result<String> {
    let mut airs = Vec::new();
    for (group_index, group) in pilout.air_groups.iter().enumerate() {
        let group_name = group.name.clone().unwrap_or_else(|| "<unnamed>".to_string());
        for (air_index, air) in group.airs.iter().enumerate() {
            airs.push(build_air_manifest(
                pilout,
                group_index,
                air_index,
                &group_name,
                air,
            )?);
        }
    }

    let mut out = String::new();
    write_prelude(&mut out);
    for air in &airs {
        write_air_status(&mut out, air)?;
    }
    for air in &airs {
        write_constraint_only_entries(&mut out, air)?;
        for link in &air.links {
            write_link(&mut out, air, link)?;
        }
    }
    out.push_str("def airStatuses : List AirStatus := [\n");
    for air in &airs {
        writeln!(out, "  airStatus_{},", ident(&air.air_name))?;
    }
    out.push_str("]\n\n");
    out.push_str("def unlinkedMixedConstraints : List ConstraintOnly := [\n");
    for air in &airs {
        for (constraint_index, _) in &air.unlinked_constraints {
            writeln!(
                out,
                "  constraintOnly_{}_{} ,",
                ident(&air.air_name),
                constraint_index
            )?;
        }
    }
    out.push_str("]\n\n");
    out.push_str("def validatedLinks : List ValidatedLink := [\n");
    for air in &airs {
        for link in &air.links {
            writeln!(
                out,
                "  link_{}_{} ,",
                ident(&air.air_name),
                link.constraint_index
            )?;
        }
    }
    out.push_str("]\n\nend Extraction.LookupWiring\n");
    Ok(out)
}

fn build_air_manifest(
    pilout: &PilOut,
    group_index: usize,
    air_index: usize,
    group_name: &str,
    air: &Air,
) -> Result<AirManifest> {
    let air_name = air.name.clone().unwrap_or_else(|| "<unnamed>".to_string());
    let emitted_constraint_file = GENERATED_CONSTRAINT_AIRS.contains(&air_name.as_str());
    let mut resolver = AstResolver::new(air);
    let mut extf_expressions = HashMap::new();
    let mut mixed_constraints = Vec::new();
    for (constraint_index, constraint) in air.constraints.iter().enumerate() {
        let expression_index = constraint_expression_index(constraint, constraint_index)?;
        if expression_uses_extf(air, expression_index, &mut extf_expressions)? {
            mixed_constraints.push((
                constraint_index,
                resolver.expression(expression_index)?,
            ));
        }
    }

    let scoped_hints: Vec<(usize, &Hint)> = pilout
        .hints
        .iter()
        .enumerate()
        .filter(|(_, hint)| {
            hint.name == "gsum_debug_data"
                && hint.air_group_id == Some(group_index as u32)
                && hint.air_id == Some(air_index as u32)
        })
        .collect();
    let gsum_hint_count = scoped_hints.len();
    let mut hints = Vec::new();
    if emitted_constraint_file {
        for (index, hint) in scoped_hints {
            hints.push(parse_hint(&mut resolver, index, hint)?);
        }
    }
    let mixed_constraint_count = mixed_constraints.len();
    let (links, unlinked_mixed_constraint_count) = if emitted_constraint_file {
        let challenges = protocol_challenges(pilout);
        find_links(&mixed_constraints, &hints, &challenges)?
    } else {
        (Vec::new(), mixed_constraint_count)
    };
    let linked_constraints: HashSet<usize> = links
        .iter()
        .map(|link| link.constraint_index)
        .collect();
    let unlinked_constraints = if emitted_constraint_file {
        mixed_constraints
            .into_iter()
            .filter(|(index, _)| !linked_constraints.contains(index))
            .collect()
    } else {
        Vec::new()
    };

    Ok(AirManifest {
        group_index,
        air_index,
        group_name: group_name.to_string(),
        emitted_constraint_file,
        air_name,
        mixed_constraint_count,
        unlinked_mixed_constraint_count,
        unlinked_constraints,
        gsum_hint_count,
        links,
    })
}

fn constraint_expression_index(constraint: &Constraint, index: usize) -> Result<usize> {
    let kind = constraint
        .constraint
        .as_ref()
        .ok_or_else(|| anyhow!("constraint #{index} is empty"))?;
    let operand = match kind {
        ConstraintKind::EveryRow(value) => value.expression_idx.as_ref(),
        ConstraintKind::FirstRow(value) => value.expression_idx.as_ref(),
        ConstraintKind::LastRow(value) => value.expression_idx.as_ref(),
        ConstraintKind::EveryFrame(value) => value.expression_idx.as_ref(),
    }
    .ok_or_else(|| anyhow!("constraint #{index} has no expression index"))?;
    Ok(operand.idx as usize)
}

fn parse_hint(resolver: &mut AstResolver<'_>, index: usize, hint: &Hint) -> Result<HintData> {
    let outer = hint
        .hint_fields
        .first()
        .ok_or_else(|| anyhow!("gsum hint #{index} has no fields"))?;
    let fields = match outer.value.as_ref() {
        Some(hint_field::Value::HintFieldArray(value)) => &value.hint_fields,
        _ => bail!("gsum hint #{index} outer field is not an array"),
    };
    let piop = match hint_field_by_name(fields, "name_piop").and_then(|field| field.value.as_ref()) {
        Some(hint_field::Value::StringValue(value)) => value.clone(),
        _ => bail!("gsum hint #{index} has no name_piop"),
    };
    let proves = hint_operand(fields, "type_piop", index)
        .and_then(|operand| const_operand_to_u64(operand).ok_or_else(|| anyhow!("type_piop is not a constant")))?
        != 0;
    let bus_id = resolver.operand(Some(hint_operand(fields, "busid", index)?))?;
    let multiplicity = resolver.operand(Some(hint_operand(fields, "num_reps", index)?))?;
    let names = hint_array(fields, "name_exprs", index)?;
    let values = hint_array(fields, "expressions", index)?;
    if names.len() != values.len() {
        bail!(
            "gsum hint #{index} names/expressions length mismatch: {} vs {}",
            names.len(),
            values.len()
        );
    }
    let mut slots = Vec::with_capacity(names.len());
    for (name, value) in names.iter().zip(values) {
        let name = match name.value.as_ref() {
            Some(hint_field::Value::StringValue(value)) => value.clone(),
            _ => bail!("gsum hint #{index} has a non-string slot name"),
        };
        let value = match value.value.as_ref() {
            Some(hint_field::Value::Operand(value)) => resolver.operand(Some(value))?,
            _ => bail!("gsum hint #{index} has a non-operand slot value"),
        };
        slots.push(Slot { name, value });
    }
    Ok(HintData {
        index,
        piop,
        proves,
        bus_id,
        multiplicity,
        slots,
    })
}

fn hint_operand<'a>(fields: &'a [crate::pilout::HintField], name: &str, index: usize) -> Result<&'a Operand> {
    match hint_field_by_name(fields, name).and_then(|field| field.value.as_ref()) {
        Some(hint_field::Value::Operand(value)) => Ok(value),
        _ => bail!("gsum hint #{index} has no operand field {name}"),
    }
}

fn hint_array<'a>(
    fields: &'a [crate::pilout::HintField],
    name: &str,
    index: usize,
) -> Result<&'a [crate::pilout::HintField]> {
    match hint_field_by_name(fields, name).and_then(|field| field.value.as_ref()) {
        Some(hint_field::Value::HintFieldArray(value)) => Ok(&value.hint_fields),
        _ => bail!("gsum hint #{index} has no array field {name}"),
    }
}

fn protocol_challenges(pilout: &PilOut) -> Vec<Ast> {
    let mut challenges = Vec::new();
    for (stage, width) in pilout.num_challenges.iter().enumerate() {
        for index in 0..*width {
            challenges.push(Ast::Challenge {
                stage: stage as u32 + 1,
                index,
            });
        }
    }
    challenges
}

fn find_links(
    constraints: &[(usize, Ast)],
    hints: &[HintData],
    challenges: &[Ast],
) -> Result<(Vec<LinkedConstraint>, usize)> {
    let mut links = Vec::new();
    let mut consumed = HashSet::new();
    let mut by_mix: HashMap<Ast, Vec<MixCandidate>> = HashMap::new();
    for (index, hint) in hints.iter().enumerate() {
        for alpha in challenges {
            for gamma in challenges {
                if alpha == gamma {
                    continue;
                }
                if let Some(mix) = std_mix(hint, alpha, gamma) {
                    by_mix.entry(normalise(mix)).or_default().push(MixCandidate {
                        hint: index,
                        alpha: alpha.clone(),
                        gamma: gamma.clone(),
                    });
                }
            }
        }
    }
    for (constraint_index, constraint) in constraints {
        let pair_matches = pair_matches(constraint, hints, &consumed, &by_mix);
        if pair_matches.len() > 1 {
            bail!(
                "constraint #{constraint_index} has {} possible two-hint template links",
                pair_matches.len()
            );
        }
        if let Some((left, right, accumulator, alpha, gamma)) = pair_matches.into_iter().next() {
            consumed.insert(left);
            consumed.insert(right);
            links.push(LinkedConstraint {
                constraint_index: *constraint_index,
                constraint: constraint.clone(),
                accumulator,
                alpha,
                gamma,
                hints: vec![hints[left].clone(), hints[right].clone()],
                shape: LinkShape::Cluster2,
            });
            continue;
        }

        let single_matches = single_matches(constraint, hints, &consumed, &by_mix);
        if single_matches.len() > 1 {
            bail!(
                "constraint #{constraint_index} has {} possible direct template links",
                single_matches.len()
            );
        }
        if let Some((hint, accumulator, alpha, gamma)) = single_matches.into_iter().next() {
            consumed.insert(hint);
            links.push(LinkedConstraint {
                constraint_index: *constraint_index,
                constraint: constraint.clone(),
                accumulator,
                alpha,
                gamma,
                hints: vec![hints[hint].clone()],
                shape: LinkShape::Direct,
            });
        }
    }
    let unlinked = constraints.len().saturating_sub(links.len());
    Ok((links, unlinked))
}

fn single_matches(
    constraint: &Ast,
    hints: &[HintData],
    consumed: &HashSet<usize>,
    by_mix: &HashMap<Ast, Vec<MixCandidate>>,
) -> Vec<(usize, Ast, Ast, Ast)> {
    let Some(mix) = direct_mix(constraint) else {
        return Vec::new();
    };
    by_mix
        .get(mix)
        .into_iter()
        .flatten()
        .filter(|candidate| !consumed.contains(&candidate.hint))
        .filter_map(|candidate| {
            direct_accumulator(constraint, &hints[candidate.hint], &candidate.alpha, &candidate.gamma)
                .map(|accumulator| {
                    (
                        candidate.hint,
                        accumulator,
                        candidate.alpha.clone(),
                        candidate.gamma.clone(),
                    )
                })
        })
        .collect()
}

fn pair_matches(
    constraint: &Ast,
    hints: &[HintData],
    consumed: &HashSet<usize>,
    by_mix: &HashMap<Ast, Vec<MixCandidate>>,
) -> Vec<(usize, usize, Ast, Ast, Ast)> {
    let Some((left_mix, right_mix)) = cluster_mixes(constraint) else {
        return Vec::new();
    };
    let mut matches = Vec::new();
    for left in by_mix.get(left_mix).into_iter().flatten() {
        if consumed.contains(&left.hint) {
            continue;
        }
        for right in by_mix.get(right_mix).into_iter().flatten() {
            if left.hint == right.hint
                || left.alpha != right.alpha
                || left.gamma != right.gamma
                || consumed.contains(&right.hint)
            {
                continue;
            }
            if let Some(accumulator) = cluster_accumulator(
                constraint,
                &hints[left.hint],
                &hints[right.hint],
                &left.alpha,
                &left.gamma,
            ) {
                matches.push((
                    left.hint,
                    right.hint,
                    accumulator,
                    left.alpha.clone(),
                    left.gamma.clone(),
                ));
            }
        }
    }
    matches
}

fn direct_mix(constraint: &Ast) -> Option<&Ast> {
    match constraint {
        Ast::Add(lhs, _) | Ast::Sub(lhs, _) => match lhs.as_ref() {
            Ast::Mul(_, mix) => Some(mix),
            _ => None,
        },
        _ => None,
    }
}

fn cluster_mixes(constraint: &Ast) -> Option<(&Ast, &Ast)> {
    let Ast::Sub(product, _) = constraint else {
        return None;
    };
    let Ast::Mul(_, mixes) = product.as_ref() else {
        return None;
    };
    let Ast::Mul(left, right) = mixes.as_ref() else {
        return None;
    };
    Some((left, right))
}

fn direct_accumulator(constraint: &Ast, hint: &HintData, alpha: &Ast, gamma: &Ast) -> Option<Ast> {
    match (hint.proves, constraint) {
        (false, Ast::Add(lhs, rhs)) => match lhs.as_ref() {
            Ast::Mul(accumulator, _) if **rhs == normalise(hint.multiplicity.clone()) => {
                let accumulator = (**accumulator).clone();
                (normalise(direct_template(accumulator.clone(), hint, alpha, gamma)) == *constraint)
                    .then_some(accumulator)
            }
            _ => None,
        },
        (true, Ast::Sub(lhs, rhs)) => match lhs.as_ref() {
            Ast::Mul(accumulator, _) if **rhs == normalise(hint.multiplicity.clone()) => {
                let accumulator = (**accumulator).clone();
                (normalise(direct_template(accumulator.clone(), hint, alpha, gamma)) == *constraint)
                    .then_some(accumulator)
            }
            _ => None,
        },
        _ => None,
    }
}

fn cluster_accumulator(
    constraint: &Ast,
    left: &HintData,
    right: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Option<Ast> {
    let product = match constraint {
        Ast::Sub(product, _) => product.as_ref(),
        _ => return None,
    };
    let Ast::Mul(accumulator, _) = product else {
        return None;
    };
    let accumulator = (**accumulator).clone();
    (normalise(cluster_template(accumulator.clone(), left, right, alpha, gamma)) == *constraint)
        .then_some(accumulator)
}

fn std_mix(hint: &HintData, alpha: &Ast, gamma: &Ast) -> Option<Ast> {
    let mut values = hint.slots.iter().rev();
    let mut value = values.next()?.value.clone();
    for slot in values {
        value = Ast::add(Ast::mul(value, alpha.clone()), slot.value.clone());
    }
    Some(Ast::add(
        Ast::add(
            Ast::mul(value, alpha.clone()),
            hint.bus_id.clone(),
        ),
        gamma.clone(),
    ))
}

fn signed_multiplicity(hint: &HintData) -> Ast {
    if hint.proves {
        hint.multiplicity.clone()
    } else {
        field_neg(hint.multiplicity.clone())
    }
}

fn direct_template(accumulator: Ast, hint: &HintData, alpha: &Ast, gamma: &Ast) -> Ast {
    let product = Ast::mul(accumulator, std_mix(hint, alpha, gamma).expect("hint has a slot"));
    if hint.proves {
        Ast::sub(product, hint.multiplicity.clone())
    } else {
        Ast::add(product, hint.multiplicity.clone())
    }
}

fn cluster_template(
    accumulator: Ast,
    left: &HintData,
    right: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Ast {
    let left_mix = std_mix(left, alpha, gamma).expect("hint has a slot");
    let right_mix = std_mix(right, alpha, gamma).expect("hint has a slot");
    Ast::sub(
        Ast::mul(accumulator, Ast::mul(left_mix.clone(), right_mix.clone())),
        Ast::add(
            Ast::mul(signed_multiplicity(left), right_mix),
            Ast::mul(signed_multiplicity(right), left_mix),
        ),
    )
}

/// The upstream macro normalizes only neutral field syntax before emitting its
/// constraint. Keep this deliberately small: it is not an algebraic solver.
fn normalise(value: Ast) -> Ast {
    match value {
        Ast::Add(lhs, rhs) => {
            let lhs = normalise(*lhs);
            let rhs = normalise(*rhs);
            if is_zero(&rhs) {
                lhs
            } else if is_zero(&lhs) {
                rhs
            } else {
                Ast::add(lhs, rhs)
            }
        }
        Ast::Sub(lhs, rhs) => {
            let lhs = normalise(*lhs);
            let rhs = normalise(*rhs);
            if is_zero(&rhs) { lhs } else { Ast::sub(lhs, rhs) }
        }
        Ast::Mul(lhs, rhs) => {
            let lhs = normalise(*lhs);
            let rhs = normalise(*rhs);
            if is_one(&rhs) {
                lhs
            } else if is_one(&lhs) {
                rhs
            } else {
                Ast::mul(lhs, rhs)
            }
        }
        Ast::Neg(value) => Ast::neg(normalise(*value)),
        value => value,
    }
}

fn is_zero(value: &Ast) -> bool {
    matches!(value, Ast::Constant(value) if value == "0")
}

fn is_one(value: &Ast) -> bool {
    matches!(value, Ast::Constant(value) if value == "1")
}

fn field_neg(value: Ast) -> Ast {
    match value {
        Ast::Constant(value) if value == "1" => Ast::constant(GOLDILOCKS_NEG_ONE),
        value => Ast::sub(Ast::constant("0"), value),
    }
}

fn write_prelude(out: &mut String) {
    out.push_str("import Mathlib\n\n");
    out.push_str("set_option linter.all false\n\n");
    out.push_str("namespace Extraction.LookupWiring\n\n");
    out.push_str("/-!\n");
    out.push_str("Lossless, constraint-linked extraction of gsum lookup wiring.\n\n");
    out.push_str("A `ValidatedLink` contains a hint tuple only after its `constraint`\n");
    out.push_str("is definitionally equal to the standard template instantiated with\n");
    out.push_str("that tuple. Hints which have no such link are represented only by\n");
    out.push_str("their per-AIR count; their tuple payload is deliberately withheld.\n");
    out.push_str("-/\n\n");
    out.push_str("inductive Expr where\n");
    out.push_str("  | constant (value : String)\n");
    out.push_str("  | witness (stage column : Nat) (rowOffset : Int)\n");
    out.push_str("  | fixed (column : Nat) (rowOffset : Int)\n");
    out.push_str("  | challenge (stage index : Nat)\n");
    out.push_str("  | airValue (index : Nat)\n");
    out.push_str("  | airGroupValue (index : Nat)\n");
    out.push_str("  | opaque (kind payload : String)\n");
    out.push_str("  | add (lhs rhs : Expr)\n");
    out.push_str("  | sub (lhs rhs : Expr)\n");
    out.push_str("  | mul (lhs rhs : Expr)\n");
    out.push_str("  | neg (value : Expr)\n");
    out.push_str("  deriving Repr, DecidableEq\n\n");
    out.push_str("structure Slot where\n  name : String\n  value : Expr\n\n");
    out.push_str("structure HintTuple where\n");
    out.push_str("  hintIndex : Nat\n  piop : String\n  proves : Bool\n  busId : Expr\n");
    out.push_str("  multiplicity : Expr\n  slots : List Slot\n\n");
    out.push_str("inductive LinkShape where\n  | direct\n  | cluster2\n  deriving Repr, DecidableEq\n\n");
    out.push_str("structure ValidatedLink where\n");
    out.push_str("  air : String\n  constraintIndex : Nat\n  shape : LinkShape\n");
    out.push_str("  accumulator : Expr\n  alpha : Expr\n  gamma : Expr\n  constraint : Expr\n  template : Expr\n");
    out.push_str("  hints : List HintTuple\n\n");
    out.push_str("structure ConstraintOnly where\n");
    out.push_str("  air : String\n  constraintIndex : Nat\n  constraint : Expr\n\n");
    out.push_str("structure AirStatus where\n");
    out.push_str("  groupIndex : Nat\n  airIndex : Nat\n  group : String\n  air : String\n");
    out.push_str("  emittedConstraintFile : Bool\n  mixedConstraintCount : Nat\n");
    out.push_str("  unlinkedMixedConstraintCount : Nat\n  gsumHintCount : Nat\n");
    out.push_str("  validatedLinkCount : Nat\n\n");
    out.push_str("def stdMix (alpha gamma busId : Expr) (slots : List Slot) : Expr :=\n");
    out.push_str("  match slots.reverse with\n");
    out.push_str("  | [] => .add busId gamma\n");
    out.push_str("  | first :: rest =>\n");
    out.push_str("    .add (.add (.mul (rest.foldl (fun acc slot => .add (.mul acc alpha) slot.value) first.value) alpha) busId) gamma\n\n");
    out.push_str("def normalise : Expr → Expr\n");
    out.push_str("  | .add lhs rhs =>\n");
    out.push_str("    match normalise lhs, normalise rhs with\n");
    out.push_str("    | lhs, .constant \"0\" => lhs\n");
    out.push_str("    | .constant \"0\", rhs => rhs\n");
    out.push_str("    | lhs, rhs => .add lhs rhs\n");
    out.push_str("  | .sub lhs rhs =>\n");
    out.push_str("    match normalise lhs, normalise rhs with\n");
    out.push_str("    | lhs, .constant \"0\" => lhs\n");
    out.push_str("    | lhs, rhs => .sub lhs rhs\n");
    out.push_str("  | .mul lhs rhs =>\n");
    out.push_str("    match normalise lhs, normalise rhs with\n");
    out.push_str("    | lhs, .constant \"1\" => lhs\n");
    out.push_str("    | .constant \"1\", rhs => rhs\n");
    out.push_str("    | lhs, rhs => .mul lhs rhs\n");
    out.push_str("  | .neg value => .neg (normalise value)\n");
    out.push_str("  | value => value\n\n");
    out.push_str("def directTemplate (alpha gamma accumulator : Expr) (hint : HintTuple) : Expr :=\n");
    out.push_str("  if hint.proves then\n");
    out.push_str("    .sub (.mul accumulator (stdMix alpha gamma hint.busId hint.slots)) hint.multiplicity\n");
    out.push_str("  else\n");
    out.push_str("    .add (.mul accumulator (stdMix alpha gamma hint.busId hint.slots)) hint.multiplicity\n\n");
    out.push_str("def negSelector : Expr → Expr\n");
    out.push_str("  | .constant \"1\" => .constant \"18446744069414584320\"\n");
    out.push_str("  | value => .sub (.constant \"0\") value\n\n");
    out.push_str("def signedSelector (hint : HintTuple) : Expr :=\n");
    out.push_str("  if hint.proves then hint.multiplicity else negSelector hint.multiplicity\n\n");
    out.push_str("def cluster2Template (alpha gamma accumulator : Expr) (left right : HintTuple) : Expr :=\n");
    out.push_str("  let leftMix := stdMix alpha gamma left.busId left.slots\n");
    out.push_str("  let rightMix := stdMix alpha gamma right.busId right.slots\n");
    out.push_str("  .sub (.mul accumulator (.mul leftMix rightMix))\n");
    out.push_str("    (.add (.mul (signedSelector left) rightMix) (.mul (signedSelector right) leftMix))\n\n");
}

fn write_air_status(out: &mut String, air: &AirManifest) -> Result<()> {
    writeln!(out, "def airStatus_{} : AirStatus := {{", ident(&air.air_name))?;
    writeln!(out, "  groupIndex := {},", air.group_index)?;
    writeln!(out, "  airIndex := {},", air.air_index)?;
    writeln!(out, "  group := \"{}\",", lean_string(&air.group_name))?;
    writeln!(out, "  air := \"{}\",", lean_string(&air.air_name))?;
    writeln!(out, "  emittedConstraintFile := {},", air.emitted_constraint_file)?;
    writeln!(out, "  mixedConstraintCount := {},", air.mixed_constraint_count)?;
    writeln!(
        out,
        "  unlinkedMixedConstraintCount := {},",
        air.unlinked_mixed_constraint_count
    )?;
    writeln!(out, "  gsumHintCount := {},", air.gsum_hint_count)?;
    writeln!(out, "  validatedLinkCount := {}", air.links.len())?;
    out.push_str("}\n\n");
    Ok(())
}

fn write_constraint_only_entries(out: &mut String, air: &AirManifest) -> Result<()> {
    for (constraint_index, constraint) in &air.unlinked_constraints {
        writeln!(
            out,
            "def constraintOnly_{}_{} : ConstraintOnly := {{",
            ident(&air.air_name),
            constraint_index
        )?;
        writeln!(out, "  air := \"{}\",", lean_string(&air.air_name))?;
        writeln!(out, "  constraintIndex := {},", constraint_index)?;
        writeln!(out, "  constraint := {}", lean_expr(constraint))?;
        out.push_str("}\n\n");
    }
    Ok(())
}

fn write_link(out: &mut String, air: &AirManifest, link: &LinkedConstraint) -> Result<()> {
    let label = format!("{}_{}", ident(&air.air_name), link.constraint_index);
    for (index, hint) in link.hints.iter().enumerate() {
        write_hint(out, &format!("hint_{}_{}", label, index), hint)?;
    }
    writeln!(out, "def constraint_{} : Expr := {}", label, lean_expr(&link.constraint))?;
    match link.shape {
        LinkShape::Direct => writeln!(
            out,
            "def template_{} : Expr := normalise (directTemplate ({}) ({}) ({}) hint_{}_0)",
            label,
            lean_expr(&link.alpha),
            lean_expr(&link.gamma),
            lean_expr(&link.accumulator),
            label
        )?,
        LinkShape::Cluster2 => writeln!(
            out,
            "def template_{} : Expr := normalise (cluster2Template ({}) ({}) ({}) hint_{}_0 hint_{}_1)",
            label,
            lean_expr(&link.alpha),
            lean_expr(&link.gamma),
            lean_expr(&link.accumulator),
            label,
            label
        )?,
    }
    writeln!(
        out,
        "example : constraint_{} = template_{} := by rfl",
        label, label
    )?;
    writeln!(out, "def link_{} : ValidatedLink := {{", label)?;
    writeln!(out, "  air := \"{}\",", lean_string(&air.air_name))?;
    writeln!(out, "  constraintIndex := {},", link.constraint_index)?;
    writeln!(
        out,
        "  shape := .{},",
        match link.shape {
            LinkShape::Direct => "direct",
            LinkShape::Cluster2 => "cluster2",
        }
    )?;
    writeln!(out, "  accumulator := {},", lean_expr(&link.accumulator))?;
    writeln!(out, "  alpha := {},", lean_expr(&link.alpha))?;
    writeln!(out, "  gamma := {},", lean_expr(&link.gamma))?;
    writeln!(out, "  constraint := constraint_{},", label)?;
    writeln!(out, "  template := template_{},", label)?;
    writeln!(out, "  hints := [{}]", (0..link.hints.len()).map(|index| format!("hint_{}_{}", label, index)).collect::<Vec<_>>().join(", "))?;
    out.push_str("}\n\n");
    Ok(())
}

fn write_hint(out: &mut String, name: &str, hint: &HintData) -> Result<()> {
    writeln!(out, "def {} : HintTuple := {{", name)?;
    writeln!(out, "  hintIndex := {},", hint.index)?;
    writeln!(out, "  piop := \"{}\",", lean_string(&hint.piop))?;
    writeln!(out, "  proves := {},", hint.proves)?;
    writeln!(out, "  busId := {},", lean_expr(&hint.bus_id))?;
    writeln!(out, "  multiplicity := {},", lean_expr(&hint.multiplicity))?;
    out.push_str("  slots := [\n");
    for slot in &hint.slots {
        writeln!(
            out,
            "    {{ name := \"{}\", value := {} }},",
            lean_string(&slot.name),
            lean_expr(&slot.value)
        )?;
    }
    out.push_str("  ]\n}\n\n");
    Ok(())
}

fn lean_expr(value: &Ast) -> String {
    match value {
        Ast::Constant(value) => format!("Expr.constant \"{}\"", lean_string(value)),
        Ast::Witness {
            stage,
            column,
            row_offset,
        } => format!("Expr.witness {stage} {column} ({row_offset})"),
        Ast::Fixed { column, row_offset } => format!("Expr.fixed {column} ({row_offset})"),
        Ast::Challenge { stage, index } => format!("Expr.challenge {stage} {index}"),
        Ast::AirValue(index) => format!("Expr.airValue {index}"),
        Ast::AirGroupValue(index) => format!("Expr.airGroupValue {index}"),
        Ast::Opaque { kind, payload } => format!(
            "Expr.opaque \"{}\" \"{}\"",
            lean_string(kind),
            lean_string(payload)
        ),
        Ast::Add(lhs, rhs) => format!("Expr.add ({}) ({})", lean_expr(lhs), lean_expr(rhs)),
        Ast::Sub(lhs, rhs) => format!("Expr.sub ({}) ({})", lean_expr(lhs), lean_expr(rhs)),
        Ast::Mul(lhs, rhs) => format!("Expr.mul ({}) ({})", lean_expr(lhs), lean_expr(rhs)),
        Ast::Neg(value) => format!("Expr.neg ({})", lean_expr(value)),
    }
}

fn lean_string(value: &str) -> String {
    value.replace('\\', "\\\\").replace('"', "\\\"")
}

fn ident(value: &str) -> String {
    let mut output: String = value
        .chars()
        .map(|character| if character.is_ascii_alphanumeric() { character } else { '_' })
        .collect();
    if output.is_empty() || output.starts_with(char::is_numeric) {
        output.insert(0, '_');
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hint(proves: bool, slots: Vec<Ast>) -> HintData {
        HintData {
            index: 7,
            piop: "Range Check".to_string(),
            proves,
            bus_id: Ast::constant("103"),
            multiplicity: Ast::constant("1"),
            slots: slots
                .into_iter()
                .enumerate()
                .map(|(index, value)| Slot {
                    name: format!("slot_{index}"),
                    value,
                })
                .collect(),
        }
    }

    #[test]
    fn direct_link_preserves_air_value_without_zero_substitution() {
        let hint = hint(false, vec![Ast::AirValue(11)]);
        let alpha = Ast::Challenge { stage: 1, index: 0 };
        let gamma = Ast::Challenge { stage: 1, index: 1 };
        let accumulator = Ast::Witness {
            stage: 2,
            column: 3,
            row_offset: 0,
        };
        let constraint = Ast::add(
            Ast::mul(accumulator.clone(), std_mix(&hint, &alpha, &gamma).unwrap()),
            hint.multiplicity.clone(),
        );
        assert_eq!(
            direct_accumulator(&constraint, &hint, &alpha, &gamma),
            Some(accumulator)
        );
        assert!(lean_expr(&hint.slots[0].value).contains(".airValue 11"));
    }

    #[test]
    fn two_hint_cluster_requires_the_standard_correction() {
        let left = hint(false, vec![Ast::Witness {
            stage: 1,
            column: 4,
            row_offset: 0,
        }]);
        let right = hint(false, vec![Ast::Witness {
            stage: 1,
            column: 5,
            row_offset: 0,
        }]);
        let accumulator = Ast::Witness {
            stage: 2,
            column: 6,
            row_offset: 0,
        };
        let alpha = Ast::Challenge { stage: 1, index: 0 };
        let gamma = Ast::Challenge { stage: 1, index: 1 };
        let constraint = Ast::sub(
            Ast::mul(
                accumulator.clone(),
                Ast::mul(
                    std_mix(&left, &alpha, &gamma).unwrap(),
                    std_mix(&right, &alpha, &gamma).unwrap(),
                ),
            ),
            Ast::add(
                Ast::mul(
                    signed_multiplicity(&left),
                    std_mix(&right, &alpha, &gamma).unwrap(),
                ),
                Ast::mul(
                    signed_multiplicity(&right),
                    std_mix(&left, &alpha, &gamma).unwrap(),
                ),
            ),
        );
        assert_eq!(
            cluster_accumulator(&constraint, &left, &right, &alpha, &gamma),
            Some(accumulator)
        );
    }
}
