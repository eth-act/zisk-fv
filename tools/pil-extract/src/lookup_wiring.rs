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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LinkShape {
    Direct,
    Cluster2,
    GsumFinalRow,
    DirectZeroTail,
    Cluster2ZeroTail,
    DirectAssumesNegForm,
    DirectAssumesNegFormZeroTail,
}

struct LinkedConstraint {
    constraint_index: usize,
    constraint: Ast,
    accumulator: Ast,
    alpha: Ast,
    gamma: Ast,
    hints: Vec<HintData>,
    direct_terms: Vec<Ast>,
    shape: LinkShape,
}

#[derive(Clone)]
struct MixedConstraint {
    index: usize,
    expression: Ast,
}

struct UnlinkedConstraint {
    index: usize,
    expression: Ast,
    reason: String,
}

#[derive(Clone)]
struct MixCandidate {
    hint: usize,
    alpha: Ast,
    gamma: Ast,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MatchRoute {
    ClusterZeroTail,
    DirectZeroTail,
    DirectAssumesNeg,
    DirectAssumesNegZeroTail,
}

struct RouteScope {
    route: MatchRoute,
    air: &'static str,
    constraints: &'static [usize],
}

const ALL_CONSTRAINTS: &[usize] = &[];

/// Audited recognizer scope, indexed independently by template route and AIR.
/// An empty constraint list means every constraint in that AIR.
const ROUTE_SCOPES: &[RouteScope] = &[
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "MemAlign", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "MemAlignByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "MemAlignReadByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "Binary", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "BinaryExtension", constraints: &[4] },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "BinaryAdd", constraints: &[5] },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "Arith", constraints: &[61] },
    RouteScope { route: MatchRoute::ClusterZeroTail, air: "Main", constraints: &[43, 44, 45] },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "MemAlign", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "MemAlignByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "MemAlignReadByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "Binary", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "BinaryExtension", constraints: &[4] },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "BinaryAdd", constraints: &[5] },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "Arith", constraints: &[61] },
    RouteScope { route: MatchRoute::DirectZeroTail, air: "Main", constraints: &[43, 44, 45] },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "MemAlign", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "MemAlignByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "MemAlignReadByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "Binary", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "BinaryExtension", constraints: &[4] },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "BinaryAdd", constraints: &[5] },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "Arith", constraints: &[61] },
    RouteScope { route: MatchRoute::DirectAssumesNeg, air: "Main", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "MemAlign", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "MemAlignByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "MemAlignReadByte", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "Binary", constraints: ALL_CONSTRAINTS },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "BinaryExtension", constraints: &[4] },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "BinaryAdd", constraints: &[5] },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "Arith", constraints: &[61] },
    RouteScope { route: MatchRoute::DirectAssumesNegZeroTail, air: "Main", constraints: &[43, 44, 45] },
];

fn route_scope(route: MatchRoute, air_name: &str, constraint_index: usize) -> bool {
    ROUTE_SCOPES.iter().any(|scope| {
        scope.route == route
            && scope.air == air_name
            && (scope.constraints.is_empty() || scope.constraints.contains(&constraint_index))
    })
}

struct AirManifest {
    group_index: usize,
    air_index: usize,
    group_name: String,
    air_name: String,
    emitted_constraint_file: bool,
    mixed_constraint_count: usize,
    unlinked_mixed_constraint_count: usize,
    unlinked_constraints: Vec<UnlinkedConstraint>,
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
            if link.shape == LinkShape::GsumFinalRow {
                write_final_row_link(&mut out, air, link)?;
            } else {
                write_link(&mut out, air, link)?;
            }
        }
    }
    out.push_str("def airStatuses : List AirStatus := [\n");
    for air in &airs {
        writeln!(out, "  airStatus_{},", ident(&air.air_name))?;
    }
    out.push_str("]\n\n");
    out.push_str("def unlinkedMixedConstraints : List ConstraintOnly := [\n");
    for air in &airs {
        for constraint in &air.unlinked_constraints {
            writeln!(
                out,
                "  constraintOnly_{}_{} ,",
                ident(&air.air_name),
                constraint.index
            )?;
        }
    }
    out.push_str("]\n\n");
    out.push_str("def validatedLinks : List ValidatedLink := [\n");
    for air in &airs {
        for link in &air.links {
            if link.shape != LinkShape::GsumFinalRow {
                writeln!(
                    out,
                    "  link_{}_{} ,",
                    ident(&air.air_name),
                    link.constraint_index
                )?;
            }
        }
    }
    out.push_str("]\n\n");
    out.push_str("def validatedFinalRows : List ValidatedFinalRow := [\n");
    for air in &airs {
        for link in &air.links {
            if link.shape == LinkShape::GsumFinalRow {
                writeln!(
                    out,
                    "  link_{}_{} ,",
                    ident(&air.air_name),
                    link.constraint_index
                )?;
            }
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
            mixed_constraints.push(MixedConstraint {
                index: constraint_index,
                expression: resolver.expression(expression_index)?,
            });
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
        find_links(&air_name, &mixed_constraints, &hints, &challenges)?
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
            .filter(|constraint| !linked_constraints.contains(&constraint.index))
            .map(|constraint| UnlinkedConstraint {
                index: constraint.index,
                expression: constraint.expression,
                reason: "no remaining gsum hint matched an audited link route".to_string(),
            })
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
    air_name: &str,
    constraints: &[MixedConstraint],
    hints: &[HintData],
    challenges: &[Ast],
) -> Result<(Vec<LinkedConstraint>, usize)> {
    let mut links = Vec::new();
    let mut consumed = HashSet::new();
    let mut by_mix: HashMap<Ast, Vec<MixCandidate>> = HashMap::new();
    let mut zero_tail_by_mix: HashMap<Ast, Vec<MixCandidate>> = HashMap::new();
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
                if let Some(mix) = zero_tail_std_mix(hint, alpha, gamma) {
                    zero_tail_by_mix
                        .entry(normalise(mix))
                        .or_default()
                        .push(MixCandidate {
                            hint: index,
                            alpha: alpha.clone(),
                            gamma: gamma.clone(),
                        });
                }
            }
        }
    }
    for mixed_constraint in constraints {
        let constraint_index = mixed_constraint.index;
        let constraint = &mixed_constraint.expression;
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
                constraint_index,
                constraint: constraint.clone(),
                accumulator,
                alpha,
                gamma,
                hints: vec![hints[left].clone(), hints[right].clone()],
                direct_terms: Vec::new(),
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
                constraint_index,
                constraint: constraint.clone(),
                accumulator,
                alpha,
                gamma,
                hints: vec![hints[hint].clone()],
                direct_terms: Vec::new(),
                shape: LinkShape::Direct,
            });
            continue;
        }

        if route_scope(
            MatchRoute::DirectAssumesNeg,
            air_name,
            constraint_index,
        ) {
            let sign_form_matches = direct_assumes_neg_form_matches(
                constraint,
                hints,
                &consumed,
                &by_mix,
            );
            if sign_form_matches.len() > 1 {
                bail!(
                    "constraint #{constraint_index} has {} possible direct assumes-neg template links",
                    sign_form_matches.len()
                );
            }
            if let Some((hint, accumulator, alpha, gamma)) = sign_form_matches.into_iter().next() {
                consumed.insert(hint);
                links.push(LinkedConstraint {
                    constraint_index,
                    constraint: constraint.clone(),
                    accumulator,
                    alpha,
                    gamma,
                    hints: vec![hints[hint].clone()],
                    direct_terms: Vec::new(),
                    shape: LinkShape::DirectAssumesNegForm,
                });
                continue;
            }
        }

        if route_scope(
            MatchRoute::ClusterZeroTail,
            air_name,
            constraint_index,
        ) {
            let pair_matches = zero_tail_pair_matches(
                constraint,
                hints,
                &consumed,
                &zero_tail_by_mix,
            );
            if pair_matches.len() > 1 {
                bail!(
                    "constraint #{constraint_index} has {} possible two-hint zero-tail template links",
                    pair_matches.len()
                );
            }
            if let Some((left, right, accumulator, alpha, gamma)) = pair_matches.into_iter().next() {
                consumed.insert(left);
                consumed.insert(right);
                links.push(LinkedConstraint {
                    constraint_index,
                    constraint: constraint.clone(),
                    accumulator,
                    alpha,
                    gamma,
                    hints: vec![hints[left].clone(), hints[right].clone()],
                    direct_terms: Vec::new(),
                    shape: LinkShape::Cluster2ZeroTail,
                });
                continue;
            }
        }

        if route_scope(
            MatchRoute::DirectZeroTail,
            air_name,
            constraint_index,
        ) {
            let single_matches = zero_tail_single_matches(
                constraint,
                hints,
                &consumed,
                &zero_tail_by_mix,
            );
            if single_matches.len() > 1 {
                bail!(
                    "constraint #{constraint_index} has {} possible direct zero-tail template links",
                    single_matches.len()
                );
            }
            if let Some((hint, accumulator, alpha, gamma)) = single_matches.into_iter().next() {
                consumed.insert(hint);
                links.push(LinkedConstraint {
                    constraint_index,
                    constraint: constraint.clone(),
                    accumulator,
                    alpha,
                    gamma,
                    hints: vec![hints[hint].clone()],
                    direct_terms: Vec::new(),
                    shape: LinkShape::DirectZeroTail,
                });
                continue;
            }
        }

        if route_scope(
            MatchRoute::DirectAssumesNegZeroTail,
            air_name,
            constraint_index,
        ) {
            let composed_matches = direct_assumes_neg_form_zero_tail_matches(
                constraint,
                hints,
                &consumed,
                &zero_tail_by_mix,
            );
            if composed_matches.len() > 1 {
                bail!(
                    "constraint #{constraint_index} has {} possible direct assumes-neg zero-tail template links",
                    composed_matches.len()
                );
            }
            if let Some((hint, accumulator, alpha, gamma)) = composed_matches.into_iter().next() {
                consumed.insert(hint);
                links.push(LinkedConstraint {
                    constraint_index,
                    constraint: constraint.clone(),
                    accumulator,
                    alpha,
                    gamma,
                    hints: vec![hints[hint].clone()],
                    direct_terms: Vec::new(),
                    shape: LinkShape::DirectAssumesNegFormZeroTail,
                });
                continue;
            }
        }

        if let Some((selector, group_value, gsum, direct_terms)) =
            gsum_final_row_parts(constraint)
        {
            links.push(LinkedConstraint {
                constraint_index,
                constraint: constraint.clone(),
                accumulator: gsum,
                alpha: selector,
                gamma: group_value,
                hints: Vec::new(),
                direct_terms,
                shape: LinkShape::GsumFinalRow,
            });
            continue;
        }
    }
    let unlinked = constraints.len().saturating_sub(links.len());
    Ok((links, unlinked))
}

fn add_terms(terms: &[Ast]) -> Ast {
    terms
        .iter()
        .cloned()
        .reduce(Ast::add)
        .unwrap_or_else(|| Ast::constant("0"))
}

fn collect_add_terms(value: &Ast, terms: &mut Vec<Ast>) {
    if let Ast::Add(lhs, rhs) = value {
        collect_add_terms(lhs, terms);
        collect_add_terms(rhs, terms);
    } else {
        terms.push(value.clone());
    }
}

fn gsum_final_row_template(
    selector: Ast,
    group_value: Ast,
    gsum: Ast,
    direct_terms: &[Ast],
) -> Ast {
    normalise(Ast::mul(
        selector,
        Ast::sub(Ast::sub(group_value, gsum), add_terms(direct_terms)),
    ))
}

/// Recognize only the last-row global-sum closure emitted by PIL:
/// L1 times (airGroupValue minus gsum minus the sum of direct terms).
fn gsum_final_row_parts(constraint: &Ast) -> Option<(Ast, Ast, Ast, Vec<Ast>)> {
    let Ast::Mul(selector, body) = constraint else {
        return None;
    };
    if !matches!(selector.as_ref(), Ast::Fixed { row_offset: 1, .. }) {
        return None;
    }
    let (group_value, gsum, direct_sum) = match body.as_ref() {
        Ast::Sub(lhs, direct_sum) => match lhs.as_ref() {
            Ast::Sub(group_value, gsum) => (
                group_value.as_ref(),
                gsum.as_ref(),
                Some(direct_sum.as_ref()),
            ),
            Ast::AirGroupValue(_) => (lhs.as_ref(), direct_sum.as_ref(), None),
            _ => return None,
        },
        _ => return None,
    };
    if !matches!(group_value, Ast::AirGroupValue(_))
        || !matches!(gsum, Ast::Witness { stage: 2, .. })
    {
        return None;
    }
    let mut direct_terms = Vec::new();
    if let Some(direct_sum) = direct_sum {
        collect_add_terms(direct_sum, &mut direct_terms);
        if !direct_terms.iter().all(|term| matches!(term, Ast::AirValue(_))) {
            return None;
        }
    }
    let parts = (
        selector.as_ref().clone(),
        group_value.clone(),
        gsum.clone(),
        direct_terms,
    );
    (gsum_final_row_template(
        parts.0.clone(),
        parts.1.clone(),
        parts.2.clone(),
        &parts.3,
    ) == *constraint)
        .then_some(parts)
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

fn zero_tail_single_matches(
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
        .filter(|candidate| has_literal_zero_tail(&hints[candidate.hint]))
        .filter_map(|candidate| {
            zero_tail_direct_accumulator(
                constraint,
                &hints[candidate.hint],
                &candidate.alpha,
                &candidate.gamma,
            )
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

fn zero_tail_pair_matches(
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
                || !(has_literal_zero_tail(&hints[left.hint])
                    || has_literal_zero_tail(&hints[right.hint]))
            {
                continue;
            }
            if let Some(accumulator) = zero_tail_cluster_accumulator(
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

fn direct_assumes_neg_form_matches(
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
        .filter(|candidate| !hints[candidate.hint].proves)
        .filter_map(|candidate| {
            direct_assumes_neg_form_accumulator(
                constraint,
                &hints[candidate.hint],
                &candidate.alpha,
                &candidate.gamma,
            )
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

fn direct_assumes_neg_form_zero_tail_matches(
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
        .filter(|candidate| {
            let hint = &hints[candidate.hint];
            !hint.proves && has_literal_zero_tail(hint)
        })
        .filter_map(|candidate| {
            direct_assumes_neg_form_zero_tail_accumulator(
                constraint,
                &hints[candidate.hint],
                &candidate.alpha,
                &candidate.gamma,
            )
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

fn zero_tail_direct_accumulator(
    constraint: &Ast,
    hint: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Option<Ast> {
    match (hint.proves, constraint) {
        (false, Ast::Add(lhs, rhs)) => match lhs.as_ref() {
            Ast::Mul(accumulator, _) if **rhs == normalise(hint.multiplicity.clone()) => {
                let accumulator = (**accumulator).clone();
                (normalise(zero_tail_direct_template(
                    accumulator.clone(),
                    hint,
                    alpha,
                    gamma,
                )) == *constraint)
                    .then_some(accumulator)
            }
            _ => None,
        },
        (true, Ast::Sub(lhs, rhs)) => match lhs.as_ref() {
            Ast::Mul(accumulator, _) if **rhs == normalise(hint.multiplicity.clone()) => {
                let accumulator = (**accumulator).clone();
                (normalise(zero_tail_direct_template(
                    accumulator.clone(),
                    hint,
                    alpha,
                    gamma,
                )) == *constraint)
                    .then_some(accumulator)
            }
            _ => None,
        },
        _ => None,
    }
}

fn direct_assumes_neg_form_accumulator(
    constraint: &Ast,
    hint: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Option<Ast> {
    let Ast::Sub(lhs, rhs) = constraint else {
        return None;
    };
    let Ast::Mul(accumulator, _) = lhs.as_ref() else {
        return None;
    };
    if **rhs != normalise(assumes_neg_multiplicity(hint)) {
        return None;
    }
    let accumulator = (**accumulator).clone();
    (normalise(direct_assumes_neg_form_template(
        accumulator.clone(),
        hint,
        alpha,
        gamma,
    )) == *constraint)
        .then_some(accumulator)
}

fn direct_assumes_neg_form_zero_tail_accumulator(
    constraint: &Ast,
    hint: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Option<Ast> {
    let Ast::Sub(lhs, rhs) = constraint else {
        return None;
    };
    let Ast::Mul(accumulator, _) = lhs.as_ref() else {
        return None;
    };
    if **rhs != normalise(assumes_neg_multiplicity(hint)) {
        return None;
    }
    let accumulator = (**accumulator).clone();
    (normalise(direct_assumes_neg_form_zero_tail_template(
        accumulator.clone(),
        hint,
        alpha,
        gamma,
    )) == *constraint)
        .then_some(accumulator)
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

fn zero_tail_cluster_accumulator(
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
    (normalise(zero_tail_cluster_template(
        accumulator.clone(),
        left,
        right,
        alpha,
        gamma,
    )) == *constraint)
        .then_some(accumulator)
}

fn std_mix(hint: &HintData, alpha: &Ast, gamma: &Ast) -> Option<Ast> {
    std_mix_slots(&hint.slots, &hint.bus_id, alpha, gamma)
}

fn std_mix_slots(slots: &[Slot], bus_id: &Ast, alpha: &Ast, gamma: &Ast) -> Option<Ast> {
    let mut values = slots.iter().rev();
    let mut value = values.next()?.value.clone();
    for slot in values {
        value = Ast::add(Ast::mul(value, alpha.clone()), slot.value.clone());
    }
    Some(Ast::add(
        Ast::add(
            Ast::mul(value, alpha.clone()),
            bus_id.clone(),
        ),
        gamma.clone(),
    ))
}

/// Mirror the upstream macro's exact compression: remove a contiguous tail
/// of literal-zero slots before the Horner fold, while retaining literal zero
/// slots that occur before a nonzero slot. This is a template constructor,
/// not an algebraic normalization.
fn zero_tail_std_mix(hint: &HintData, alpha: &Ast, gamma: &Ast) -> Option<Ast> {
    let end = hint
        .slots
        .iter()
        .rposition(|slot| !is_zero(&slot.value))?;
    std_mix_slots(&hint.slots[..=end], &hint.bus_id, alpha, gamma)
}

fn has_literal_zero_tail(hint: &HintData) -> bool {
    matches!(hint.slots.last(), Some(slot) if is_zero(&slot.value))
}

fn signed_multiplicity(hint: &HintData) -> Ast {
    if hint.proves {
        hint.multiplicity.clone()
    } else {
        field_neg(hint.multiplicity.clone())
    }
}

/// PIL's assumes-side direct update renders the correction as `0 - m` and
/// subtracts that term. Preserve the spelling exactly; this is not field
/// negation normalization.
fn assumes_neg_multiplicity(hint: &HintData) -> Ast {
    Ast::sub(Ast::constant("0"), hint.multiplicity.clone())
}

fn direct_template(accumulator: Ast, hint: &HintData, alpha: &Ast, gamma: &Ast) -> Ast {
    let product = Ast::mul(accumulator, std_mix(hint, alpha, gamma).expect("hint has a slot"));
    if hint.proves {
        Ast::sub(product, hint.multiplicity.clone())
    } else {
        Ast::add(product, hint.multiplicity.clone())
    }
}

fn zero_tail_direct_template(
    accumulator: Ast,
    hint: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Ast {
    let product = Ast::mul(
        accumulator,
        zero_tail_std_mix(hint, alpha, gamma).expect("hint has a nonzero slot"),
    );
    if hint.proves {
        Ast::sub(product, hint.multiplicity.clone())
    } else {
        Ast::add(product, hint.multiplicity.clone())
    }
}

fn direct_assumes_neg_form_template(
    accumulator: Ast,
    hint: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Ast {
    debug_assert!(!hint.proves);
    Ast::sub(
        Ast::mul(
            accumulator,
            std_mix(hint, alpha, gamma).expect("hint has a slot"),
        ),
        assumes_neg_multiplicity(hint),
    )
}

fn direct_assumes_neg_form_zero_tail_template(
    accumulator: Ast,
    hint: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Ast {
    debug_assert!(!hint.proves);
    Ast::sub(
        Ast::mul(
            accumulator,
            zero_tail_std_mix(hint, alpha, gamma).expect("hint has a nonzero slot"),
        ),
        assumes_neg_multiplicity(hint),
    )
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

fn zero_tail_cluster_template(
    accumulator: Ast,
    left: &HintData,
    right: &HintData,
    alpha: &Ast,
    gamma: &Ast,
) -> Ast {
    let left_mix = zero_tail_std_mix(left, alpha, gamma).expect("hint has a nonzero slot");
    let right_mix = zero_tail_std_mix(right, alpha, gamma).expect("hint has a nonzero slot");
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
    out.push_str("that tuple. Final-row links instead retain the exact group value,\n");
    out.push_str("global-sum accumulator, selector, and direct terms.\n");
    out.push_str("Hints which have no such link are represented only by their per-AIR\n");
    out.push_str("count; their tuple payload is deliberately withheld.\n");
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
    out.push_str("structure DerivedTuple where\n");
    out.push_str("  piop : String\n  proves : Bool\n  busId : Expr\n");
    out.push_str("  multiplicity : Expr\n  slots : List Slot\n\n");
    out.push_str("inductive LinkShape where\n  | direct\n  | cluster2\n  | gsumFinalRow\n  | directZeroTail\n  | cluster2ZeroTail\n  | directAssumesNegForm\n  | directAssumesNegFormZeroTail\n  deriving Repr, DecidableEq\n\n");
    out.push_str("structure ConstraintOnly where\n");
    out.push_str("  air : String\n  constraintIndex : Nat\n  constraint : Expr\n  reason : String\n\n");
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
    out.push_str("def literalZeroSlot : Slot → Bool\n");
    out.push_str("  | ⟨_, .constant \"0\"⟩ => true\n");
    out.push_str("  | _ => false\n\n");
    out.push_str("def zeroTailSlots (slots : List Slot) : List Slot :=\n");
    out.push_str("  (slots.reverse.dropWhile literalZeroSlot).reverse\n\n");
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
    out.push_str("def directZeroTailTemplate (alpha gamma accumulator : Expr) (hint : HintTuple) : Expr :=\n");
    out.push_str("  if hint.proves then\n");
    out.push_str("    .sub (.mul accumulator (stdMix alpha gamma hint.busId (zeroTailSlots hint.slots))) hint.multiplicity\n");
    out.push_str("  else\n");
    out.push_str("    .add (.mul accumulator (stdMix alpha gamma hint.busId (zeroTailSlots hint.slots))) hint.multiplicity\n\n");
    out.push_str("def assumesNegMultiplicity (hint : HintTuple) : Expr :=\n");
    out.push_str("  .sub (.constant \"0\") hint.multiplicity\n\n");
    out.push_str("def directAssumesNegFormTemplate (alpha gamma accumulator : Expr) (hint : HintTuple) : Expr :=\n");
    out.push_str("  .sub (.mul accumulator (stdMix alpha gamma hint.busId hint.slots)) (assumesNegMultiplicity hint)\n\n");
    out.push_str("def directAssumesNegFormZeroTailTemplate (alpha gamma accumulator : Expr) (hint : HintTuple) : Expr :=\n");
    out.push_str("  .sub (.mul accumulator (stdMix alpha gamma hint.busId (zeroTailSlots hint.slots))) (assumesNegMultiplicity hint)\n\n");
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
    out.push_str("def cluster2ZeroTailTemplate (alpha gamma accumulator : Expr) (left right : HintTuple) : Expr :=\n");
    out.push_str("  let leftMix := stdMix alpha gamma left.busId (zeroTailSlots left.slots)\n");
    out.push_str("  let rightMix := stdMix alpha gamma right.busId (zeroTailSlots right.slots)\n");
    out.push_str("  .sub (.mul accumulator (.mul leftMix rightMix))\n");
    out.push_str("    (.add (.mul (signedSelector left) rightMix) (.mul (signedSelector right) leftMix))\n\n");
    out.push_str("def addTerms : List Expr → Expr\n");
    out.push_str("  | [] => .constant \"0\"\n");
    out.push_str("  | first :: rest => rest.foldl Expr.add first\n\n");
    out.push_str("def gsumFinalRowTemplate (selector groupValue gsum : Expr) (directTerms : List Expr) : Expr :=\n");
    out.push_str("  .mul selector (.sub (.sub groupValue gsum) (addTerms directTerms))\n\n");
    out.push_str("def templateOf (shape : LinkShape) (alpha gamma accumulator : Expr)\n");
    out.push_str("    (hints : List HintTuple) (derivedTuples : List DerivedTuple) : Option Expr :=\n");
    out.push_str("  match shape, hints, derivedTuples with\n");
    out.push_str("  | .direct, [hint], [] => some (normalise (directTemplate alpha gamma accumulator hint))\n");
    out.push_str("  | .cluster2, [left, right], [] => some (normalise (cluster2Template alpha gamma accumulator left right))\n");
    out.push_str("  | .directZeroTail, [hint], [] => some (normalise (directZeroTailTemplate alpha gamma accumulator hint))\n");
    out.push_str("  | .cluster2ZeroTail, [left, right], [] => some (normalise (cluster2ZeroTailTemplate alpha gamma accumulator left right))\n");
    out.push_str("  | .directAssumesNegForm, [hint], [] => some (normalise (directAssumesNegFormTemplate alpha gamma accumulator hint))\n");
    out.push_str("  | .directAssumesNegFormZeroTail, [hint], [] => some (normalise (directAssumesNegFormZeroTailTemplate alpha gamma accumulator hint))\n");
    out.push_str("  | _, _, _ => none\n\n");
    out.push_str("structure ValidatedLink where\n");
    out.push_str("  air : String\n  constraintIndex : Nat\n  shape : LinkShape\n");
    out.push_str("  accumulator : Expr\n  alpha : Expr\n  gamma : Expr\n  constraint : Expr\n  template : Expr\n");
    out.push_str("  hints : List HintTuple\n  derivedTuples : List DerivedTuple\n");
    out.push_str("  templateFromShape : templateOf shape alpha gamma accumulator hints derivedTuples = some template\n");
    out.push_str("  constraintEqualsTemplate : constraint = template\n\n");
    out.push_str("theorem ValidatedLink.constraintValidated (link : ValidatedLink) :\n");
    out.push_str("    templateOf link.shape link.alpha link.gamma link.accumulator\n");
    out.push_str("      link.hints link.derivedTuples = some link.constraint := by\n");
    out.push_str("  rw [link.constraintEqualsTemplate]\n");
    out.push_str("  exact link.templateFromShape\n\n");
    out.push_str("structure ValidatedFinalRow where\n");
    out.push_str("  air : String\n  constraintIndex : Nat\n  shape : LinkShape\n");
    out.push_str("  selector : Expr\n  groupValue : Expr\n  gsum : Expr\n  directTerms : List Expr\n");
    out.push_str("  constraint : Expr\n  template : Expr\n  hints : List HintTuple\n");
    out.push_str("  templateFromTerms : normalise (gsumFinalRowTemplate selector groupValue gsum directTerms) = template\n");
    out.push_str("  constraintEqualsTemplate : constraint = template\n\n");
    out.push_str("theorem ValidatedFinalRow.constraintValidated (link : ValidatedFinalRow) :\n");
    out.push_str("    normalise (gsumFinalRowTemplate link.selector link.groupValue link.gsum link.directTerms) =\n");
    out.push_str("      link.constraint := by\n");
    out.push_str("  rw [link.constraintEqualsTemplate]\n");
    out.push_str("  exact link.templateFromTerms\n\n");
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
    for constraint in &air.unlinked_constraints {
        writeln!(
            out,
            "def constraintOnly_{}_{} : ConstraintOnly := {{",
            ident(&air.air_name),
            constraint.index
        )?;
        writeln!(out, "  air := \"{}\",", lean_string(&air.air_name))?;
        writeln!(out, "  constraintIndex := {},", constraint.index)?;
        writeln!(
            out,
            "  constraint := {},",
            lean_expr(&constraint.expression)
        )?;
        writeln!(out, "  reason := \"{}\"", lean_string(&constraint.reason))?;
        out.push_str("}\n\n");
    }
    Ok(())
}

fn write_link(out: &mut String, air: &AirManifest, link: &LinkedConstraint) -> Result<()> {
    debug_assert_ne!(link.shape, LinkShape::GsumFinalRow);
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
        LinkShape::GsumFinalRow => unreachable!(),
        LinkShape::DirectZeroTail => writeln!(
            out,
            "def template_{} : Expr := normalise (directZeroTailTemplate ({}) ({}) ({}) hint_{}_0)",
            label,
            lean_expr(&link.alpha),
            lean_expr(&link.gamma),
            lean_expr(&link.accumulator),
            label
        )?,
        LinkShape::Cluster2ZeroTail => writeln!(
            out,
            "def template_{} : Expr := normalise (cluster2ZeroTailTemplate ({}) ({}) ({}) hint_{}_0 hint_{}_1)",
            label,
            lean_expr(&link.alpha),
            lean_expr(&link.gamma),
            lean_expr(&link.accumulator),
            label,
            label
        )?,
        LinkShape::DirectAssumesNegForm => writeln!(
            out,
            "def template_{} : Expr := normalise (directAssumesNegFormTemplate ({}) ({}) ({}) hint_{}_0)",
            label,
            lean_expr(&link.alpha),
            lean_expr(&link.gamma),
            lean_expr(&link.accumulator),
            label
        )?,
        LinkShape::DirectAssumesNegFormZeroTail => writeln!(
            out,
            "def template_{} : Expr := normalise (directAssumesNegFormZeroTailTemplate ({}) ({}) ({}) hint_{}_0)",
            label,
            lean_expr(&link.alpha),
            lean_expr(&link.gamma),
            lean_expr(&link.accumulator),
            label
        )?,
    }
    writeln!(out, "def link_{} : ValidatedLink := {{", label)?;
    writeln!(out, "  air := \"{}\",", lean_string(&air.air_name))?;
    writeln!(out, "  constraintIndex := {},", link.constraint_index)?;
    writeln!(
        out,
        "  shape := .{},",
        match link.shape {
            LinkShape::Direct => "direct",
            LinkShape::Cluster2 => "cluster2",
            LinkShape::GsumFinalRow => unreachable!(),
            LinkShape::DirectZeroTail => "directZeroTail",
            LinkShape::Cluster2ZeroTail => "cluster2ZeroTail",
            LinkShape::DirectAssumesNegForm => "directAssumesNegForm",
            LinkShape::DirectAssumesNegFormZeroTail => "directAssumesNegFormZeroTail",
        }
    )?;
    writeln!(out, "  accumulator := {},", lean_expr(&link.accumulator))?;
    writeln!(out, "  alpha := {},", lean_expr(&link.alpha))?;
    writeln!(out, "  gamma := {},", lean_expr(&link.gamma))?;
    writeln!(out, "  constraint := constraint_{},", label)?;
    writeln!(out, "  template := template_{},", label)?;
    writeln!(out, "  hints := [{}],", (0..link.hints.len()).map(|index| format!("hint_{}_{}", label, index)).collect::<Vec<_>>().join(", "))?;
    out.push_str("  derivedTuples := [],\n");
    out.push_str("  templateFromShape := by rfl\n");
    out.push_str("  constraintEqualsTemplate := by rfl\n");
    out.push_str("}\n\n");
    Ok(())
}

fn write_final_row_link(out: &mut String, air: &AirManifest, link: &LinkedConstraint) -> Result<()> {
    debug_assert_eq!(link.shape, LinkShape::GsumFinalRow);
    let label = format!("{}_{}", ident(&air.air_name), link.constraint_index);
    writeln!(out, "def constraint_{} : Expr := {}", label, lean_expr(&link.constraint))?;
    writeln!(
        out,
        "def template_{} : Expr := normalise (gsumFinalRowTemplate ({}) ({}) ({}) [{}])",
        label,
        lean_expr(&link.alpha),
        lean_expr(&link.gamma),
        lean_expr(&link.accumulator),
        link.direct_terms.iter().map(lean_expr).collect::<Vec<_>>().join(", ")
    )?;
    writeln!(out, "def link_{} : ValidatedFinalRow := {{", label)?;
    writeln!(out, "  air := \"{}\",", lean_string(&air.air_name))?;
    writeln!(out, "  constraintIndex := {},", link.constraint_index)?;
    out.push_str("  shape := .gsumFinalRow,\n");
    writeln!(out, "  selector := {},", lean_expr(&link.alpha))?;
    writeln!(out, "  groupValue := {},", lean_expr(&link.gamma))?;
    writeln!(out, "  gsum := {},", lean_expr(&link.accumulator))?;
    writeln!(
        out,
        "  directTerms := [{}],",
        link.direct_terms.iter().map(lean_expr).collect::<Vec<_>>().join(", ")
    )?;
    writeln!(out, "  constraint := constraint_{},", label)?;
    writeln!(out, "  template := template_{},", label)?;
    out.push_str("  hints := [],\n");
    out.push_str("  templateFromTerms := by rfl\n");
    out.push_str("  constraintEqualsTemplate := by rfl\n");
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

    #[test]
    fn validated_link_carries_shape_computed_kernel_equalities() {
        let mut prelude = String::new();
        write_prelude(&mut prelude);

        assert!(prelude.contains(
            "templateFromShape : templateOf shape alpha gamma accumulator hints derivedTuples = some template"
        ));
        assert!(prelude.contains("constraintEqualsTemplate : constraint = template"));
        assert!(prelude.contains("theorem ValidatedLink.constraintValidated"));
        assert!(prelude.contains("| .direct, [hint], [] =>"));
        assert!(prelude.contains("| _, _, _ => none"));
        assert!(prelude.contains("structure ValidatedFinalRow where"));
        assert!(prelude.contains("theorem ValidatedFinalRow.constraintValidated"));
    }

    #[test]
    fn recognizer_scope_is_per_route_and_air() {
        assert!(route_scope(MatchRoute::DirectZeroTail, "BinaryAdd", 5));
        assert!(route_scope(MatchRoute::DirectZeroTail, "BinaryExtension", 4));
        assert!(route_scope(MatchRoute::DirectZeroTail, "Arith", 61));
        assert!(route_scope(MatchRoute::ClusterZeroTail, "Binary", 10));
        assert!(route_scope(MatchRoute::DirectAssumesNeg, "Main", 81));
        assert!(route_scope(
            MatchRoute::DirectAssumesNegZeroTail,
            "Main",
            43,
        ));
        assert!(route_scope(MatchRoute::ClusterZeroTail, "BinaryAdd", 5));
        assert!(!route_scope(MatchRoute::DirectZeroTail, "BinaryAdd", 4));
        assert!(!route_scope(MatchRoute::DirectZeroTail, "Arith", 62));
        assert!(!route_scope(
            MatchRoute::DirectAssumesNegZeroTail,
            "Main",
            46,
        ));
    }

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

    #[test]
    fn zero_tail_mix_trims_only_terminal_literal_zero_slots() {
        let tail_hint = hint(
            true,
            vec![
                Ast::constant("1"),
                Ast::constant("0"),
                Ast::constant("0"),
                Ast::constant("8"),
                Ast::constant("0"),
                Ast::constant("0"),
            ],
        );
        let expected = hint(
            true,
            vec![
                Ast::constant("1"),
                Ast::constant("0"),
                Ast::constant("0"),
                Ast::constant("8"),
            ],
        );
        let alpha = Ast::Challenge { stage: 1, index: 0 };
        let gamma = Ast::Challenge { stage: 1, index: 1 };

        assert!(has_literal_zero_tail(&tail_hint));
        assert_eq!(
            zero_tail_std_mix(&tail_hint, &alpha, &gamma),
            std_mix(&expected, &alpha, &gamma),
        );
        assert_ne!(
            zero_tail_std_mix(&tail_hint, &alpha, &gamma),
            std_mix(&tail_hint, &alpha, &gamma),
        );
    }

    #[test]
    fn zero_tail_cluster_requires_a_terminal_zero_hint() {
        let left = hint(false, vec![Ast::Witness {
            stage: 1,
            column: 4,
            row_offset: 0,
        }]);
        let right = hint(
            true,
            vec![
                Ast::Witness {
                    stage: 1,
                    column: 5,
                    row_offset: 0,
                },
                Ast::constant("0"),
            ],
        );
        let accumulator = Ast::Witness {
            stage: 2,
            column: 6,
            row_offset: 0,
        };
        let alpha = Ast::Challenge { stage: 1, index: 0 };
        let gamma = Ast::Challenge { stage: 1, index: 1 };
        let constraint = normalise(zero_tail_cluster_template(
            accumulator.clone(),
            &left,
            &right,
            &alpha,
            &gamma,
        ));

        assert_eq!(
            zero_tail_cluster_accumulator(&constraint, &left, &right, &alpha, &gamma),
            Some(accumulator),
        );
    }

    #[test]
    fn direct_assumes_neg_form_preserves_the_pilout_sign_spelling() {
        let hint = HintData {
            multiplicity: Ast::add(Ast::AirValue(0), Ast::constant("0")),
            ..hint(false, vec![Ast::constant("1")])
        };
        let accumulator = Ast::Witness {
            stage: 2,
            column: 6,
            row_offset: 0,
        };
        let alpha = Ast::Challenge { stage: 1, index: 0 };
        let gamma = Ast::Challenge { stage: 1, index: 1 };
        let constraint = normalise(direct_assumes_neg_form_template(
            accumulator.clone(),
            &hint,
            &alpha,
            &gamma,
        ));

        assert_eq!(
            direct_assumes_neg_form_accumulator(&constraint, &hint, &alpha, &gamma),
            Some(accumulator),
        );
        assert!(matches!(
            constraint,
            Ast::Sub(_, rhs) if *rhs == Ast::sub(Ast::constant("0"), Ast::AirValue(0))
        ));
    }

    #[test]
    fn direct_assumes_neg_form_zero_tail_composes_exactly() {
        let hint = HintData {
            multiplicity: Ast::add(Ast::AirValue(0), Ast::constant("0")),
            ..hint(false, vec![Ast::constant("1"), Ast::constant("0")])
        };
        let accumulator = Ast::Witness {
            stage: 2,
            column: 6,
            row_offset: 0,
        };
        let alpha = Ast::Challenge { stage: 1, index: 0 };
        let gamma = Ast::Challenge { stage: 1, index: 1 };
        let constraint = normalise(direct_assumes_neg_form_zero_tail_template(
            accumulator.clone(),
            &hint,
            &alpha,
            &gamma,
        ));

        assert_eq!(
            direct_assumes_neg_form_zero_tail_accumulator(
                &constraint,
                &hint,
                &alpha,
                &gamma,
            ),
            Some(accumulator),
        );
    }

}
