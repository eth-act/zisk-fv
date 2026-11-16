use std::{collections::{HashMap, HashSet}, fs, path::PathBuf};
use anyhow::{anyhow, bail, ensure, Context, Result};
use prost::Message;
mod pilout { include!(concat!(env!("OUT_DIR"), "/pilout.rs")); }
use pilout::{Air, Operand, PilOut, constraint::Constraint as ConstraintKind,
    expression::Operation, operand::Operand as OperandKind};

fn operands(op: &Operation) -> [Option<&Operand>; 2] {
    match op {
        Operation::Add(x) => [x.lhs.as_ref(), x.rhs.as_ref()],
        Operation::Sub(x) => [x.lhs.as_ref(), x.rhs.as_ref()],
        Operation::Mul(x) => [x.lhs.as_ref(), x.rhs.as_ref()],
        Operation::Neg(x) => [x.value.as_ref(), None],
    }
}
fn operands_mut(op: &mut Operation) -> [Option<&mut Operand>; 2] {
    match op {
        Operation::Add(x) => [x.lhs.as_mut(), x.rhs.as_mut()],
        Operation::Sub(x) => [x.lhs.as_mut(), x.rhs.as_mut()],
        Operation::Mul(x) => [x.lhs.as_mut(), x.rhs.as_mut()],
        Operation::Neg(x) => [x.value.as_mut(), None],
    }
}
fn clone_expression(air: &mut Air, id: u32, memo: &mut HashMap<u32,u32>, active: &mut HashSet<u32>) -> Result<u32> {
    if let Some(new) = memo.get(&id) { return Ok(*new); }
    ensure!(active.insert(id), "cycle at source expression {id}");
    let mut expr = air.expressions.get(id as usize).context("source expression index")?.clone();
    for operand in operands_mut(expr.operation.as_mut().context("missing operation")?).into_iter().flatten() {
        if let Some(OperandKind::Expression(reference)) = operand.operand.as_mut() {
            reference.idx = clone_expression(air, reference.idx, memo, active)?;
        }
    }
    active.remove(&id);
    let new = u32::try_from(air.expressions.len())?;
    air.expressions.push(expr);
    memo.insert(id,new);
    Ok(new)
}
fn mutate_leaves(air: &mut Air, id: u32, visited: &mut HashSet<u32>, f: &mut impl FnMut(&mut Operand) -> Result<usize>) -> Result<usize> {
    if !visited.insert(id) { return Ok(0); }
    let mut count = 0;
    let children = {
        let op = air.expressions.get_mut(id as usize).context("cloned expression index")?.operation.as_mut().context("missing operation")?;
        let mut children = [None,None];
        for (i,operand) in operands_mut(op).into_iter().flatten().enumerate() {
            count += f(operand)?;
            if let Some(OperandKind::Expression(reference)) = &operand.operand { children[i] = Some(reference.idx); }
        }
        children
    };
    for child in children.into_iter().flatten() { count += mutate_leaves(air,child,visited,f)?; }
    Ok(count)
}
fn expression_ref(operand: &Option<Operand>) -> Result<u32> {
    match &operand.as_ref().context("missing operand")?.operand {
        Some(OperandKind::Expression(reference)) => Ok(reference.idx),
        other => bail!("expected actual expression reference, got {other:?}"),
    }
}
fn outer_difference(air: &Air, root: u32) -> Result<u32> {
    match air.expressions[root as usize].operation.as_ref().context("missing root")? {
        Operation::Mul(product) => {
            ensure!(matches!(product.lhs.as_ref().and_then(|x|x.operand.as_ref()),
                Some(OperandKind::FixedCol(x)) if x.idx == 1 && x.row_offset == 1),
                "actual root selector is not fixed1/rotation1: {product:?}");
            let id = expression_ref(&product.rhs)?;
            ensure!(matches!(air.expressions[id as usize].operation,Some(Operation::Sub(_))), "outer subtraction missing");
            Ok(id)
        }
        other => bail!("actual c33 root is not Mul: {other:?}"),
    }
}
fn root_index(air: &Air) -> Result<u32> {
    match air.constraints.get(33).context("Mem c33 missing")?.constraint.as_ref() {
        Some(ConstraintKind::EveryRow(c)) => Ok(c.expression_idx.as_ref().context("c33 root missing")?.idx),
        other => bail!("actual c33 is not EveryRow: {other:?}"),
    }
}
fn validate_graph(p: &PilOut, group: usize, air_id: usize, id: u32, seen: &mut HashSet<u32>) -> Result<()> {
    if !seen.insert(id) { return Ok(()); }
    let air = &p.air_groups[group].airs[air_id];
    let expr = air.expressions.get(id as usize).context("invalid expression reference")?;
    for operand in operands(expr.operation.as_ref().context("missing operation")?).into_iter().flatten() {
        match operand.operand.as_ref().context("empty operand")? {
            OperandKind::Expression(r) => validate_graph(p,group,air_id,r.idx,seen)?,
            OperandKind::AirGroupValue(r) => ensure!((r.idx as usize) < p.air_groups[group].air_group_values.len(), "undeclared GROUP{}",r.idx),
            OperandKind::AirValue(r) => ensure!((r.idx as usize) < air.air_values.len(), "undeclared AIR{}",r.idx),
            OperandKind::WitnessCol(r) => {
                ensure!(r.stage > 0,"invalid witness stage0");
                let width = air.stage_widths.get((r.stage-1) as usize).context("undeclared witness stage")?;
                ensure!(r.col_idx < *width,"witness column out of declared stage");
            }
            OperandKind::FixedCol(r) => ensure!(p.symbols.iter().any(|s|
                s.air_group_id == Some(group as u32) && s.air_id == Some(air_id as u32) &&
                s.r#type == pilout::SymbolType::FixedCol as i32 && s.id == r.idx),"undeclared fixed{}",r.idx),
            other => bail!("unexpected operand in actual c33 source graph: {other:?}"),
        }
    }
    Ok(())
}
fn main() -> Result<()> {
    let mut options = HashMap::new();
    let mut args = std::env::args().skip(1);
    while let Some(key) = args.next() { options.insert(key,args.next().context("flag without value")?); }
    let get = |key: &str| options.get(key).map(String::as_str).ok_or_else(||anyhow!("missing {key}"));
    let input = PathBuf::from(get("--input")?);
    let output = PathBuf::from(get("--output")?);
    let report = PathBuf::from(get("--report")?);
    let case = get("--case")?;
    ensure!(["baseline","neutral_clone","group_to_air0","group_index1","direct_sign","drop_direct5","l1_rotation0"].contains(&case),"unknown case {case}");
    let bytes = fs::read(&input)?;
    let mut p = PilOut::decode(bytes.as_slice())?;
    let group = p.air_groups.iter().position(|g|g.name.as_deref()==Some("Zisk")).context("Zisk group")?;
    let air_id = p.air_groups[group].airs.iter().position(|a|a.name.as_deref()==Some("Mem")).context("Mem AIR")?;
    ensure!((group,air_id)==(0,14),"unexpected pinned source scope");
    let original_root = root_index(&p.air_groups[group].airs[air_id])?;
    validate_graph(&p,group,air_id,original_root,&mut HashSet::new())?;
    let original_expressions = p.air_groups[group].airs[air_id].expressions.len();
    let mut changes = 0;
    let mut new_root = original_root;
    if case == "group_index1" {
        ensure!(p.air_groups[group].air_group_values.len()==1,"source already declares another group value");
        let mut symbol = p.symbols.iter().find(|s|s.name=="Zisk.gsum_result" && s.r#type==pilout::SymbolType::AirGroupValue as i32).context("actual GROUP0 symbol")?.clone();
        ensure!(symbol.id==0 && symbol.stage==Some(2) && symbol.air_group_id==Some(0) && symbol.air_id.is_none() && symbol.dim==0 && symbol.lengths.is_empty(),"wrong group declaration shape");
        symbol.id=1; symbol.name="Zisk.gsum_result_counterfactual".to_string();
        p.symbols.push(symbol);
        p.air_groups[group].air_group_values.push(pilout::AirGroupValue{agg_type:pilout::AggregationType::Sum as i32,stage:2});
    }
    if case != "baseline" {
        let air = &mut p.air_groups[group].airs[air_id];
        new_root=clone_expression(air,original_root,&mut HashMap::new(),&mut HashSet::new())?;
        let outer=outer_difference(air,new_root)?;
        match air.constraints[33].constraint.as_mut().context("c33")? {
            ConstraintKind::EveryRow(c) => c.expression_idx.as_mut().context("c33 reference")?.idx=new_root,
            _ => bail!("wrong c33 kind"),
        }
        match case {
            "neutral_clone" => {},
            "group_to_air0" | "group_index1" => {
                changes=mutate_leaves(air,new_root,&mut HashSet::new(),&mut |operand| {
                    if matches!(&operand.operand,Some(OperandKind::AirGroupValue(x)) if x.idx==0) {
                        operand.operand=Some(if case=="group_to_air0" { OperandKind::AirValue(pilout::operand::AirValue{idx:0}) }
                            else { OperandKind::AirGroupValue(pilout::operand::AirGroupValue{idx:1}) });
                        Ok(1)
                    } else { Ok(0) }
                })?;
            }
            "l1_rotation0" => {
                changes=mutate_leaves(air,new_root,&mut HashSet::new(),&mut |operand| {
                    if let Some(OperandKind::FixedCol(x))=operand.operand.as_mut() {
                        if x.idx==1 && x.row_offset==1 { x.row_offset=0;return Ok(1); }
                    }
                    Ok(0)
                })?;
            }
            "direct_sign" => {
                let old=air.expressions[outer as usize].operation.take().context("outer operation")?;
                if let Operation::Sub(x)=old { air.expressions[outer as usize].operation=Some(Operation::Add(pilout::expression::Add{lhs:x.lhs,rhs:x.rhs}));changes=1; }
                else { bail!("outer source subtraction missing"); }
            }
            "drop_direct5" => {
                let direct = match air.expressions[outer as usize].operation.as_ref().context("outer")? { Operation::Sub(x)=>expression_ref(&x.rhs)?,_=>bail!("outer subtraction") };
                let previous=match air.expressions[direct as usize].operation.as_ref().context("direct sum")? {
                    Operation::Add(x) => {
                        ensure!(matches!(x.rhs.as_ref().and_then(|o|o.operand.as_ref()),Some(OperandKind::AirValue(r)) if r.idx==20),"last direct term not AIR20: {x:?}");
                        x.lhs.clone().context("previous five terms")?
                    }
                    _=>bail!("direct sum not Add"),
                };
                if let Some(Operation::Sub(x))=air.expressions[outer as usize].operation.as_mut() { x.rhs=Some(previous);changes=1; }
            }
            _=>bail!("unhandled semantic case"),
        }
    }
    ensure!(changes==usize::from(case!="baseline" && case!="neutral_clone"),"semantic mutation count {changes}");
    validate_graph(&p,group,air_id,new_root,&mut HashSet::new())?;
    let encoded=if case=="baseline" { bytes.clone() } else { p.encode_to_vec() };
    if case!="baseline" { ensure!(encoded!=bytes,"counterfactual did not change actual source bytes"); }
    if let Some(parent)=output.parent() { fs::create_dir_all(parent)?; }
    if let Some(parent)=report.parent() { fs::create_dir_all(parent)?; }
    fs::write(&output,&encoded)?;
    fs::write(report,serde_json::to_vec_pretty(&serde_json::json!({
        "layer":"actual production compiled PilOut protobuf","case":case,"group":group,"air":air_id,"constraint":33,
        "original_root":original_root,"new_root":new_root,"original_expressions":original_expressions,
        "new_expressions":p.air_groups[group].airs[air_id].expressions.len(),"semantic_changes":changes,
        "group_declarations":p.air_groups[group].air_group_values.len(),"input_bytes":bytes.len(),"output_bytes":encoded.len(),
        "source_schema_and_reference_checks":"passed","generated_Lean_edited":false
    }))?)?;
    Ok(())
}
