//! Probe binary for understanding how bus emissions are encoded in the
//! ZisK pilout. Run with:
//!
//!   cargo run --release --example probe_buses --
//!     /home/cody/zisk-fv/build/zisk.pilout
//!
//! Dumps top-level hints, focusing on those with air_id matching the Main
//! AIR (idx 0). Shows hint name, field names, and operand kinds. Used to
//! discover the structural form of operation-bus emissions.

use prost::Message;
use std::env;
use std::fs;

mod pilout {
    include!(concat!(env!("OUT_DIR"), "/pilout.rs"));
}

use pilout::{
    expression::Operation as ExprOp, hint_field, operand::Operand as OperandKind, Expression,
    HintField, Operand, PilOut,
};

fn render_op(p: &PilOut, air_idx: usize, op: &Operand) -> String {
    match &op.operand {
        Some(OperandKind::Constant(c)) => format!("{:?}", c.value),
        Some(OperandKind::WitnessCol(w)) => {
            format!("WC(stage={},col={},off={})", w.stage, w.col_idx, w.row_offset)
        }
        Some(OperandKind::Expression(e)) => {
            let air = &p.air_groups[0].airs[air_idx];
            render_expr(p, air_idx, &air.expressions[e.idx as usize])
        }
        Some(o) => format!("{:?}", o),
        None => "<none>".to_string(),
    }
}

fn render_expr(p: &PilOut, air_idx: usize, e: &Expression) -> String {
    match e.operation.as_ref().unwrap() {
        ExprOp::Add(a) => format!(
            "({} + {})",
            render_op(p, air_idx, a.lhs.as_ref().unwrap()),
            render_op(p, air_idx, a.rhs.as_ref().unwrap())
        ),
        ExprOp::Sub(s) => format!(
            "({} - {})",
            render_op(p, air_idx, s.lhs.as_ref().unwrap()),
            render_op(p, air_idx, s.rhs.as_ref().unwrap())
        ),
        ExprOp::Mul(m) => format!(
            "({} * {})",
            render_op(p, air_idx, m.lhs.as_ref().unwrap()),
            render_op(p, air_idx, m.rhs.as_ref().unwrap())
        ),
        ExprOp::Neg(n) => format!("(-{})", render_op(p, air_idx, n.value.as_ref().unwrap())),
    }
}

fn describe_operand(op: &Operand) -> String {
    match &op.operand {
        Some(OperandKind::Constant(c)) => format!("Const(bytes={:?})", c.value),
        Some(OperandKind::Challenge(c)) => format!("Challenge(stage={}, idx={})", c.stage, c.idx),
        Some(OperandKind::ProofValue(p)) => format!("ProofValue(stage={}, idx={})", p.stage, p.idx),
        Some(OperandKind::AirGroupValue(a)) => format!("AirGroupValue(idx={})", a.idx),
        Some(OperandKind::AirValue(a)) => format!("AirValue(idx={})", a.idx),
        Some(OperandKind::PublicValue(p)) => format!("PublicValue(idx={})", p.idx),
        Some(OperandKind::PeriodicCol(c)) => {
            format!("PeriodicCol(idx={}, off={})", c.idx, c.row_offset)
        }
        Some(OperandKind::FixedCol(c)) => format!("FixedCol(idx={}, off={})", c.idx, c.row_offset),
        Some(OperandKind::WitnessCol(w)) => format!(
            "WitnessCol(stage={}, col={}, off={})",
            w.stage, w.col_idx, w.row_offset
        ),
        Some(OperandKind::Expression(e)) => format!("Expression(idx={})", e.idx),
        Some(OperandKind::CustomCol(c)) => format!(
            "CustomCol(commit={}, stage={}, col={}, off={})",
            c.commit_id, c.stage, c.col_idx, c.row_offset
        ),
        None => "<none>".to_string(),
    }
}

fn describe_field(field: &HintField, indent: usize) {
    let pad = " ".repeat(indent);
    let name = field.name.as_deref().unwrap_or("<unnamed>");
    match &field.value {
        Some(hint_field::Value::StringValue(s)) => {
            println!("{}{}: string({})", pad, name, s);
        }
        Some(hint_field::Value::Operand(op)) => {
            println!("{}{}: {}", pad, name, describe_operand(op));
        }
        Some(hint_field::Value::HintFieldArray(a)) => {
            println!("{}{}: array(len={})", pad, name, a.hint_fields.len());
            for inner in &a.hint_fields {
                describe_field(inner, indent + 2);
            }
        }
        None => {
            println!("{}{}: <none>", pad, name);
        }
    }
}

fn main() {
    let path = env::args()
        .nth(1)
        .unwrap_or_else(|| "/home/cody/zisk-fv/build/zisk.pilout".to_string());
    let bytes = fs::read(&path).expect("read pilout");
    let p = PilOut::decode(bytes.as_slice()).expect("decode pilout");

    println!("PilOut: top-level hints = {}", p.hints.len());
    let mut by_name = std::collections::BTreeMap::<String, usize>::new();
    for h in &p.hints {
        *by_name.entry(h.name.clone()).or_insert(0) += 1;
    }
    println!("hint name histogram:");
    for (k, v) in &by_name {
        println!("  {} x {}", v, k);
    }

    let only_main = env::args().any(|a| a == "--main");
    let only_bin_add = env::args().any(|a| a == "--binadd");
    let only_name = env::args()
        .skip_while(|a| a != "--name")
        .nth(1);
    let resolve_idx: Option<usize> = env::args()
        .skip_while(|a| a != "--resolve-expr")
        .nth(1)
        .and_then(|s| s.parse().ok());
    let resolve_air: usize = env::args()
        .skip_while(|a| a != "--resolve-air")
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    if let Some(idx) = resolve_idx {
        let air = &p.air_groups[0].airs[resolve_air];
        println!(
            "expr {} of air {} = {}",
            idx,
            air.name.as_deref().unwrap_or(""),
            render_expr(&p, resolve_air, &air.expressions[idx])
        );
        return;
    }

    for (i, h) in p.hints.iter().enumerate() {
        if only_main && h.air_id != Some(0) {
            continue;
        }
        if only_bin_add && h.air_id != Some(11) {
            continue;
        }
        if let Some(n) = &only_name {
            if &h.name != n {
                continue;
            }
        }
        println!(
            "\n--- hint #{}  name={}  airgroup={:?}  air={:?}  fields={}",
            i,
            h.name,
            h.air_group_id,
            h.air_id,
            h.hint_fields.len()
        );
        for f in &h.hint_fields {
            describe_field(f, 2);
        }
    }
}
