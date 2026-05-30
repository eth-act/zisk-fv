use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

use riscv::RiscvInstruction;
use zisk_core::{Riscv2ZiskContext, ZiskInst, ZiskInstBuilder};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Add,
    Sub,
    Sll,
    Slt,
    Sltu,
    Xor,
    Srl,
    Sra,
    Or,
    And,
    Addw,
    Subw,
    Sllw,
    Srlw,
    Sraw,
    Addi,
    Slli,
    Slti,
    Sltiu,
    Xori,
    Srli,
    Srai,
    Ori,
    Andi,
    Addiw,
    Slliw,
    Srliw,
    Sraiw,
    Beq,
    Bne,
    Blt,
    Bge,
    Bltu,
    Bgeu,
    Lb,
    Lbu,
    Lh,
    Lhu,
    Lw,
    Lwu,
    Ld,
    Sb,
    Sh,
    Sw,
    Sd,
    Lui,
    Auipc,
    Jal,
    Jalr,
    Fence,
    Mul,
    Mulh,
    Mulhsu,
    Mulhu,
    Mulw,
    Div,
    Divu,
    Divw,
    Divuw,
    Rem,
    Remu,
    Remw,
    Remuw,
}

#[derive(Clone, Debug)]
struct Case {
    id: usize,
    op: Op,
    paddr: u64,
    rd: u32,
    rs1: u32,
    rs2: u32,
    imm: i32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Row {
    paddr: u64,
    op: u64,
    a_src: u64,
    a_use_sp_imm1: u64,
    a_offset_imm0: u64,
    b_src: u64,
    b_use_sp_imm1: u64,
    b_offset_imm0: u64,
    store: u64,
    store_offset: i64,
    store_pc: bool,
    set_pc: bool,
    ind_width: u64,
    jmp_offset1: i64,
    jmp_offset2: i64,
    is_external_op: bool,
    m32: bool,
}

#[derive(Debug)]
struct LeanDigest {
    id: usize,
    row_count: usize,
    hash: u64,
}

fn main() {
    let cases = generate_cases();
    let mut child = spawn_lean_oracle(true);
    let mut stdin = child.stdin.take().expect("Lean oracle stdin");
    for case in &cases {
        writeln!(stdin, "{}", case_line(case)).expect("write Lean oracle case");
    }
    drop(stdin);

    let stdout = child.stdout.take().expect("Lean oracle stdout");
    let mut checked = 0usize;
    for (case, line) in cases.iter().zip(BufReader::new(stdout).lines()) {
        let line = line.expect("read Lean oracle line");
        let (lean, lean_rows) = parse_rows_line(&line);
        assert_eq!(lean.id, case.id, "Lean oracle returned cases out of order");
        assert_eq!(lean.row_count, lean_rows.len(), "bad Lean row count");
        assert_eq!(lean.hash, rows_hash(&lean_rows), "bad Lean row hash");

        let rust_rows = rust_rows(case);
        if rust_rows != lean_rows {
            panic!(
                "transpiler differential mismatch\ncase_id={}\ncase={:?}\ndiffering_fields={}\nrust_rows={:#?}\nlean_rows={:#?}",
                case.id,
                case,
                diff_rows(&rust_rows, &lean_rows),
                rust_rows,
                lean_rows
            );
        }
        checked += 1;
    }

    let status = child.wait().expect("wait for Lean oracle");
    assert!(status.success(), "Lean oracle failed with {status}");
    assert_eq!(checked, cases.len(), "Lean oracle produced too few rows");

    println!("checked {checked} RV64IM Rust-vs-Lean static-transpiler cases");
}

fn generate_cases() -> Vec<Case> {
    let full_12bit = std::env::var_os("ZISK_DIFF_FULL_12BIT").is_some();
    let full_uj = std::env::var_os("ZISK_DIFF_FULL_UJ").is_some();
    let shard_12bit_count = parse_env_usize("ZISK_DIFF_12BIT_SHARD_COUNT").unwrap_or(1);
    let shard_12bit_index = parse_env_usize("ZISK_DIFF_12BIT_SHARD_INDEX").unwrap_or(0);
    let uj_shard_count = parse_env_usize("ZISK_DIFF_UJ_SHARD_COUNT").unwrap_or(1);
    let uj_shard_index = parse_env_usize("ZISK_DIFF_UJ_SHARD_INDEX").unwrap_or(0);
    assert!(
        shard_12bit_count > 0,
        "ZISK_DIFF_12BIT_SHARD_COUNT must be positive"
    );
    assert!(
        shard_12bit_index < shard_12bit_count,
        "ZISK_DIFF_12BIT_SHARD_INDEX must be less than ZISK_DIFF_12BIT_SHARD_COUNT"
    );
    assert!(
        uj_shard_count > 0,
        "ZISK_DIFF_UJ_SHARD_COUNT must be positive"
    );
    assert!(
        uj_shard_index < uj_shard_count,
        "ZISK_DIFF_UJ_SHARD_INDEX must be less than ZISK_DIFF_UJ_SHARD_COUNT"
    );
    let mut cases = Vec::new();
    let mut push = |op, rd, rs1, rs2, imm| {
        let id = cases.len();
        cases.push(Case {
            id,
            op,
            paddr: 0x1000 + id as u64 * 8,
            rd,
            rs1,
            rs2,
            imm,
        });
    };

    let r_ops = [
        Op::Add,
        Op::Sub,
        Op::Sll,
        Op::Slt,
        Op::Sltu,
        Op::Xor,
        Op::Srl,
        Op::Sra,
        Op::Or,
        Op::And,
        Op::Addw,
        Op::Subw,
        Op::Sllw,
        Op::Srlw,
        Op::Sraw,
        Op::Mul,
        Op::Mulh,
        Op::Mulhsu,
        Op::Mulhu,
        Op::Mulw,
        Op::Div,
        Op::Divu,
        Op::Divw,
        Op::Divuw,
        Op::Rem,
        Op::Remu,
        Op::Remw,
        Op::Remuw,
    ];
    for op in r_ops {
        for rd in 0..32 {
            for rs1 in 0..32 {
                for rs2 in 0..32 {
                    push(op, rd, rs1, rs2, 0);
                }
            }
        }
    }

    let i_ops = [
        Op::Addi,
        Op::Slti,
        Op::Sltiu,
        Op::Xori,
        Op::Ori,
        Op::Andi,
        Op::Addiw,
    ];
    for op in i_ops {
        if full_12bit {
            let mut shard_cursor = 0usize;
            for rd in 0..32 {
                for rs1 in 0..32 {
                    for imm in -2048..=2047 {
                        if shard_cursor % shard_12bit_count == shard_12bit_index {
                            push(op, rd, rs1, 0, imm);
                        }
                        shard_cursor += 1;
                    }
                }
            }
        } else {
            for rd in [0, 1, 31] {
                for rs1 in [0, 1, 31] {
                    for imm in -2048..=2047 {
                        push(op, rd, rs1, 0, imm);
                    }
                }
            }
            for rd in 0..32 {
                for rs1 in 0..32 {
                    for imm in [-2048, -1, 0, 1, 2047] {
                        push(op, rd, rs1, 0, imm);
                    }
                }
            }
        }
    }

    for op in [Op::Slli, Op::Srli, Op::Srai] {
        for rd in 0..32 {
            for rs1 in 0..32 {
                for shamt in 0..64 {
                    push(op, rd, rs1, 0, shamt);
                }
            }
        }
    }
    for op in [Op::Slliw, Op::Srliw, Op::Sraiw] {
        for rd in 0..32 {
            for rs1 in 0..32 {
                for shamt in 0..32 {
                    push(op, rd, rs1, 0, shamt);
                }
            }
        }
    }

    for op in [Op::Lb, Op::Lbu, Op::Lh, Op::Lhu, Op::Lw, Op::Lwu, Op::Ld] {
        if full_12bit {
            let mut shard_cursor = 0usize;
            for rd in 0..32 {
                for rs1 in 0..32 {
                    for imm in -2048..=2047 {
                        if shard_cursor % shard_12bit_count == shard_12bit_index {
                            push(op, rd, rs1, 0, imm);
                        }
                        shard_cursor += 1;
                    }
                }
            }
        } else {
            for rd in [0, 1, 31] {
                for rs1 in [0, 1, 31] {
                    for imm in -2048..=2047 {
                        push(op, rd, rs1, 0, imm);
                    }
                }
            }
            for rd in 0..32 {
                for rs1 in 0..32 {
                    for imm in [-2048, -1, 0, 1, 2047] {
                        push(op, rd, rs1, 0, imm);
                    }
                }
            }
        }
    }
    for op in [
        Op::Sb,
        Op::Sh,
        Op::Sw,
        Op::Sd,
        Op::Beq,
        Op::Bne,
        Op::Blt,
        Op::Bge,
        Op::Bltu,
        Op::Bgeu,
    ] {
        if full_12bit {
            let mut shard_cursor = 0usize;
            for rs1 in 0..32 {
                for rs2 in 0..32 {
                    for imm in -2048..=2047 {
                        if shard_cursor % shard_12bit_count == shard_12bit_index {
                            push(op, 0, rs1, rs2, imm);
                        }
                        shard_cursor += 1;
                    }
                }
            }
        } else {
            for rs1 in [0, 1, 31] {
                for rs2 in [0, 1, 31] {
                    for imm in -2048..=2047 {
                        push(op, 0, rs1, rs2, imm);
                    }
                }
            }
            for rs1 in 0..32 {
                for rs2 in 0..32 {
                    for imm in [-2048, -1, 0, 1, 2047] {
                        push(op, 0, rs1, rs2, imm);
                    }
                }
            }
        }
    }

    push(Op::Fence, 0, 0, 0, 0);

    let uj_imms: Box<dyn Iterator<Item = i32>> = if full_uj {
        Box::new((-1_048_576..=1_048_575).step_by(2))
    } else {
        Box::new(
            [
                i32::MIN,
                -1_048_576,
                -4096,
                -4,
                -1,
                0,
                1,
                4,
                4096,
                1_048_574,
                1_048_575,
                i32::MAX,
            ]
            .into_iter(),
        )
    };
    for (uj_index, imm) in uj_imms.enumerate() {
        if uj_index % uj_shard_count != uj_shard_index {
            continue;
        }
        for rd in 0..32 {
            push(Op::Lui, rd, 0, 0, imm);
            push(Op::Auipc, rd, 0, 0, imm);
            push(Op::Jal, rd, 0, 0, imm);
        }
    }

    for rd in 0..32 {
        for rs1 in 0..32 {
            for imm in [-2048, -5, -4, -1, 0, 1, 3, 4, 7, 2047] {
                push(Op::Jalr, rd, rs1, 0, imm);
            }
        }
    }

    cases
}

fn parse_env_usize(name: &str) -> Option<usize> {
    std::env::var(name).ok().map(|value| {
        value
            .parse()
            .unwrap_or_else(|_| panic!("{name} must be a non-negative integer, got {value:?}"))
    })
}

fn spawn_lean_oracle(with_rows: bool) -> std::process::Child {
    let mut command = Command::new("lake");
    command
        .args([
            "env",
            "lean",
            "--run",
            "tools/transpiler-diff/LeanOracle.lean",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped());
    if with_rows {
        command.env("ZISK_DIFF_LEAN_ROWS", "1");
    }
    command.spawn().expect("spawn Lean oracle")
}

fn case_line(case: &Case) -> String {
    format!(
        "{}\t{}\t{}\t{}\t{}\t{}\t{}",
        case.id,
        mnemonic(case.op),
        case.paddr,
        case.rd,
        case.rs1,
        case.rs2,
        case.imm
    )
}

fn parse_rows_line(line: &str) -> (LeanDigest, Vec<Row>) {
    let fields: Vec<_> = line.split('\t').collect();
    assert_eq!(fields.len(), 4, "bad Lean rows line: {line}");
    let digest = LeanDigest {
        id: fields[0].parse().expect("Lean id"),
        row_count: fields[1].parse().expect("Lean row count"),
        hash: fields[2].parse().expect("Lean hash"),
    };
    let rows = if fields[3].is_empty() {
        Vec::new()
    } else {
        fields[3].split(';').map(parse_row).collect()
    };
    (digest, rows)
}

fn parse_row(text: &str) -> Row {
    let f: Vec<_> = text.split(',').collect();
    assert_eq!(f.len(), 17, "bad Lean row: {text}");
    Row {
        paddr: f[0].parse().unwrap(),
        op: f[1].parse().unwrap(),
        a_src: f[2].parse().unwrap(),
        a_use_sp_imm1: f[3].parse().unwrap(),
        a_offset_imm0: f[4].parse().unwrap(),
        b_src: f[5].parse().unwrap(),
        b_use_sp_imm1: f[6].parse().unwrap(),
        b_offset_imm0: f[7].parse().unwrap(),
        store: f[8].parse().unwrap(),
        store_offset: f[9].parse().unwrap(),
        store_pc: f[10] == "1",
        set_pc: f[11] == "1",
        ind_width: f[12].parse().unwrap(),
        jmp_offset1: f[13].parse().unwrap(),
        jmp_offset2: f[14].parse().unwrap(),
        is_external_op: f[15] == "1",
        m32: f[16] == "1",
    }
}

fn rust_rows(case: &Case) -> Vec<Row> {
    let mut insts: HashMap<u64, ZiskInstBuilder> = HashMap::new();
    let mut ctx = Riscv2ZiskContext {
        insts: &mut insts,
        input_precompile: None,
        output_precompile: None,
        input_precompile_reg: None,
        output_precompile_reg: None,
    };
    let i = riscv_inst(case);
    ctx.convert(&i, &[]);
    let mut keys: Vec<_> = insts.keys().copied().collect();
    keys.sort_unstable();
    keys.into_iter()
        .map(|key| project(&insts[&key].i))
        .collect()
}

fn riscv_inst(case: &Case) -> RiscvInstruction {
    RiscvInstruction {
        rom_address: case.paddr,
        t: op_type(case.op).to_string(),
        inst: mnemonic(case.op).to_string(),
        rd: case.rd,
        rs1: case.rs1,
        rs2: case.rs2,
        imm: case.imm,
        ..Default::default()
    }
}

fn project(i: &ZiskInst) -> Row {
    Row {
        paddr: i.paddr,
        op: i.op as u64,
        a_src: i.a_src,
        a_use_sp_imm1: i.a_use_sp_imm1,
        a_offset_imm0: i.a_offset_imm0,
        b_src: i.b_src,
        b_use_sp_imm1: i.b_use_sp_imm1,
        b_offset_imm0: i.b_offset_imm0,
        store: i.store,
        store_offset: i.store_offset,
        store_pc: i.store_pc,
        set_pc: i.set_pc,
        ind_width: i.ind_width,
        jmp_offset1: i.jmp_offset1,
        jmp_offset2: i.jmp_offset2,
        is_external_op: i.is_external_op,
        m32: i.m32,
    }
}

fn rows_hash(rows: &[Row]) -> u64 {
    rows.iter().fold(14_695_981_039_346_656_037, row_hash)
}

fn row_hash(h: u64, row: &Row) -> u64 {
    let mut h = h;
    for field in [
        row.paddr,
        row.op,
        row.a_src,
        row.a_use_sp_imm1,
        row.a_offset_imm0,
        row.b_src,
        row.b_use_sp_imm1,
        row.b_offset_imm0,
        row.store,
        row.store_offset as u64,
        row.store_pc as u64,
        row.set_pc as u64,
        row.ind_width,
        row.jmp_offset1 as u64,
        row.jmp_offset2 as u64,
        row.is_external_op as u64,
        row.m32 as u64,
    ] {
        h = (h ^ field).wrapping_mul(1_099_511_628_211);
    }
    h
}

fn diff_rows(left: &[Row], right: &[Row]) -> String {
    let mut out = String::new();
    if left.len() != right.len() {
        let _ = write!(out, "row_count:{}!={};", left.len(), right.len());
    }
    for (idx, (l, r)) in left.iter().zip(right.iter()).enumerate() {
        macro_rules! diff {
            ($field:ident) => {
                if l.$field != r.$field {
                    let _ = write!(
                        out,
                        " row[{idx}].{}:{:?}!={:?};",
                        stringify!($field),
                        l.$field,
                        r.$field
                    );
                }
            };
        }
        diff!(paddr);
        diff!(op);
        diff!(a_src);
        diff!(a_use_sp_imm1);
        diff!(a_offset_imm0);
        diff!(b_src);
        diff!(b_use_sp_imm1);
        diff!(b_offset_imm0);
        diff!(store);
        diff!(store_offset);
        diff!(store_pc);
        diff!(set_pc);
        diff!(ind_width);
        diff!(jmp_offset1);
        diff!(jmp_offset2);
        diff!(is_external_op);
        diff!(m32);
    }
    out
}

fn mnemonic(op: Op) -> &'static str {
    match op {
        Op::Add => "add",
        Op::Sub => "sub",
        Op::Sll => "sll",
        Op::Slt => "slt",
        Op::Sltu => "sltu",
        Op::Xor => "xor",
        Op::Srl => "srl",
        Op::Sra => "sra",
        Op::Or => "or",
        Op::And => "and",
        Op::Addw => "addw",
        Op::Subw => "subw",
        Op::Sllw => "sllw",
        Op::Srlw => "srlw",
        Op::Sraw => "sraw",
        Op::Addi => "addi",
        Op::Slli => "slli",
        Op::Slti => "slti",
        Op::Sltiu => "sltiu",
        Op::Xori => "xori",
        Op::Srli => "srli",
        Op::Srai => "srai",
        Op::Ori => "ori",
        Op::Andi => "andi",
        Op::Addiw => "addiw",
        Op::Slliw => "slliw",
        Op::Srliw => "srliw",
        Op::Sraiw => "sraiw",
        Op::Beq => "beq",
        Op::Bne => "bne",
        Op::Blt => "blt",
        Op::Bge => "bge",
        Op::Bltu => "bltu",
        Op::Bgeu => "bgeu",
        Op::Lb => "lb",
        Op::Lbu => "lbu",
        Op::Lh => "lh",
        Op::Lhu => "lhu",
        Op::Lw => "lw",
        Op::Lwu => "lwu",
        Op::Ld => "ld",
        Op::Sb => "sb",
        Op::Sh => "sh",
        Op::Sw => "sw",
        Op::Sd => "sd",
        Op::Lui => "lui",
        Op::Auipc => "auipc",
        Op::Jal => "jal",
        Op::Jalr => "jalr",
        Op::Fence => "fence",
        Op::Mul => "mul",
        Op::Mulh => "mulh",
        Op::Mulhsu => "mulhsu",
        Op::Mulhu => "mulhu",
        Op::Mulw => "mulw",
        Op::Div => "div",
        Op::Divu => "divu",
        Op::Divw => "divw",
        Op::Divuw => "divuw",
        Op::Rem => "rem",
        Op::Remu => "remu",
        Op::Remw => "remw",
        Op::Remuw => "remuw",
    }
}

fn op_type(op: Op) -> &'static str {
    match op {
        Op::Add
        | Op::Sub
        | Op::Sll
        | Op::Slt
        | Op::Sltu
        | Op::Xor
        | Op::Srl
        | Op::Sra
        | Op::Or
        | Op::And
        | Op::Addw
        | Op::Subw
        | Op::Sllw
        | Op::Srlw
        | Op::Sraw
        | Op::Mul
        | Op::Mulh
        | Op::Mulhsu
        | Op::Mulhu
        | Op::Mulw
        | Op::Div
        | Op::Divu
        | Op::Divw
        | Op::Divuw
        | Op::Rem
        | Op::Remu
        | Op::Remw
        | Op::Remuw => "R",
        Op::Sb | Op::Sh | Op::Sw | Op::Sd => "S",
        Op::Beq | Op::Bne | Op::Blt | Op::Bge | Op::Bltu | Op::Bgeu => "B",
        Op::Lui | Op::Auipc => "U",
        Op::Jal => "J",
        _ => "I",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zisk_core::{SRC_IMM, SRC_IND, STORE_NONE, STORE_REG};

    #[test]
    fn builder_rewrites_x0_register_source_to_zero_immediate() {
        let mut b = ZiskInstBuilder::new(0x1000);
        b.src_a("reg", 0, false);
        b.src_b("reg", 0, false);
        assert_eq!(b.i.a_src, SRC_IMM);
        assert_eq!(b.i.a_offset_imm0, 0);
        assert_eq!(b.i.b_src, SRC_IMM);
        assert_eq!(b.i.b_offset_imm0, 0);
    }

    #[test]
    fn builder_elides_store_to_x0() {
        let mut b = ZiskInstBuilder::new(0x1000);
        b.store("reg", 0, false, false);
        assert_eq!(b.i.store, STORE_NONE);
        assert!(!b.i.store_pc);
    }

    #[test]
    fn builder_splits_signed_immediate_as_u64_chunks() {
        let mut b = ZiskInstBuilder::new(0x1000);
        b.src_b("imm", (-2048_i32) as u64, false);
        assert_eq!(b.i.b_src, SRC_IMM);
        assert_eq!(b.i.b_use_sp_imm1, 0xffff_ffff);
        assert_eq!(b.i.b_offset_imm0, 0xffff_f800);
    }

    #[test]
    fn builder_sets_store_pc_on_register_store() {
        let mut b = ZiskInstBuilder::new(0x1000);
        b.store_pc("reg", 1, false);
        assert_eq!(b.i.store, STORE_REG);
        assert_eq!(b.i.store_offset, 1);
        assert!(b.i.store_pc);
    }

    #[test]
    fn builder_sets_pc_and_ind_width() {
        let mut b = ZiskInstBuilder::new(0x1000);
        b.set_pc();
        b.ind_width(8);
        b.src_b("ind", 12, false);
        assert!(b.i.set_pc);
        assert_eq!(b.i.ind_width, 8);
        assert_eq!(b.i.b_src, SRC_IND);
    }

    #[test]
    fn builder_sets_m32_from_w_opcode_name() {
        let mut b = ZiskInstBuilder::new(0x1000);
        b.op("add_w").unwrap();
        assert!(b.i.m32);

        let mut b = ZiskInstBuilder::new(0x1000);
        b.op("add").unwrap();
        assert!(!b.i.m32);
        assert_eq!(b.i.a_src, 0);
    }

    #[test]
    fn rust_hash_matches_row_field_order_smoke_test() {
        let row = Row {
            paddr: 1,
            op: 2,
            a_src: 3,
            a_use_sp_imm1: 4,
            a_offset_imm0: 5,
            b_src: 6,
            b_use_sp_imm1: 7,
            b_offset_imm0: 8,
            store: 9,
            store_offset: -1,
            store_pc: true,
            set_pc: false,
            ind_width: 10,
            jmp_offset1: -2,
            jmp_offset2: 11,
            is_external_op: true,
            m32: false,
        };
        assert_eq!(rows_hash(&[row]), 6_815_333_013_191_349_912);
    }
}
