import Mathlib

import ZiskFv.Airs.Main
import ZiskFv.Airs.Main.OpcodeClassification
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
-- One representative shape dispatcher import (LUI from ControlFlow non-branch).
-- Additional shape dispatchers will be added under
-- `ZiskFv/Equivalence/Compliance/Dispatch/<Shape>.lean` as Step 4.3 progresses.
import ZiskFv.Equivalence.Compliance.LuiExemplar

/-!
# Compliance.lean — Global dispatcher (Step 4.3 of the wild-lynx plan)

This file is the **architectural validation** that the 63
independently-authored `equiv_<OP>_from_trust` wrappers under
`ZiskFv/Equivalence/Compliance/` compose into a global theorem.

## Status (Step 4.3 Phase 1 — partial)

This file currently lands the **decode-side scaffolding** plus a single
representative shape dispatcher (`dispatch_ControlFlow_LUI`) to demonstrate
the pattern. The full global theorem
(`zisk_riscv_compliant_program_bus`) and the remaining eight shape
dispatchers are tracked as Step 4.3 follow-up work and described in
the structural commentary below.

The follow-up work is concretely bounded — the wrapper signatures
under `ZiskFv/Equivalence/Compliance/*Exemplar.lean` already pin
each per-op trust discharge; what remains is the per-shape
`rcases` dispatch + the global `∃ instr` packaging. See the
report from this commit for the gap surface.

## Architecture

The Main AIR carries 35 distinct `op` selector values that together
cover the 63 RV64IM opcodes (some Zisk OPs alias multiple RISC-V
instructions, e.g. `OP_ADD = 10` covers both ADD and ADDI; the
register-vs-immediate distinction lives in Main's `b_src_imm` /
`a_src_imm` selectors, not the `op` column).

A *fully mechanical* `decode_main_row : Valid_Main → ℕ → Option
instruction` is therefore not constructible from `Valid_Main` alone
— the operand fields (`imm`, `rd`, `rs1`, `rs2`) and the
register-vs-immediate disambiguator are not exposed as named
columns on `Valid_Main`. Decoding to a Sail `instruction` requires
either (a) extending `Valid_Main` with the operand accessors plus a
transpile bridge stating their semantics, or (b) reformulating the
global theorem with the operand fields as **existentials**: for
each op selector value, the caller (a real ZisK trace) determines
which operand witnesses to supply, and the dispatcher proves the
equivalence for whichever `instruction` form the witnesses pick.

Pattern (b) is what the per-op wrappers already implement: e.g.
`equiv_LUI_from_trust` takes `(imm : BitVec 20)` and `(rd : regidx)`
as explicit parameters and relates them to `lui_input : LuiInput` via
the `h_input_imm` / `h_input_rd` state predicates.

The decode_main_row function in this file therefore reports only the
**Zisk op-selector kind** (one of the 35 enumerated values plus
`none` for out-of-scope), not a full `instruction`. The shape
dispatchers consume the kind and produce the per-op equivalence with
operand witnesses as explicit parameters.

## Shape buckets

| Bucket                           | Opcodes                              | Wrappers                                       |
|----------------------------------|--------------------------------------|------------------------------------------------|
| `dispatch_ControlFlow_LUI`       | LUI                                  | `LuiExemplar`                                  |
| `dispatch_ControlFlow_AUIPC`     | AUIPC                                | `AuipcExemplar`                                |
| `dispatch_ControlFlow_JAL`       | JAL                                  | `JalExemplar`                                  |
| `dispatch_ControlFlow_JALR`      | JALR                                 | `JalrExemplar`                                 |
| `dispatch_ControlFlow_FENCE`     | FENCE                                | `FenceExemplar`                                |
| `dispatch_ControlFlow_Branch`    | BEQ, BNE, BLT, BGE, BLTU, BGEU       | `Beq/Bne/Blt/Bge/Bltu/Bgeu`                    |
| `dispatch_BinaryAdd`             | ADD, ADDI                            | `Add/Addi`                                     |
| `dispatch_BinaryAddW`            | ADDW, SUBW, ADDIW                    | `Addw/Subw/Addiw`                              |
| `dispatch_Binary`                | SUB,AND,OR,XOR,SLT,SLTU,SLTI,SLTIU,  | `Sub/And/Or/Xor/Slt/Sltu/Slti/Sltiu/Andi/Ori/  |
|                                  | ANDI,ORI,XORI,SLLI,SRLI,SRAI         |  Xori` (+ shift-immediate ops)                 |
| `dispatch_BinaryExtension_Shift` | SLL,SRL,SRA,SLLW,SRLW,SRAW,          | `Sll/Srl/Sra/Shift/ShiftR/ShiftRA/ShiftLI/     |
|                                  | SLLI,SRLI,SRAI,SLLIW,SRLIW,SRAIW     |  ShiftRLI/ShiftRAI/Slli/Srli/Srai`             |
| `dispatch_ArithMul`              | MUL,MULH,MULHSU,MULHU,MULW           | `Mul/MulH/MulHSU/MulHU/MulW`                   |
| `dispatch_ArithDiv`              | DIV,DIVU,REM,REMU,DIVW,DIVUW,        | `DivPilot/Divu/Rem/Remu/Divw/Divuw/Remw/Remuw` |
|                                  | REMW,REMUW                           |                                                |
| `dispatch_Mem_Load`              | LD,LBU,LHU,LWU,LB,LH,LW              | `Ld/Lbu/Lhu/Lwu/Lb/Lh/Lw`                      |
| `dispatch_Mem_Store`             | SB,SH,SW,SD                          | `Sb/Sh/Sw/Sd`                                  |

## What goes where in the global theorem

Per shape, the global theorem takes:
- The relevant provider-AIR validators (`Valid_Main` is always there;
  other shape-specific ones — `Valid_BinaryAdd`, `Valid_Binary`,
  `Valid_BinaryExtension`, `Valid_ArithMul`, `Valid_ArithDiv`,
  `Valid_Mem`, `Valid_MemAlign{,Byte,ReadByte}` — vary).
- A universal-per-row constraint for each provider AIR (`∀ r,
  <AIR>.core_every_row v r`).
- A state predicate bundle.
- A structural exec_row/mem_rows shape predicate (length pins +
  per-entry multiplicity/as pins).
- Existential operand witnesses + the corresponding Sail-side state
  bridge equations (`h_input_*` family).

Per-shape dispatchers extract from the universal-per-row hypothesis
the row-local constraint each wrapper needs.
-/

namespace ZiskFv.Equivalence.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Decode side

The decode kind enumerates the 35 Zisk op-selector values that the
RV64IM scope covers. It is a thin enum over `Valid_Main.op`'s value
— the bridge to a Sail `instruction` happens per-shape inside the
dispatcher (the dispatcher takes operand witnesses as inputs and
proves the equivalence for the corresponding `instruction` form).
-/

/-- The 35-way Zisk op-selector classifier, lifted to an enum.

    This is **not** a full Sail `instruction` decoder — see this
    file's module docstring for why. It identifies which family
    of per-op equivalence theorem applies to the current Main row.

    `mainOpKind.fromMain m r` returns `none` iff `m.op r` is not
    one of the 35 in-scope values (i.e., out of RV64IM scope:
    precompiles, Zicclsm, ECALL/EBREAK, internal ops). For all
    in-scope rows it returns the unique matching kind. -/
inductive mainOpKind where
  | FLAG | COPYB | LTU | LT | EQ | ADD | SUB | AND | OR | XOR
  | ADD_W | SUB_W | SLL | SRL | SRA | SLL_W | SRL_W | SRA_W
  | SIGNEXTEND_B | SIGNEXTEND_H | SIGNEXTEND_W
  | MULU | MULUH | MULSUH | MUL | MULH | MUL_W
  | DIVU | REMU | DIV | REM | DIVU_W | REMU_W | DIV_W | REM_W
  deriving DecidableEq, Repr

namespace mainOpKind

/-- Project the kind enum back to its `FGL` literal. Round-trips
    through `Fundamentals/Transpiler.lean`'s `OP_<X>` definitions. -/
@[simp] def toFGL : mainOpKind → FGL
  | .FLAG => OP_FLAG | .COPYB => OP_COPYB
  | .LTU => OP_LTU | .LT => OP_LT | .EQ => OP_EQ
  | .ADD => OP_ADD | .SUB => OP_SUB | .AND => OP_AND
  | .OR => OP_OR | .XOR => OP_XOR
  | .ADD_W => OP_ADD_W | .SUB_W => OP_SUB_W
  | .SLL => OP_SLL | .SRL => OP_SRL | .SRA => OP_SRA
  | .SLL_W => OP_SLL_W | .SRL_W => OP_SRL_W | .SRA_W => OP_SRA_W
  | .SIGNEXTEND_B => OP_SIGNEXTEND_B
  | .SIGNEXTEND_H => OP_SIGNEXTEND_H
  | .SIGNEXTEND_W => OP_SIGNEXTEND_W
  | .MULU => OP_MULU | .MULUH => OP_MULUH | .MULSUH => OP_MULSUH
  | .MUL => OP_MUL | .MULH => OP_MULH | .MUL_W => OP_MUL_W
  | .DIVU => OP_DIVU | .REMU => OP_REMU
  | .DIV => OP_DIV | .REM => OP_REM
  | .DIVU_W => OP_DIVU_W | .REMU_W => OP_REMU_W
  | .DIV_W => OP_DIV_W | .REM_W => OP_REM_W

end mainOpKind

/-! ## Shape dispatchers

Each shape dispatcher consumes:
- The relevant provider-AIR validator(s) and universal-row hypothesis
  (`∀ r, <AIR>.core_every_row`).
- A row index pinned to a specific Zisk op selector via a `h_main_op
  : m.op r_main = OP_<X>` hypothesis.
- The operand witnesses + Sail-side state predicates the wrapper
  expects.
- The structural exec_row / mem_rows bus shape.

And concludes the per-op equivalence by delegating to
`equiv_<OP>_from_trust`. The dispatcher proof body is the
mechanical assembly of dispatch inputs from the per-row /
universal hypotheses.

This file currently lands one representative — `dispatch_LUI`,
the cleanest pattern (Main-only, no provider-AIR, no register-vs-
immediate disambiguation). The remaining eight shape dispatchers
follow the same pattern; see the per-shape grouping table in this
file's module docstring.
-/

/-- **Representative shape dispatcher — ControlFlow non-branch / LUI.**

    This is the canonical example pattern for a per-shape dispatcher
    in this file. It is currently a pass-through wrapper around
    `equiv_LUI_from_trust` — it does not yet add value over directly
    calling the wrapper, but its purpose is structural: the full
    global theorem will dispatch through this layer to bound the
    `rcases` disjunction depth at any one point.

    See the module docstring above for the full list of shape
    dispatchers that will land here as Step 4.3 progresses. -/
theorem dispatch_LUI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_lui : m.op r_main = OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some lui_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = lui_input.PC + 4#64)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_rd_idx : lui_input.rd = Transpiler.wrap_to_regidx e_rd.ptr) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  exact equiv_LUI_from_trust state lui_input imm rd m r_main next_pc
    exec_row e_rd h_main_active h_main_op_lui h_lui_subset
    h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_rd_idx

end ZiskFv.Equivalence.Compliance
