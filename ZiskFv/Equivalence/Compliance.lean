import Mathlib

import ZiskFv.Airs.Main
import ZiskFv.Airs.Main.OpcodeClassification
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
-- One representative shape dispatcher import (LUI from ControlFlow non-branch).
-- Additional shape dispatchers will be added under
-- `ZiskFv/Equivalence/Compliance/Dispatch/<Shape>.lean` as Step 4.3 progresses.
import ZiskFv.Equivalence.Compliance.LuiExemplar
import ZiskFv.Equivalence.Compliance.AuipcExemplar
import ZiskFv.Equivalence.Compliance.JalExemplar
import ZiskFv.Equivalence.Compliance.JalrExemplar
import ZiskFv.Equivalence.Compliance.FenceExemplar
import ZiskFv.Equivalence.Compliance.BeqExemplar
import ZiskFv.Equivalence.Compliance.BneExemplar
import ZiskFv.Equivalence.Compliance.BltExemplar
import ZiskFv.Equivalence.Compliance.BgeExemplar
import ZiskFv.Equivalence.Compliance.BltuExemplar
import ZiskFv.Equivalence.Compliance.BgeuExemplar
import ZiskFv.Equivalence.Compliance.AddExemplar
import ZiskFv.Equivalence.Compliance.AddiExemplar
import ZiskFv.Equivalence.Compliance.AddwExemplar
import ZiskFv.Equivalence.Compliance.SubwExemplar
import ZiskFv.Equivalence.Compliance.AddiwExemplar
import ZiskFv.Equivalence.Compliance.SubExemplar
import ZiskFv.Equivalence.Compliance.AndExemplar
import ZiskFv.Equivalence.Compliance.AndiExemplar
import ZiskFv.Equivalence.Compliance.OrExemplar
import ZiskFv.Equivalence.Compliance.OriExemplar
import ZiskFv.Equivalence.Compliance.XorExemplar
import ZiskFv.Equivalence.Compliance.XoriExemplar
import ZiskFv.Equivalence.Compliance.SltExemplar
import ZiskFv.Equivalence.Compliance.SltuExemplar
import ZiskFv.Equivalence.Compliance.SltiExemplar
import ZiskFv.Equivalence.Compliance.SltiuExemplar
import ZiskFv.Equivalence.Compliance.SllExemplar
import ZiskFv.Equivalence.Compliance.SrlExemplar
import ZiskFv.Equivalence.Compliance.SraExemplar
import ZiskFv.Equivalence.Compliance.SlliExemplar
import ZiskFv.Equivalence.Compliance.SrliExemplar
import ZiskFv.Equivalence.Compliance.SraiExemplar
import ZiskFv.Equivalence.Compliance.ShiftExemplar
import ZiskFv.Equivalence.Compliance.ShiftLIExemplar
import ZiskFv.Equivalence.Compliance.ShiftRExemplar
import ZiskFv.Equivalence.Compliance.ShiftRLIExemplar
import ZiskFv.Equivalence.Compliance.ShiftRAExemplar
import ZiskFv.Equivalence.Compliance.ShiftRAIExemplar
import ZiskFv.Equivalence.Compliance.MulExemplar
import ZiskFv.Equivalence.Compliance.MulHExemplar
import ZiskFv.Equivalence.Compliance.MulHUExemplar
import ZiskFv.Equivalence.Compliance.MulHSUExemplar
import ZiskFv.Equivalence.Compliance.MulWExemplar
import ZiskFv.Equivalence.Compliance.DivPilot
import ZiskFv.Equivalence.Compliance.DivuExemplar
import ZiskFv.Equivalence.Compliance.DivwExemplar
import ZiskFv.Equivalence.Compliance.DivuwExemplar
import ZiskFv.Equivalence.Compliance.RemExemplar
import ZiskFv.Equivalence.Compliance.RemuExemplar
import ZiskFv.Equivalence.Compliance.RemwExemplar
import ZiskFv.Equivalence.Compliance.RemuwExemplar
import ZiskFv.Equivalence.Compliance.LdExemplar
import ZiskFv.Equivalence.Compliance.LbuExemplar
import ZiskFv.Equivalence.Compliance.LhuExemplar
import ZiskFv.Equivalence.Compliance.LwuExemplar
import ZiskFv.Equivalence.Compliance.LbExemplar
import ZiskFv.Equivalence.Compliance.LhExemplar
import ZiskFv.Equivalence.Compliance.LwExemplar
import ZiskFv.Equivalence.Compliance.SbExemplar
import ZiskFv.Equivalence.Compliance.ShExemplar
import ZiskFv.Equivalence.Compliance.SwExemplar
import ZiskFv.Equivalence.Compliance.SdExemplar

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
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Airs.Binary
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.Airs.Mem

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
lemma dispatch_LUI
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

/-! ### ControlFlow non-branch dispatchers (AUIPC, JAL, JALR, FENCE)

Pass-through dispatchers mirroring `dispatch_LUI`. Each is a thin
delegation to the corresponding `equiv_<OP>_from_trust` wrapper.
The shape grouping is `ControlFlow_NonBranch`; each opcode in the
shape gets its own dispatcher because the wrappers' conclusion
shapes (`instruction.UTYPE / .JAL / .JALR / .FENCE`) and operand
inputs differ — a single uniform-signature dispatcher across the
shape would require Phase 3's shape-envelope abstraction. -/

/-- **Dispatcher for AUIPC.** Pass-through to `equiv_AUIPC_from_trust`. -/
lemma dispatch_AUIPC
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_auipc : m.op r_main = OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  equiv_AUIPC_from_trust state auipc_input imm rd exec_row e_rd nextPC_val
    m r_main next_pc h_main_active h_main_op_auipc h_auipc_subset
    h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq h_rd_idx
    h_no_wrap h_lo_bound h_pc_offset_lt_2_32

/-- **Dispatcher for JAL.** Pass-through to `equiv_JAL_from_trust`. -/
lemma dispatch_JAL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jal : m.op r_main = OP_FLAG)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 :=
  equiv_JAL_from_trust state jal_input imm rd misa_val m r_main next_pc
    exec_row e_rd nextPC_val h_main_active h_main_op_jal h_jal_subset
    h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_not_throws h_success h_nextPC_option h_rd_idx
    h_pc_bound h_lo_bound h_pc_offset_lt_2_32

/-- **Dispatcher for JALR.** Pass-through to `equiv_JALR_from_trust`. -/
lemma dispatch_JALR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jalr : m.op r_main = OP_COPYB)
    (h_jalr_subset :
      ZiskFv.Tactics.JumpArchetype.jalr_subset_holds m r_main next_pc)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 :=
  equiv_JALR_from_trust state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd nextPC_val m r_main next_pc
    h_main_active h_main_op_jalr h_jalr_subset
    h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
    h_cur_privilege h_mseccfg
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_success h_nextPC_option h_rd_idx
    h_pc_bound h_lo_bound h_pc_offset_lt_2_32

/-- **Dispatcher for FENCE.** Pass-through to `equiv_FENCE_from_trust`. -/
lemma dispatch_FENCE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_fence : main.op r_main = OP_FLAG)
    (h_input_pc : state.regs.get? Register.PC = .some fence_input.PC)
    (h_input_priv :
      state.regs.get? Register.cur_privilege = .some Privilege.Machine)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_FENCE_pure fence_input).nextPC) :
    execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_FENCE_from_trust state fence_input fm pred succ rs rd main r_main
    exec_row h_main_active h_main_op_fence h_input_pc h_input_priv
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-! ### Branch dispatchers (BEQ, BNE, BLT, BGE, BLTU, BGEU)

All six branches share the exact same signature shape (modulo
type/name renaming). Each dispatcher is a thin pass-through to
its corresponding `equiv_<OP>_from_trust` wrapper. -/

/-- **Dispatcher for BEQ.** Pass-through to `equiv_BEQ_from_trust`. -/
lemma dispatch_BEQ
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (beq_input.PC + BitVec.signExtend 64 beq_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_BEQ_from_trust state beq_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-- **Dispatcher for BNE.** Pass-through to `equiv_BNE_from_trust`. -/
lemma dispatch_BNE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bne_input.PC + BitVec.signExtend 64 bne_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_BNE_from_trust state bne_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-- **Dispatcher for BLT.** Pass-through to `equiv_BLT_from_trust`. -/
lemma dispatch_BLT
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (blt_input.PC + BitVec.signExtend 64 blt_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_BLT_from_trust state blt_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-- **Dispatcher for BGE.** Pass-through to `equiv_BGE_from_trust`. -/
lemma dispatch_BGE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bge_input : PureSpec.BgeInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bge_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bge_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bge_input.PC + BitVec.signExtend 64 bge_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGE_pure bge_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_BGE_from_trust state bge_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-- **Dispatcher for BLTU.** Pass-through to `equiv_BLTU_from_trust`. -/
lemma dispatch_BLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_BLTU_from_trust state bltu_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-- **Dispatcher for BGEU.** Pass-through to `equiv_BGEU_from_trust`. -/
lemma dispatch_BGEU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput) (imm : BitVec 13) (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = (bus_effect exec_row [] state).2 :=
  equiv_BGEU_from_trust state bgeu_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_target_aligned h_exec_len h_e0_mult h_e1_mult h_nextPC_matches

/-! ### BinaryAdd dispatchers (ADD, ADDI) -/

/-- **Dispatcher for ADD.** Pass-through to `equiv_ADD_from_trust`. -/
lemma dispatch_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_add : m.op r_main = OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok add_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok add_input.r2_val state)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some add_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : add_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_ADD_from_trust state add_input r1 r2 rd m b r_main exec_row e0 e1 e2
    h_main_active h_main_op_add h_main_subset h_b_core h_lane_rd
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for ADDI.** Pass-through to `equiv_ADDI_from_trust`. -/
lemma dispatch_ADDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addi : m.op r_main = OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addi_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_ADDI_from_trust state addi_input r1 rd imm m b r_main exec_row e0 e1 e2
    h_main_active h_main_op_addi h_main_subset h_b_core h_addi_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-! ### BinaryAddW dispatchers (ADDW, SUBW, ADDIW) -/

/-- **Dispatcher for ADDW.** Pass-through to `equiv_ADDW_from_trust`. -/
lemma dispatch_ADDW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addw : m.op r_main = OP_ADD_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok addw_input.r2_val state)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addw_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_ADDW_from_trust state addw_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_addw h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for SUBW.** Pass-through to `equiv_SUBW_from_trust`. -/
lemma dispatch_SUBW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_subw : m.op r_main = OP_SUB_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok subw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok subw_input.r2_val state)
    (h_input_rd : subw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some subw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : subw_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SUBW_from_trust state subw_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_subw h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for ADDIW.** Pass-through to `equiv_ADDIW_from_trust`. -/
lemma dispatch_ADDIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_addiw : m.op r_main = OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addiw_input.r1_val state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addiw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addiw_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_ADDIW_from_trust state addiw_input r1 rd imm m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_addiw h_addiw_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-! ### Binary dispatchers (SUB, AND, OR, XOR, SLT, SLTU + I-type variants)

11 ops over the `Binary` shape: 6 R-type (SUB, AND, OR, XOR, SLT, SLTU)
and 5 I-type (ANDI, ORI, XORI, SLTI, SLTIU). All share the same
`Valid_Main + Valid_Binary` provider footprint and `e0/e1/e2`
memory-bus row shape. Each dispatcher is a thin pass-through to its
`equiv_<OP>_from_trust` wrapper. -/

/-- **Dispatcher for SUB.** -/
lemma dispatch_SUB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sub : m.op r_main = OP_SUB)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sub_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sub_input.r2_val state)
    (h_input_rd : sub_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sub_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sub_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SUB_from_trust state sub_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_sub h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for AND.** -/
lemma dispatch_AND
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_and : m.op r_main = OP_AND)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok and_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok and_input.r2_val state)
    (h_input_rd : and_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some and_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_and_pure and_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : and_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.AND))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_AND_from_trust state and_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_and h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for OR.** -/
lemma dispatch_OR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_or : m.op r_main = OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok or_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok or_input.r2_val state)
    (h_input_rd : or_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some or_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_or_pure or_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : or_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_OR_from_trust state or_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_or h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for XOR.** -/
lemma dispatch_XOR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_xor : m.op r_main = OP_XOR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok xor_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok xor_input.r2_val state)
    (h_input_rd : xor_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some xor_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : xor_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_XOR_from_trust state xor_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_xor h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for SLT.** -/
lemma dispatch_SLT
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_slt : m.op r_main = OP_LT)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok slt_input.r2_val state)
    (h_input_rd : slt_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slt_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slt_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLT_from_trust state slt_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_slt h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for SLTU.** -/
lemma dispatch_SLTU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sltu : m.op r_main = OP_LTU)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sltu_input.r2_val state)
    (h_input_rd : sltu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sltu_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLTU_from_trust state sltu_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_sltu h_lane_rd
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for ANDI.** -/
lemma dispatch_ANDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_andi : m.op r_main = OP_AND)
    (h_andi_subset : itype_imm_subset_holds_main m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok andi_input.r1_val state)
    (h_input_imm : andi_input.imm = imm)
    (h_input_rd : andi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some andi_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : andi_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_ANDI_from_trust state andi_input r1 rd imm m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_andi h_andi_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for ORI.** -/
lemma dispatch_ORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_ori : m.op r_main = OP_OR)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok ori_input.r1_val state)
    (h_input_imm : ori_input.imm = imm)
    (h_input_rd : ori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some ori_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : ori_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_ORI_from_trust state ori_input r1 rd imm m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_ori h_ori_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for XORI.** -/
lemma dispatch_XORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_xori : m.op r_main = OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok xori_input.r1_val state)
    (h_input_imm : xori_input.imm = imm)
    (h_input_rd : xori_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some xori_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : xori_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_XORI_from_trust state xori_input r1 rd imm m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_xori h_xori_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for SLTI.** -/
lemma dispatch_SLTI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_slti : m.op r_main = OP_LT)
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slti_input.r1_val state)
    (h_input_imm : slti_input.imm = imm)
    (h_input_rd : slti_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slti_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slti_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLTI_from_trust state slti_input r1 rd imm m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_slti h_slti_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-- **Dispatcher for SLTIU.** -/
lemma dispatch_SLTIU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_sltiu : m.op r_main = OP_LTU)
    (h_sltiu_subset : itype_imm_subset_holds_main m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sltiu_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLTIU_from_trust state sltiu_input r1 rd imm m v r_main exec_row e0 e1 e2
    h_main_active h_main_op_sltiu h_sltiu_subset h_lane_rd
    h_input_r1 h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx

/-! ### BinaryExtension shift dispatchers (12 ops)

64-bit: SLL, SRL, SRA + SLLI, SRLI, SRAI.
32-bit (W): SLLW, SRLW, SRAW + SLLIW, SRLIW, SRAIW.

All share the `Valid_Main + Valid_BinaryExtension` provider footprint
and `e0/e1/e2` memory-bus row shape. The W-immediate wrappers
(SLLIW/SRLIW/SRAIW) extract shamt from the input record directly
(no separate `shamt` parameter), unlike the 64-bit immediates. -/

/-- **Dispatcher for SLL.** -/
lemma dispatch_SLL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sll_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sll_input.r2_val state)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sll_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sll_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLL_from_trust state sll_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRL.** -/
lemma dispatch_SRL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srl_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srl_input.r2_val state)
    (h_input_rd : srl_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srl_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srl_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRL_from_trust state srl_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRA.** -/
lemma dispatch_SRA
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sra_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sra_input.r2_val state)
    (h_input_rd : sra_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sra_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sra_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRA_from_trust state sra_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SLLI.** -/
lemma dispatch_SLLI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slli_input.r1_val state)
    (h_input_shamt : slli_input.shamt = shamt)
    (h_input_rd : slli_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slli_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slli_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLLI_from_trust state slli_input r1 rd shamt m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_shamt h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRLI.** -/
lemma dispatch_SRLI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srli_input.r1_val state)
    (h_input_shamt : srli_input.shamt = shamt)
    (h_input_rd : srli_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srli_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srli_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRLI_from_trust state srli_input r1 rd shamt m v r_main exec_row e0 e1 e2
    h_input_r1 h_input_shamt h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRAI.** -/
lemma dispatch_SRAI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srai_input.r1_val state)
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srai_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srai_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRAI_from_trust state srai_input r1 rd shamt m v r_main exec_row e0 e1 e2
    h_input_r1 h_input_shamt h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SLLW.** -/
lemma dispatch_SLLW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sllw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLLW_from_trust state sllw_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRLW.** -/
lemma dispatch_SRLW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRLW_from_trust state srlw_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRAW.** -/
lemma dispatch_SRAW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraw_input : PureSpec.SrawInput) (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sraw_input.r2_val state)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sraw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRAW_from_trust state sraw_input r1 r2 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SLLIW.** -/
lemma dispatch_SLLIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput) (r1 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slliw_input.r1_val state)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slliw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : slliw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SLLIW_from_trust state slliw_input r1 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRLIW.** -/
lemma dispatch_SRLIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput) (r1 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srliw_input.r1_val state)
    (h_input_rd : srliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srliw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srliw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRLIW_from_trust state srliw_input r1 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-- **Dispatcher for SRAIW.** -/
lemma dispatch_SRAIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraiw_input : PureSpec.SraiwInput) (r1 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraiw_input.r1_val state)
    (h_input_rd : sraiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraiw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : sraiw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction
      (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SRAIW_from_trust state sraiw_input r1 rd m v r_main exec_row e0 e1 e2
    h_input_r1_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op h_lane_rd

/-! ### ArithMul dispatchers (MUL, MULH, MULHU, MULHSU, MULW)

5 ops on the `Valid_Main + Valid_ArithMul` shape. The wrappers
carry many caller burdens (op-bus match witnesses, row constraints,
byte ranges, W-form sign-extension); the dispatchers are pure
pass-throughs. -/

/-- **Dispatcher for MUL.** -/
lemma dispatch_MUL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_mul : m.op r_main = OP_MUL)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mul_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mul_input.r2_val state)
    (h_input_rd : mul_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mul_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mul_pure mul_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mul_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.Low
             signed_rs1 := srs1
             signed_rs2 := srs2 }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_MUL_from_trust state mul_input r1 r2 rd srs1 srs2
    exec_row e0 e1 e2 m r_main v r_a
    h_main_active h_main_op_mul h_match_primary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7 h_row_constraints

/-- **Dispatcher for MULH.** -/
lemma dispatch_MULH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_mulh : m.op r_main = OP_MULH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulh_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulh_input.r2_val state)
    (h_input_rd : mulh_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulh_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulh_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_MULH_from_trust state mulh_input r1 r2 rd
    exec_row e0 e1 e2 m r_main v r_a
    h_main_active h_main_op_mulh h_match_secondary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints

/-- **Dispatcher for MULHU.** -/
lemma dispatch_MULHU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_mulhu : m.op r_main = OP_MULUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulhu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulhu_input.r2_val state)
    (h_input_rd : mulhu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulhu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulhu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_MULHU_from_trust state mulhu_input r1 r2 rd
    exec_row e0 e1 e2 m r_main v r_a
    h_main_active h_main_op_mulhu h_match_secondary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7 h_row_constraints

/-- **Dispatcher for MULHSU.** -/
lemma dispatch_MULHSU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_mulhsu : m.op r_main = OP_MULSUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulhsu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulhsu_input.r2_val state)
    (h_input_rd : mulhsu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulhsu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulhsu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_MULHSU_from_trust state mulhsu_input r1 r2 rd
    exec_row e0 e1 e2 m r_main v r_a
    h_main_active h_main_op_mulhsu h_match_secondary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints

/-- **Dispatcher for MULW.** -/
lemma dispatch_MULW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_mulw : m.op r_main = OP_MUL_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok mulw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok mulw_input.r2_val state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_MULW_pure mulw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : mulw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_op2 :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MULW (r2, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_MULW_from_trust state mulw_input r1 r2 rd
    exec_row e0 e1 e2 m r_main v r_a
    h_main_active h_main_op_mulw h_match_primary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints h_sext_choice h_op1 h_op2

/-! ### ArithDiv dispatchers (DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW)

8 ops on the `Valid_Main + Valid_ArithDiv` shape. The W-variants
carry additional W-form operand bridges and sign-extension witnesses;
the signed variants carry sign-witness booleans + XOR. -/

/-- **Dispatcher for DIV.** -/
lemma dispatch_DIV
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_div : m.op r_main = OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_div_pure div_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : div_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok div_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok div_input.r2_val state)
    (h_input_rd : div_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some div_input.PC)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_DIV_from_trust state div_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_div h_match_primary
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_input_r1 h_input_r2 h_input_rd h_input_pc h_op2_ne h_no_overflow
    h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor

/-- **Dispatcher for DIVU.** -/
lemma dispatch_DIVU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_divu : m.op r_main = OP_DIVU)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divu_input.r2_val state)
    (h_input_rd : divu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : divu_input.r2_val.toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_DIVU_from_trust state divu_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_divu h_match_primary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7 h_row_constraints h_op2_ne

/-- **Dispatcher for DIVW.** -/
lemma dispatch_DIVW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_divw : m.op r_main = OP_DIV_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divw_input.r2_val state)
    (h_input_rd : divw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_op2 :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_DIVW_from_trust state divw_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_divw h_match_primary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
    h_sext_choice h_op1 h_op2 h_op2_ne h_no_overflow

/-- **Dispatcher for DIVUW.** -/
lemma dispatch_DIVUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_divuw : m.op r_main = OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok divuw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok divuw_input.r2_val state)
    (h_input_rd : divuw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some divuw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : divuw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_op2 : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_DIVUW_from_trust state divuw_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_divuw h_match_primary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints h_sext_choice h_op1 h_op2 h_op2_ne

/-- **Dispatcher for REM.** -/
lemma dispatch_REM
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_rem : m.op r_main = OP_REM)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : rem_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok rem_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok rem_input.r2_val state)
    (h_input_rd : rem_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some rem_input.PC)
    (h_op2_ne : rem_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (rem_input.r1_val.toInt = -(2:ℤ)^63 ∧ rem_input.r2_val.toInt = -1))
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_REM_from_trust state rem_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_rem h_match_secondary
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_input_r1 h_input_r2 h_input_rd h_input_pc h_op2_ne h_no_overflow
    h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor

/-- **Dispatcher for REMU.** -/
lemma dispatch_REMU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_remu : m.op r_main = OP_REMU)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remu_input.r2_val state)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remu_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remu_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : remu_input.r2_val.toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_REMU_from_trust state remu_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_remu h_match_secondary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h0 h1 h2 h3 h4 h5 h6 h7 h_row_constraints h_op2_ne

/-- **Dispatcher for REMW.** -/
lemma dispatch_REMW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_remw : m.op r_main = OP_REM_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remw_input.r2_val state)
    (h_input_rd : remw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - (v.np r_a).val * (2:ℤ)^32)
    (h_op2 :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_REMW_from_trust state remw_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_remw h_match_secondary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
    h_sext_choice h_op1 h_op2 h_op2_ne h_no_overflow_w

/-- **Dispatcher for REMUW.** -/
lemma dispatch_REMUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_remuw : m.op r_main = OP_REMU_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok remuw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok remuw_input.r2_val state)
    (h_input_rd : remuw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some remuw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : remuw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((e2.x4.val = 0 ∧ e2.x5.val = 0 ∧ e2.x6.val = 0 ∧ e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((e2.x4.val = 255 ∧ e2.x5.val = 255 ∧ e2.x6.val = 255 ∧ e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_op1 : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_op2 : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_REMUW_from_trust state remuw_input r1 r2 rd exec_row e0 e1 e2
    m r_main v r_a h_main_active h_main_op_remuw h_match_secondary
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_row_constraints h_sext_choice h_op1 h_op2 h_op2_ne

/-! ### Memory load dispatchers (LD, LBU, LHU, LWU, LB, LH, LW)

LD on `Valid_Main + Valid_Mem`. LBU/LHU/LWU on
`Valid_Main + Valid_Mem + Valid_MemAlignByte + Valid_MemAlignReadByte
+ Valid_MemAlign` (plus the `SubdoublewordLoadLowBytePinning`
bridge). LB/LH/LW on `Valid_Main + Valid_Mem + Valid_BinaryExtension`.

All seven share the `e0/e1/e2` memory-bus row shape with
`e1.as.val = 2` (memory read). LD lands a plain `execute_instruction`;
LBU/LHU/LWU likewise; LB/LH/LW use the `do; Sail.writeReg` form. -/

/-- **Dispatcher for LD.** -/
lemma dispatch_LD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_ld : main.op r_main = OP_COPYB)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.ld_state_assumptions ld_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADD_pure ld_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LD_from_trust state ld_input mstatus pmaRegion misa mseccfg
    main mem r_main exec_row e0 e1 e2
    h_main_active h_main_op_ld risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for LBU.** -/
lemma dispatch_LBU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL)
    (h_low :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_lbu : main.op r_main = OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lbu_state_assumptions lbu_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADBU_pure lbu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LBU_from_trust state lbu_input mstatus pmaRegion misa mseccfg
    main mem r_main mab marb ma h_low exec_row e0 e1 e2
    h_main_active h_main_op_lbu h_width
    risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for LHU.** -/
lemma dispatch_LHU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL)
    (h_low :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_lhu : main.op r_main = OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lhu_state_assumptions lhu_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADHU_pure lhu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LHU_from_trust state lhu_input mstatus pmaRegion misa mseccfg
    main mem r_main mab marb ma h_low exec_row e0 e1 e2
    h_main_active h_main_op_lhu h_width
    risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for LWU.** -/
lemma dispatch_LWU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL)
    (h_low :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_lwu : main.op r_main = OP_COPYB)
    (h_width : main.ind_width r_main = (4 : FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lwu_state_assumptions lwu_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADWU_pure lwu_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LWU_from_trust state lwu_input mstatus pmaRegion misa mseccfg
    main mem r_main mab marb ma h_low exec_row e0 e1 e2
    h_main_active h_main_op_lwu h_width
    risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for LB.** -/
lemma dispatch_LB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lb_state_assumptions lb_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADB_pure lb_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LB_from_trust state lb_input mstatus pmaRegion misa mseccfg
    main mem r_main v exec_row e0 e1 e2
    h_main_active h_main_op risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for LH.** -/
lemma dispatch_LH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lh_state_assumptions lh_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADH_pure lh_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm,
        regidx.Regidx lh_input.r1,
        regidx.Regidx lh_input.rd,
        false,
        2
      ))) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LH_from_trust state lh_input mstatus pmaRegion misa mseccfg
    main mem r_main v exec_row e0 e1 e2
    h_main_active h_main_op risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for LW.** -/
lemma dispatch_LW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 1)
    (h_main_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lw_state_assumptions lw_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADW_pure lw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_LW_from_trust state lw_input mstatus pmaRegion misa mseccfg
    main mem r_main v exec_row e0 e1 e2
    h_main_active h_main_op risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-! ### Memory store dispatchers (SB, SH, SW, SD)

All four are Main-only stores (`Valid_Main`). They differ in
`ind_width` (1/2/4/8 for SB/SH/SW/SD respectively) but share the
same memory-bus row shape (`e2.as.val = 2` indicates memory write). -/

/-- **Dispatcher for SB.** -/
lemma dispatch_SB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 1)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sb_state_assumptions sb_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREB_pure sb_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sb_input.imm,
      regidx.Regidx sb_input.r2,
      regidx.Regidx sb_input.r1,
      1
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SB_from_trust state sb_input mstatus pmaRegion misa mseccfg
    main r_main exec_row e0 e1 e2
    h_main_active h_main_op h_main_ind_width
    risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for SH.** -/
lemma dispatch_SH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 2)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sh_state_assumptions sh_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREH_pure sh_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sh_input.imm,
      regidx.Regidx sh_input.r2,
      regidx.Regidx sh_input.r1,
      2
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SH_from_trust state sh_input mstatus pmaRegion misa mseccfg
    main r_main exec_row e0 e1 e2
    h_main_active h_main_op h_main_ind_width
    risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for SW.** -/
lemma dispatch_SW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (h_main_ind_width : main.ind_width r_main = 4)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sw_state_assumptions sw_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STOREW_pure sw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sw_input.imm,
      regidx.Regidx sw_input.r2,
      regidx.Regidx sw_input.r1,
      4
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SW_from_trust state sw_input mstatus pmaRegion misa mseccfg
    main r_main exec_row e0 e1 e2
    h_main_active h_main_op h_main_ind_width
    risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

/-- **Dispatcher for SD.** -/
lemma dispatch_SD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sd_state_assumptions sd_input state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STORED_pure sd_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 :=
  equiv_SD_from_trust state sd_input mstatus pmaRegion misa mseccfg
    main r_main exec_row e0 e1 e2
    h_main_active h_main_op risc_v_assumptions h_opcode_assumptions
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as

end ZiskFv.Equivalence.Compliance
