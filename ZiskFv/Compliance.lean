import Mathlib

import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Main.OpcodeClassification
import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Compliance.FromTrust.Lui
import ZiskFv.Compliance.FromTrust.Auipc
import ZiskFv.Compliance.FromTrust.Jal
import ZiskFv.Compliance.FromTrust.Jalr
import ZiskFv.Compliance.FromTrust.Fence
import ZiskFv.Compliance.FromTrust.Beq
import ZiskFv.Compliance.FromTrust.Bne
import ZiskFv.Compliance.FromTrust.Blt
import ZiskFv.Compliance.FromTrust.Bge
import ZiskFv.Compliance.FromTrust.Bltu
import ZiskFv.Compliance.FromTrust.Bgeu
import ZiskFv.Compliance.FromTrust.Add
import ZiskFv.Compliance.FromTrust.Addi
import ZiskFv.Compliance.FromTrust.Addw
import ZiskFv.Compliance.FromTrust.Subw
import ZiskFv.Compliance.FromTrust.Addiw
import ZiskFv.Compliance.FromTrust.Sub
import ZiskFv.Compliance.FromTrust.And
import ZiskFv.Compliance.FromTrust.Andi
import ZiskFv.Compliance.FromTrust.Or
import ZiskFv.Compliance.FromTrust.Ori
import ZiskFv.Compliance.FromTrust.Xor
import ZiskFv.Compliance.FromTrust.Xori
import ZiskFv.Compliance.FromTrust.Slt
import ZiskFv.Compliance.FromTrust.Sltu
import ZiskFv.Compliance.FromTrust.Slti
import ZiskFv.Compliance.FromTrust.Sltiu
import ZiskFv.Compliance.FromTrust.Sll
import ZiskFv.Compliance.FromTrust.Srl
import ZiskFv.Compliance.FromTrust.Sra
import ZiskFv.Compliance.FromTrust.Slli
import ZiskFv.Compliance.FromTrust.Srli
import ZiskFv.Compliance.FromTrust.Srai
import ZiskFv.Compliance.FromTrust.Shift
import ZiskFv.Compliance.FromTrust.ShiftLI
import ZiskFv.Compliance.FromTrust.ShiftR
import ZiskFv.Compliance.FromTrust.ShiftRLI
import ZiskFv.Compliance.FromTrust.ShiftRA
import ZiskFv.Compliance.FromTrust.ShiftRAI
import ZiskFv.Compliance.FromTrust.Mul
import ZiskFv.Compliance.FromTrust.MulH
import ZiskFv.Compliance.FromTrust.MulHU
import ZiskFv.Compliance.FromTrust.MulHSU
import ZiskFv.Compliance.FromTrust.MulW
import ZiskFv.Compliance.FromTrust.Div
import ZiskFv.Compliance.FromTrust.Divu
import ZiskFv.Compliance.FromTrust.Divw
import ZiskFv.Compliance.FromTrust.Divuw
import ZiskFv.Compliance.FromTrust.Rem
import ZiskFv.Compliance.FromTrust.Remu
import ZiskFv.Compliance.FromTrust.Remw
import ZiskFv.Compliance.FromTrust.Remuw
import ZiskFv.Compliance.FromTrust.Ld
import ZiskFv.Compliance.FromTrust.Lbu
import ZiskFv.Compliance.FromTrust.Lhu
import ZiskFv.Compliance.FromTrust.Lwu
import ZiskFv.Compliance.FromTrust.Lb
import ZiskFv.Compliance.FromTrust.Lh
import ZiskFv.Compliance.FromTrust.Lw
import ZiskFv.Compliance.FromTrust.Sb
import ZiskFv.Compliance.FromTrust.Sh
import ZiskFv.Compliance.FromTrust.Sw
import ZiskFv.Compliance.FromTrust.Sd

/-!
# Compliance.lean — Global compliance theorem for RV64IM

This file lands `zisk_riscv_compliant_program_bus`, the global theorem
covering all 63 RV64IM opcodes. Each `OpEnvelope` arm routes to the
corresponding `equiv_<OP>_from_trust` wrapper under
`Compliance/FromTrust/`.

## Opcode bucketing by AIR shape

| Shape                  | Opcodes                                                |
|------------------------|--------------------------------------------------------|
| ControlFlow non-branch | LUI, AUIPC, JAL, JALR, FENCE                           |
| ControlFlow branch     | BEQ, BNE, BLT, BGE, BLTU, BGEU                         |
| BinaryAdd              | ADD, ADDI                                              |
| BinaryAddW             | ADDW, SUBW, ADDIW                                      |
| Binary                 | SUB, AND, OR, XOR, SLT, SLTU, SLTI, SLTIU,             |
|                        | ANDI, ORI, XORI, SLLI, SRLI, SRAI                      |
| BinaryExtension Shift  | SLL, SRL, SRA, SLLW, SRLW, SRAW, SLLIW, SRLIW, SRAIW   |
| ArithMul               | MUL, MULH, MULHSU, MULHU, MULW                         |
| ArithDiv               | DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW, REMUW         |
| Mem Load               | LD, LBU, LHU, LWU, LB, LH, LW                          |
| Mem Store              | SB, SH, SW, SD                                         |

## Why a sum type for `OpEnvelope`

The 63 wrapper signatures do not unify: they take different
`PureSpec.<OP>Input` records, different provider-AIR validators
(LUI: none; ADD: BinaryAdd; LBU/LHU/LWU: Mem + MemAlignByte +
MemAlignReadByte + MemAlign; etc.), and different bus shapes
(branches end with `bus_effect exec_row [] state`; UType/JAL/JALR
with `[e_rd]`; most arithmetic/mem with `[e0, e1, e2]`). Their
LHS conclusion forms also differ: `execute_instruction (instruction
…) state` vs. `(do; writeReg Register.nextPC; execute …) state`
whenever a Sail wrapper unfolds to a `writeReg` prefix.

A sum type is the honest encoding; an existential over a unified
record would be vacuous because most fields would be `True` / junk
values per arm.

## Trust footprint

Zero new axioms in this file. The trust footprint is exactly the
union of the 63 `equiv_<OP>_from_trust` wrappers' closures against
the project's trust ledger.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.Binary
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.Mem
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv
open ZiskFv.PackedBitVec.SignedChunkLift
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Compliance

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Decode side — `Option mainOpKind` -/

/-- The 35-way Zisk op-selector classifier, lifted to an enum.

    This is **not** a full Sail `instruction` decoder — operand fields
    (`imm`, `rd`, `rs1`, `rs2`) and the register-vs-immediate
    disambiguator are not exposed as named columns on `Valid_Main`, so
    decoding to a Sail `instruction` requires operand witnesses
    supplied per-wrapper. This enum identifies which family of per-op
    equivalence theorem applies to the current Main row. -/
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

/-- **Decode the op-kind from a Main row.**

    Returns `none` iff `m.op r_main` is not one of the 35 in-scope
    Zisk OPs. The bridge from kind to a full Sail `instruction`
    happens at dispatch time, where the caller supplies operand
    witnesses (see `OpEnvelope` below).

    This is a `Prop`-valued helper : it returns `some k` iff
    `m.op r_main = k.toFGL`. The companion lemma
    `decode_main_row_correct` shows that under the RV64IM scope
    assumption decoding always succeeds. -/
noncomputable def decode_main_row (m : Valid_Main C FGL FGL) (r : ℕ) :
    Option mainOpKind :=
  open Classical in
  if h : ∃ k : mainOpKind, m.op r = k.toFGL then
    some h.choose
  else
    none

/-- `decode_main_row` succeeds for every RV64IM-in-scope row, and the
    decoded kind's `toFGL` matches `m.op r`.

    Direct from `main_op_in_RV64IM_scope`. -/
theorem decode_main_row_correct
    (m : Valid_Main C FGL FGL) (r : ℕ)
    (h_scope : main_op_in_RV64IM_scope m r) :
    ∃ k : mainOpKind, decode_main_row m r = some k ∧ m.op r = k.toFGL := by
  -- Enumerate the 35-way disjunction and produce the matching kind.
  have h_exists : ∃ k : mainOpKind, m.op r = k.toFGL := by
    rcases h_scope with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                       h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
                       h | h | h | h | h
    · exact ⟨.FLAG, h⟩
    · exact ⟨.COPYB, h⟩
    · exact ⟨.LTU, h⟩
    · exact ⟨.LT, h⟩
    · exact ⟨.EQ, h⟩
    · exact ⟨.ADD, h⟩
    · exact ⟨.SUB, h⟩
    · exact ⟨.AND, h⟩
    · exact ⟨.OR, h⟩
    · exact ⟨.XOR, h⟩
    · exact ⟨.ADD_W, h⟩
    · exact ⟨.SUB_W, h⟩
    · exact ⟨.SLL, h⟩
    · exact ⟨.SRL, h⟩
    · exact ⟨.SRA, h⟩
    · exact ⟨.SLL_W, h⟩
    · exact ⟨.SRL_W, h⟩
    · exact ⟨.SRA_W, h⟩
    · exact ⟨.SIGNEXTEND_B, h⟩
    · exact ⟨.SIGNEXTEND_H, h⟩
    · exact ⟨.SIGNEXTEND_W, h⟩
    · exact ⟨.MULU, h⟩
    · exact ⟨.MULUH, h⟩
    · exact ⟨.MULSUH, h⟩
    · exact ⟨.MUL, h⟩
    · exact ⟨.MULH, h⟩
    · exact ⟨.MUL_W, h⟩
    · exact ⟨.DIVU, h⟩
    · exact ⟨.REMU, h⟩
    · exact ⟨.DIV, h⟩
    · exact ⟨.REM, h⟩
    · exact ⟨.DIVU_W, h⟩
    · exact ⟨.REMU_W, h⟩
    · exact ⟨.DIV_W, h⟩
    · exact ⟨.REM_W, h⟩
  refine ⟨h_exists.choose, ?_, h_exists.choose_spec⟩
  unfold decode_main_row
  exact dif_pos h_exists

/-! ## The `OpEnvelope` sum type

Bundles, per Zisk op-kind, the inputs the corresponding
`equiv_<OP>_from_trust` wrapper requires beyond `(state, m, r_main)`.
Each arm's signature is verbatim from its wrapper.
-/

set_option maxHeartbeats 1000000 in
/-- Per-op input bundle.

    Each constructor's parameter list is exactly the corresponding
    `equiv_<OP>_from_trust` wrapper's parameter list, minus the shared
    `(state, m, r_main)`. -/
inductive OpEnvelope
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) where
  -- ============================ BEQ (branch, no mem) ====================
  | beq
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BNE (branch, no mem) ====================
  | bne
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BLT (branch, no mem) ====================
  | blt
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BGE (branch, no mem) ====================
  | bge
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BLTU (branch, no mem) ===================
  | bltu
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ BGEU (branch, no mem) ===================
  | bgeu
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.Equivalence.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) : OpEnvelope state m r_main
  -- ============================ FENCE (no mem) ==========================
  | fence
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (promises : ZiskFv.Equivalence.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) : OpEnvelope state m r_main
  -- ============================ LUI (1 mem entry) =======================
  | lui
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_lui_subset : lui_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) : OpEnvelope state m r_main
  -- ============================ AUIPC (1 mem entry) =====================
  | auipc
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) : OpEnvelope state m r_main
  -- ============================ JAL (1 mem entry) =======================
  | jal
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_FLAG)
    (h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) : OpEnvelope state m r_main
  -- ============================ JALR (1 mem entry, do-block) ============
  | jalr
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_jalr_subset :
      ZiskFv.Tactics.JumpArchetype.jalr_subset_holds m r_main next_pc)
    (promises : ZiskFv.Equivalence.Promises.JumpPromises
        state jalr_input.PC jalr_input.rd misa_val
        (PureSpec.execute_JALR_pure jalr_input).success
        (PureSpec.execute_JALR_pure jalr_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) : OpEnvelope state m r_main
  -- ============================ ADD (3 mem entries, BinaryAdd) ==========
  | add
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (badd : ZiskFv.Compliance.BinaryAddWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDI (do-block LHS, BinaryAdd) ==========
  | addi
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
    (badd : ZiskFv.Compliance.BinaryAddWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_main_subset : add_subset_holds m r_main)
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDW (Binary, do-block) =================
  | addw
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SUBW (Binary, do-block) =================
  | subw
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ADDIW (Binary, do-block, I-type) ========
  | addiw
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_addiw_subset : itype_imm_subset_holds_main m r_main addiw_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SUB (Binary, R-type) ====================
  | sub
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SUB)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ AND (Binary, R-type) ====================
  | and
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ OR (Binary, R-type) =====================
  | or
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ XOR (Binary, R-type) ====================
  | xor
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
        (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLT (Binary, R-type) ====================
  | slt
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state slt_input.r1_val slt_input.r2_val slt_input.rd slt_input.PC
        (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLTU (Binary, R-type) ===================
  | sltu
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state sltu_input.r1_val sltu_input.r2_val sltu_input.rd sltu_input.PC
        (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ANDI (Binary, I-type) ===================
  | andi
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_AND)
    (h_andi_subset : itype_imm_subset_holds_main m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ ORI (Binary, I-type) ====================
  | ori
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ XORI (Binary, I-type) ===================
  | xori
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLTI (Binary, I-type) ===================
  | slti
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLTIU (Binary, I-type) ==================
  | sltiu
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : Valid_Binary C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LTU)
    (h_sltiu_subset : itype_imm_subset_holds_main m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SLL (BinaryExtension, R-type) ===========
  | sll
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRL ====================================
  | srl
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRA ====================================
  | sra
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SLLI ====================================
  | slli
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRLI ====================================
  | srli
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRAI ====================================
  | srai
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SLLW ====================================
  | sllw
    (sllw_input : PureSpec.SllwInput) (r1 r2 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : sllw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRLW ====================================
  | srlw
    (srlw_input : PureSpec.SrlwInput) (r1 r2 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRAW ====================================
  | sraw
    (sraw_input : PureSpec.SrawInput) (r1 r2 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sraw_input.r2_val state)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : sraw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SLLIW ===================================
  | slliw
    (slliw_input : PureSpec.SlliwInput) (r1 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRLIW ===================================
  | srliw
    (srliw_input : PureSpec.SrliwInput) (r1 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SRAIW ===================================
  | sraiw
    (sraiw_input : PureSpec.SraiwInput) (r1 rd : regidx)
    (v : Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main
  -- ============================ SB (store, Main-only) ===================
  | sb
    (sb_input : PureSpec.SbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 1)
    (h_opcode_assumptions : PureSpec.sb_state_assumptions sb_input state)
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sb_state_assumptions sb_input state)
        (PureSpec.execute_STOREB_pure sb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SH (store, Main-only) ===================
  | sh
    (sh_input : PureSpec.ShInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 2)
    (h_opcode_assumptions : PureSpec.sh_state_assumptions sh_input state)
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sh_state_assumptions sh_input state)
        (PureSpec.execute_STOREH_pure sh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SW (store, Main-only) ===================
  | sw
    (sw_input : PureSpec.SwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_main_ind_width : m.ind_width r_main = 4)
    (h_opcode_assumptions : PureSpec.sw_state_assumptions sw_input state)
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sw_state_assumptions sw_input state)
        (PureSpec.execute_STOREW_pure sw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ SD (store, Main-only) ===================
  | sd
    (sd_input : PureSpec.SdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_opcode_assumptions : PureSpec.sd_state_assumptions sd_input state)
    (promises : ZiskFv.Equivalence.Promises.StorePromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.sd_state_assumptions sd_input state)
        (PureSpec.execute_STORED_pure sd_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LD (load doubleword) ====================
  | ld
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LBU =====================================
  | lbu
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_width : m.ind_width r_main = (1 : FGL))
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LHU =====================================
  | lhu
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_width : m.ind_width r_main = (2 : FGL))
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LWU =====================================
  | lwu
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 0 OP_COPYB)
    (h_width : m.ind_width r_main = (4 : FGL))
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lwu_state_assumptions lwu_input state)
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LB (signed-byte load) ===================
  | lb
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LH ======================================
  | lh
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ LW ======================================
  | lw
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (mem : Valid_Mem C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_W)
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lw_state_assumptions lw_input state)
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) : OpEnvelope state m r_main
  -- ============================ MUL =====================================
  | mul
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    OpEnvelope state m r_main
  -- ============================ MULH ====================================
  | mulh
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    OpEnvelope state m r_main
  -- ============================ MULHU ===================================
  | mulhu
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    OpEnvelope state m r_main
  -- ============================ MULHSU ==================================
  | mulhsu
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULSUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a) :
    OpEnvelope state m r_main
  -- ============================ MULW ====================================
  | mulw
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithMul C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MUL_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (opBus_row_Arith v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    OpEnvelope state m r_main
  -- ============================ DIV =====================================
  | div
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main
  -- ============================ DIVU ====================================
  | divu
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : divu_input.r2_val.toNat ≠ 0) :
    OpEnvelope state m r_main
  -- ============================ DIVW ====================================
  | divw
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIV_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb divw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow :
      ¬ (Sail.BitVec.extractLsb divw_input.r1_val 31 0 = BitVec.ofNat 32 (2^31)
          ∧ Sail.BitVec.extractLsb divw_input.r2_val 31 0 = BitVec.allOnes 32)) :
    OpEnvelope state m r_main
  -- ============================ DIVUW ===================================
  | divuw
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat ≠ 0) :
    OpEnvelope state m r_main
  -- ============================ REM =====================================
  | rem
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REM)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    OpEnvelope state m r_main
  -- ============================ REMU ====================================
  | remu
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : remu_input.r2_val.toNat ≠ 0) :
    OpEnvelope state m r_main
  -- ============================ REMW ====================================
  | remw
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REM_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - (v.np r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32)
    (h_op2_ne : Sail.BitVec.extractLsb remw_input.r2_val 31 0 ≠ 0#32)
    (h_no_overflow_w :
      ¬ (Sail.BitVec.extractLsb remw_input.r1_val 31 0 = (BitVec.ofNat 32 (2^31))
          ∧ Sail.BitVec.extractLsb remw_input.r2_val 31 0 = BitVec.allOnes 32)) :
    OpEnvelope state m r_main
  -- ============================ REMUW ===================================
  | remuw
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.Equivalence.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      ((bus.e2.x4.val = 0 ∧ bus.e2.x5.val = 0 ∧ bus.e2.x6.val = 0 ∧ bus.e2.x7.val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      ((bus.e2.x4.val = 255 ∧ bus.e2.x5.val = 255 ∧ bus.e2.x6.val = 255 ∧ bus.e2.x7.val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0) :
    OpEnvelope state m r_main

namespace OpEnvelope

variable
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {m : Valid_Main C FGL FGL} {r_main : ℕ}

/-- The op-kind this envelope corresponds to. -/
def kind : OpEnvelope state m r_main → mainOpKind
  | .beq .. => .EQ -- branches don't have a single mainOpKind arm;
                          -- the wrapper pins `m.op r_main` directly
                          -- rather than via a kind hypothesis, so we
                          -- map all six branches to `.EQ` (Zisk has no
                          -- separate op for branches; they all live
                          -- under is_external_op = 0 with op = ?
                          -- — see Main's PIL for the exact encoding).
                          -- NOTE: this routing-only choice has no
                          -- soundness implication; the wrapper's
                          -- conclusion does not depend on `kind`.
  | .bne .. => .EQ
  | .blt .. => .EQ
  | .bge .. => .EQ
  | .bltu .. => .EQ
  | .bgeu .. => .EQ
  | .fence .. => .FLAG
  | .lui .. => .COPYB
  | .auipc .. => .FLAG
  | .jal .. => .FLAG
  | .jalr .. => .COPYB
  | .add .. => .ADD
  | .addi .. => .ADD
  | .addw .. => .ADD_W
  | .subw .. => .SUB_W
  | .addiw .. => .ADD_W
  | .sub .. => .SUB
  | .and .. => .AND
  | .or .. => .OR
  | .xor .. => .XOR
  | .slt .. => .LT
  | .sltu .. => .LTU
  | .andi .. => .AND
  | .ori .. => .OR
  | .xori .. => .XOR
  | .slti .. => .LT
  | .sltiu .. => .LTU
  | .sll .. => .SLL
  | .srl .. => .SRL
  | .sra .. => .SRA
  | .slli .. => .SLL
  | .srli .. => .SRL
  | .srai .. => .SRA
  | .sllw .. => .SLL_W
  | .srlw .. => .SRL_W
  | .sraw .. => .SRA_W
  | .slliw .. => .SLL_W
  | .srliw .. => .SRL_W
  | .sraiw .. => .SRA_W
  | .sb .. => .COPYB
  | .sh .. => .COPYB
  | .sw .. => .COPYB
  | .sd .. => .COPYB
  | .ld .. => .COPYB
  | .lbu .. => .COPYB
  | .lhu .. => .COPYB
  | .lwu .. => .COPYB
  | .lb .. => .SIGNEXTEND_B
  | .lh .. => .SIGNEXTEND_H
  | .lw .. => .SIGNEXTEND_W
  | .mul .. => .MUL
  | .mulh .. => .MULH
  | .mulhu .. => .MULUH
  | .mulhsu .. => .MULSUH
  | .mulw .. => .MUL_W
  | .div .. => .DIV
  | .divu .. => .DIVU
  | .divw .. => .DIV_W
  | .divuw .. => .DIVU_W
  | .rem .. => .REM
  | .remu .. => .REMU
  | .remw .. => .REM_W
  | .remuw .. => .REMU_W

/-- The wrapper's conclusion as a `Prop`. -/
def exec_eq : OpEnvelope state m r_main → Prop
  | .beq _ ops .. =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BEQ)) state
        = (bus_effect ops.exec_row [] state).2
  | .bne _ ops .. =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BNE)) state
        = (bus_effect ops.exec_row [] state).2
  | .blt _ ops .. =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLT)) state
        = (bus_effect ops.exec_row [] state).2
  | .bge _ ops .. =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGE)) state
        = (bus_effect ops.exec_row [] state).2
  | .bltu _ ops .. =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BLTU)) state
        = (bus_effect ops.exec_row [] state).2
  | .bgeu _ ops .. =>
      execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BGEU)) state
        = (bus_effect ops.exec_row [] state).2
  | .fence _ fm pred succ rs rd exec_row .. =>
      execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state
        = (bus_effect exec_row [] state).2
  | .lui _ imm rd _ exec_row e_rd .. =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) state
        = (bus_effect exec_row [e_rd] state).2
  | .auipc _ imm rd exec_row e_rd .. =>
      execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
        = (bus_effect exec_row [e_rd] state).2
  | .jal _ imm rd _ _ exec_row e_rd .. =>
      execute_instruction (instruction.JAL (imm, rd)) state
        = (bus_effect exec_row [e_rd] state).2
  | .jalr _ imm rs1 rd _ _ exec_row e_rd .. =>
      (do
          Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
          LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
        = (bus_effect exec_row [e_rd] state).2
  | .add _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .addi _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .addw _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .subw _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .addiw _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ADDIW (imm, r1, rd))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sub _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SUB))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .and _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.AND))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .or _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.OR))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .xor _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.XOR))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .slt _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sltu _ r1 r2 rd _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .andi _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ANDI))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .ori _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .xori _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .slti _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sltiu _ r1 rd imm _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sll _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .srl _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sra _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .slli _ r1 rd shamt _ bus .. =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .srli _ r1 rd shamt _ bus .. =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .srai _ r1 rd shamt _ bus .. =>
      execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sllw _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .srlw _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sraw _ r1 r2 rd _ bus .. =>
      execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .slliw slliw_input r1 rd _ bus .. =>
      execute_instruction
        (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .srliw srliw_input r1 rd _ bus .. =>
      execute_instruction
        (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sraiw sraiw_input r1 rd _ bus .. =>
      execute_instruction
        (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sb sb_input _ bus .. =>
      execute_instruction (instruction.STORE (
        sb_input.imm,
        regidx.Regidx sb_input.r2,
        regidx.Regidx sb_input.r1,
        1
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sh sh_input _ bus .. =>
      execute_instruction (instruction.STORE (
        sh_input.imm,
        regidx.Regidx sh_input.r2,
        regidx.Regidx sh_input.r1,
        2
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sw sw_input _ bus .. =>
      execute_instruction (instruction.STORE (
        sw_input.imm,
        regidx.Regidx sw_input.r2,
        regidx.Regidx sw_input.r1,
        4
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .sd sd_input _ bus .. =>
      execute_instruction (instruction.STORE (
        sd_input.imm,
        regidx.Regidx sd_input.r2,
        regidx.Regidx sd_input.r1,
        8
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .ld ld_input _ _ bus .. =>
      execute_instruction (instruction.LOAD (
        ld_input.imm,
        regidx.Regidx ld_input.r1,
        regidx.Regidx ld_input.rd,
        false,
        8
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .lbu lbu_input _ _ _ bus .. =>
      execute_instruction (instruction.LOAD (
        lbu_input.imm,
        regidx.Regidx lbu_input.r1,
        regidx.Regidx lbu_input.rd,
        true,
        1
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .lhu lhu_input _ _ _ bus .. =>
      execute_instruction (instruction.LOAD (
        lhu_input.imm,
        regidx.Regidx lhu_input.r1,
        regidx.Regidx lhu_input.rd,
        true,
        2
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .lwu lwu_input _ _ _ bus .. =>
      execute_instruction (instruction.LOAD (
        lwu_input.imm,
        regidx.Regidx lwu_input.r1,
        regidx.Regidx lwu_input.rd,
        true,
        4
      )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .lb lb_input _ _ _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lb_input.imm,
          regidx.Regidx lb_input.r1,
          regidx.Regidx lb_input.rd,
          false,
          1
        ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .lh lh_input _ _ _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lh_input.imm,
          regidx.Regidx lh_input.r1,
          regidx.Regidx lh_input.rd,
          false,
          2
        ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .lw lw_input _ _ _ bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          lw_input.imm,
          regidx.Regidx lw_input.r1,
          regidx.Regidx lw_input.rd,
          false,
          4
        ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .mul _ r1 r2 rd srs1 srs2 bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL
            (r2, r1, rd,
             { result_part := VectorHalf.Low
               signed_rs1 := srs1
               signed_rs2 := srs2 }))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .mulh _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL
            (r2, r1, rd,
             { result_part := VectorHalf.High
               signed_rs1 := .Signed
               signed_rs2 := .Signed }))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .mulhu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL
            (r2, r1, rd,
             { result_part := VectorHalf.High
               signed_rs1 := .Unsigned
               signed_rs2 := .Unsigned }))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .mulhsu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MUL
            (r2, r1, rd,
             { result_part := VectorHalf.High
               signed_rs1 := .Signed
               signed_rs2 := .Unsigned }))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .mulw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute
          (instruction.MULW (r2, r1, rd))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .div _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .divu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .divw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, false))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .divuw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIVW (r2, r1, rd, true))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .rem _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, false))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .remu _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .remw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, false))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2
  | .remuw _ r1 r2 rd bus .. =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
        = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2

end OpEnvelope

/-! ## The global theorem

For each constructor of `OpEnvelope`, route to the corresponding
`equiv_<OP>_from_trust` wrapper. The proof is one `match` arm per
op, delegating verbatim. -/

/-- **Global compliance theorem.**

    Given an op-envelope packaging all the inputs and hypotheses the
    corresponding `equiv_<OP>_from_trust` wrapper requires, the
    envelope's declared conclusion (`exec_eq`) holds.

    The conclusion's shape is determined by the envelope's
    constructor; the global theorem is a 63-arm routing match
    delegating to each wrapper.

    Trust footprint: the union of the 63 wrappers' closures against
    the project's trust ledger. This theorem adds zero new trust. -/
theorem zisk_riscv_compliant_program_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (env : OpEnvelope (C := C) state m r_main) :
    env.exec_eq := by
  cases env with
  | beq beq_input ops promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_BEQ_from_trust state beq_input ops promises
  | bne bne_input ops promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_BNE_from_trust state bne_input ops promises
  | blt blt_input ops promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_BLT_from_trust state blt_input ops promises
  | bge bge_input ops promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_BGE_from_trust state bge_input ops promises
  | bltu bltu_input ops promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_BLTU_from_trust state bltu_input ops promises
  | bgeu bgeu_input ops promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_BGEU_from_trust state bgeu_input ops promises
  | fence fence_input fm pred succ rs rd exec_row
          pins promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_FENCE_from_trust state fence_input fm pred succ rs rd m r_main
      exec_row pins promises
  | lui lui_input imm rd next_pc exec_row e_rd
        pins h_lui_subset promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LUI_from_trust state lui_input imm rd m r_main next_pc
      exec_row e_rd pins h_lui_subset promises
  | auipc auipc_input imm rd exec_row e_rd nextPC_val next_pc
          pins h_auipc_subset
          promises h_no_wrap h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_AUIPC_from_trust state auipc_input imm rd exec_row e_rd nextPC_val
      m r_main next_pc pins h_auipc_subset
      promises h_no_wrap h_lo_bound h_pc_offset_lt_2_32
  | jal jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
        pins h_jal_subset
        promises h_input_imm h_not_throws
        h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_JAL_from_trust state jal_input imm rd misa_val m r_main next_pc
      exec_row e_rd nextPC_val pins h_jal_subset
      promises h_input_imm h_not_throws
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | jalr jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val next_pc
         pins h_jalr_subset
         promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
         h_pc_bound h_lo_bound h_pc_offset_lt_2_32 =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_JALR_from_trust state jalr_input imm rs1 rd misa_val mseccfg
      exec_row e_rd nextPC_val m r_main next_pc
      pins h_jalr_subset
      promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
  | add add_input r1 r2 rd badd bus pins h_main_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_ADD_from_trust state add_input r1 r2 rd m badd r_main bus pins
      h_main_subset h_lane_rd promises
  | addi addi_input r1 rd imm badd bus pins h_main_subset h_addi_subset h_lane_rd
         promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_ADDI_from_trust state addi_input r1 rd imm m badd r_main bus pins
      h_main_subset h_addi_subset h_lane_rd
      promises
  | addw addw_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_ADDW_from_trust state addw_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | subw subw_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SUBW_from_trust state subw_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | addiw addiw_input r1 rd imm v bus pins h_addiw_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_ADDIW_from_trust state addiw_input r1 rd imm m v r_main bus pins
      h_addiw_subset h_lane_rd promises
  | sub sub_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SUB_from_trust state sub_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | and and_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_AND_from_trust state and_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | or or_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_OR_from_trust state or_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | xor xor_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_XOR_from_trust state xor_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | slt slt_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLT_from_trust state slt_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | sltu sltu_input r1 r2 rd v bus pins h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLTU_from_trust state sltu_input r1 r2 rd m v r_main bus pins
      h_lane_rd promises
  | andi andi_input r1 rd imm v bus pins h_andi_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_ANDI_from_trust state andi_input r1 rd imm m v r_main bus pins
      h_andi_subset h_lane_rd promises
  | ori ori_input r1 rd imm v bus pins h_ori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_ORI_from_trust state ori_input r1 rd imm m v r_main bus pins
      h_ori_subset h_lane_rd promises
  | xori xori_input r1 rd imm v bus pins h_xori_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_XORI_from_trust state xori_input r1 rd imm m v r_main bus pins
      h_xori_subset h_lane_rd promises
  | slti slti_input r1 rd imm v bus pins h_slti_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLTI_from_trust state slti_input r1 rd imm m v r_main bus pins
      h_slti_subset h_lane_rd promises
  | sltiu sltiu_input r1 rd imm v bus pins h_sltiu_subset h_lane_rd promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLTIU_from_trust state sltiu_input r1 rd imm m v r_main bus pins
      h_sltiu_subset h_lane_rd promises
  | sll sll_input r1 r2 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLL_from_trust state sll_input r1 r2 rd m v r_main bus promises pins h_lane_rd
  | srl srl_input r1 r2 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRL_from_trust state srl_input r1 r2 rd m v r_main bus promises pins h_lane_rd
  | sra sra_input r1 r2 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRA_from_trust state sra_input r1 r2 rd m v r_main bus promises pins h_lane_rd
  | slli slli_input r1 rd shamt v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLLI_from_trust state slli_input r1 rd shamt m v r_main bus promises pins h_lane_rd
  | srli srli_input r1 rd shamt v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRLI_from_trust state srli_input r1 rd shamt m v r_main bus promises pins h_lane_rd
  | srai srai_input r1 rd shamt v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRAI_from_trust state srai_input r1 rd shamt m v r_main bus promises pins h_lane_rd
  | sllw sllw_input r1 r2 rd v bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLLW_from_trust state sllw_input r1 r2 rd m v r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_lane_rd
  | srlw srlw_input r1 r2 rd v bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRLW_from_trust state srlw_input r1 r2 rd m v r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_lane_rd
  | sraw sraw_input r1 r2 rd v bus
         h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
         h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
         h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
         pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRAW_from_trust state sraw_input r1 r2 rd m v r_main bus
      h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
      h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
      pins h_lane_rd
  | slliw slliw_input r1 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SLLIW_from_trust state slliw_input r1 rd m v r_main bus promises pins h_lane_rd
  | srliw srliw_input r1 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRLIW_from_trust state srliw_input r1 rd m v r_main bus promises pins h_lane_rd
  | sraiw sraiw_input r1 rd v bus promises pins h_lane_rd =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SRAIW_from_trust state sraiw_input r1 rd m v r_main bus promises pins h_lane_rd
  | sb sb_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SB_from_trust state sb_input regs
      m r_main bus pins h_main_ind_width h_opcode_assumptions promises
  | sh sh_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SH_from_trust state sh_input regs
      m r_main bus pins h_main_ind_width h_opcode_assumptions promises
  | sw sw_input regs bus pins h_main_ind_width h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SW_from_trust state sw_input regs
      m r_main bus pins h_main_ind_width h_opcode_assumptions promises
  | sd sd_input regs bus pins h_opcode_assumptions promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_SD_from_trust state sd_input regs
      m r_main bus pins h_opcode_assumptions promises
  | ld ld_input regs mem bus pins promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LD_from_trust state ld_input regs
      m mem r_main bus pins promises
  | lbu lbu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LBU_from_trust state lbu_input regs
      m mem r_main align bus pins h_width promises
  | lhu lhu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LHU_from_trust state lhu_input regs
      m mem r_main align bus pins h_width promises
  | lwu lwu_input regs mem align bus pins h_width promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LWU_from_trust state lwu_input regs
      m mem r_main align bus pins h_width promises
  | lb lb_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LB_from_trust state lb_input regs
      m mem r_main v bus pins promises
  | lh lh_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LH_from_trust state lh_input regs
      m mem r_main v bus pins promises
  | lw lw_input regs mem v bus pins promises =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_LW_from_trust state lw_input regs
      m mem r_main v bus pins promises
  | mul mul_input r1 r2 rd srs1 srs2 bus v r_a
        pins h_match_primary
        promises
        bounds h_row_constraints =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_MUL_from_trust state mul_input r1 r2 rd srs1 srs2
      bus m r_main v r_a
      pins h_match_primary
      promises
      bounds h_row_constraints
  | mulh mulh_input r1 r2 rd bus v r_a
         pins h_match_secondary
         promises
         h_row_constraints =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_MULH_from_trust state mulh_input r1 r2 rd
      bus m r_main v r_a
      pins h_match_secondary
      promises
      h_row_constraints
  | mulhu mulhu_input r1 r2 rd bus v r_a
          pins h_match_secondary
          promises
          bounds h_row_constraints =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_MULHU_from_trust state mulhu_input r1 r2 rd
      bus m r_main v r_a
      pins h_match_secondary
      promises
      bounds h_row_constraints
  | mulhsu mulhsu_input r1 r2 rd bus v r_a
           pins h_match_secondary
           promises
           h_row_constraints =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_MULHSU_from_trust state mulhsu_input r1 r2 rd
      bus m r_main v r_a
      pins h_match_secondary
      promises
      h_row_constraints
  | mulw mulw_input r1 r2 rd bus v r_a
         pins h_match_primary
         promises
         h_row_constraints h_sext_choice h_rs1_value h_rs2_value =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_MULW_from_trust state mulw_input r1 r2 rd
      bus m r_main v r_a
      pins h_match_primary
      promises
      h_row_constraints h_sext_choice h_rs1_value h_rs2_value
  | div div_input r1 r2 rd bus v r_a
        pins h_match_primary
        promises
        h_op2_ne h_no_overflow
        h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_DIV_from_trust state div_input r1 r2 rd bus
      m r_main v r_a pins h_match_primary
      promises
      h_op2_ne h_no_overflow
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
  | divu divu_input r1 r2 rd bus v r_a
         pins h_match_primary
         promises
         bounds h_row_constraints h_op2_ne =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_DIVU_from_trust state divu_input r1 r2 rd bus
      m r_main v r_a pins h_match_primary
      promises
      bounds h_row_constraints h_op2_ne
  | divw divw_input r1 r2 rd bus v r_a
         pins h_match_primary
         promises
         h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
         h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_DIVW_from_trust state divw_input r1 r2 rd bus
      m r_main v r_a pins h_match_primary
      promises
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow
  | divuw divuw_input r1 r2 rd bus v r_a
          pins h_match_primary
          promises
          h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_DIVUW_from_trust state divuw_input r1 r2 rd bus
      m r_main v r_a pins h_match_primary
      promises
      h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne
  | rem rem_input r1 r2 rd bus v r_a
        pins h_match_secondary
        promises
        h_op2_ne h_no_overflow
        h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_REM_from_trust state rem_input r1 r2 rd bus
      m r_main v r_a pins h_match_secondary
      promises
      h_op2_ne h_no_overflow
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
  | remu remu_input r1 r2 rd bus v r_a
         pins h_match_secondary
         promises
         bounds h_row_constraints h_op2_ne =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_REMU_from_trust state remu_input r1 r2 rd bus
      m r_main v r_a pins h_match_secondary
      promises
      bounds h_row_constraints h_op2_ne
  | remw remw_input r1 r2 rd bus v r_a
         pins h_match_secondary
         promises
         h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
         h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_REMW_from_trust state remw_input r1 r2 rd bus
      m r_main v r_a pins h_match_secondary
      promises
      h_row_constraints h_na_bool h_nb_bool h_nr_bool h_np_xor
      h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_no_overflow_w
  | remuw remuw_input r1 r2 rd bus v r_a
          pins h_match_secondary
          promises
          h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne =>
    simp only [OpEnvelope.exec_eq]
    exact equiv_REMUW_from_trust state remuw_input r1 r2 rd bus
      m r_main v r_a pins h_match_secondary
      promises
      h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne

end ZiskFv.Compliance
