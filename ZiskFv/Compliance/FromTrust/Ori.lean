import Mathlib

import ZiskFv.Equivalence.Ori
import ZiskFv.Equivalence.Promises.IType
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Tactics.ALUITypeArchetype

/-!
# `equiv_ORI` Compliance wrapper — Binary ITYPE shape

Mass-author clone of `FromTrust/Andi.lean` with `AND → OR`. Consumes
`binary_b_op_or_sext_eq_OP_OR` (class #6, parallel to `_OP_AND`).
Trust class unchanged.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_ORI_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_ori : m.op r_main = OP_OR)
    (h_ori_subset : itype_imm_subset_holds_main m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (promises : ZiskFv.Equivalence.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm exec_row e0 e1 e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- OP_OR = 15 = 0x0f.
  have h_op_disj :
      m.op r_main = 0x02 ∨ m.op r_main = 0x03 ∨ m.op r_main = 0x04
    ∨ m.op r_main = 0x05 ∨ m.op r_main = 0x06 ∨ m.op r_main = 0x07
    ∨ m.op r_main = 0x08 ∨ m.op r_main = 0x09 ∨ m.op r_main = 0x0a
    ∨ m.op r_main = 0x0b ∨ m.op r_main = 0x0c ∨ m.op r_main = 0x0d
    ∨ m.op r_main = 0x0e ∨ m.op r_main = 0x0f ∨ m.op r_main = 0x10
    ∨ m.op r_main = 0x12 ∨ m.op r_main = 0x13 ∨ m.op r_main = 0x14
    ∨ m.op r_main = 0x15 ∨ m.op r_main = 0x16 ∨ m.op r_main = 0x17
    ∨ m.op r_main = 0x18 ∨ m.op r_main = 0x19 ∨ m.op r_main = 0x1a
    ∨ m.op r_main = 0x1b ∨ m.op r_main = 0x1c ∨ m.op r_main = 0x1d
    ∨ m.op r_main = 0x50 ∨ m.op r_main = 0x51 := by
    have h15 : m.op r_main = 15 := by rw [h_main_op_ori]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary = 15 := by
    have h_op_match : m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary := by
      simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
      exact h_match.2.1
    rw [h_main_op_ori] at h_op_match
    simp only [OP_OR] at h_op_match
    exact h_op_match.symm
  have h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    binary_b_op_or_sext_eq_OP_OR v r_binary h_emit_op
  exact ZiskFv.Equivalence.Ori.equiv_ORI
    state ori_input r1 rd imm m v r_main r_binary exec_row e0 e1 e2
    promises
    h_main_active h_main_op_ori h_match h_bop_or_sext h_lane_rd h_ori_subset

end ZiskFv.Compliance
