import Mathlib

import ZiskFv.Equivalence.Xor
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges

/-!
# `equiv_XOR` Compliance wrapper — Binary shape

Mass-author clone of `FromTrust/Or.lean` with `OR → XOR`. Consumes the
mode-pin axiom `binary_b_op_or_sext_eq_OP_XOR` (class #6).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_XOR_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xor_input : PureSpec.XorInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
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
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- OP_XOR = 16 = 0x10.
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
    have h16 : m.op r_main = 16 := by rw [h_main_op_xor]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary = 16 := by
    have h_op_match : m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary := by
      simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
      exact h_match.2.1
    rw [h_main_op_xor] at h_op_match
    simp only [OP_XOR] at h_op_match
    exact h_op_match.symm
  have h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    binary_b_op_or_sext_eq_OP_XOR v r_binary h_emit_op
  exact ZiskFv.Equivalence.Xor.equiv_XOR
    state xor_input r1 r2 rd m v r_main r_binary exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op_xor h_match h_bop_or_sext h_lane_rd

end ZiskFv.Compliance
