import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.LoadHalf
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.ZiskCircuit.SextLoadBridge
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.SailSpec.lh
import ZiskFv.SailSpec.BusEffect

/-!
End-to-end theorem for RV64 LH (load halfword, signed / sign-extended).
Uses structural bus hypotheses (shape (d-2-signed)) plus a memory-model
bridge (`mem_load_correct_2byte`) instead of a monolithic
bus-execute-matches-sail premise.
-/

namespace ZiskFv.Equivalence.Lh

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.LoadHalf

variable {C : Type → Type → Type} [Circuit FGL FGL C]

lemma equiv_LH_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lh_state_assumptions lh_input state) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm,
        regidx.Regidx lh_input.r1,
        regidx.Regidx lh_input.rd,
        false,
        2
      ))) state
      = let output := PureSpec.execute_LOADH_pure lh_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADH_pure_equiv
    lh_input risc_v_assumptions h_opcode_assumptions

/-- **Canonical equivalence.** -/
theorem equiv_LH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
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
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (h_ext : main.is_external_op r_main = 1)
    (h_op : main.op r_main = ZiskFv.Trusted.OP_SIGNEXTEND_H)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_binary : ℕ)
    (h_op_binary :
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (hc_lo_sum_lt :
      (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
      + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
      + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
      + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt :
      (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
      + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
      + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
      + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : main.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : main.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_a0_match : (v.free_in_a_0 r_binary).val = e1.x0.val)
    (h_a1_match : (v.free_in_a_1 r_binary).val = e1.x1.val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm,
        regidx.Regidx lh_input.r1,
        regidx.Regidx lh_input.rd,
        false,
        2
      ))) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match,
          h_rd_zero_iff, h_rd_idx⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.lh_discharge_full
      main r_main e1 e2 lh_input.r1_val lh_input.imm lh_input.rd
      h_ext h_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  rw [equiv_LH_sail state lh_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  have h_mem :=
    ZiskFv.ZiskCircuit.MemModel.mem_load_correct_2byte
      main mem r_main e1 state h_main_emit_b
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  obtain ⟨he0, he1⟩ := h_mem
  have hd0 : (e1.x0 : BitVec 8) = lh_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : (e1.x1 : BitVec 8) = lh_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have h_e1_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e1
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_lh_packed :=
    ZiskFv.ZiskCircuit.SextLoadBridge.load_half_c_packed
      main r_main v r_binary e1 e2
      h_op_binary h_bytes hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_main_emit_c
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_a0_match h_a1_match h_e1_range.1 h_e1_range.2.1
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.signExtend 64 (lh_input.data1 ++ lh_input.data0) := by
    rw [h_lh_packed, hd0, hd1]
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_load_2byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        (BitVec.signExtend 64 (lh_input.data1 ++ lh_input.data0))
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  simp only [PureSpec.execute_LOADH_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : lh_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne]
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : lh_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := lh_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : lh_input.rd.toNat ≠ 0 := by
      intro h; apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq; simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨lh_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext; exact h_rd_idx.symm
    rw [h_idx_eq]

end ZiskFv.Equivalence.Lh
