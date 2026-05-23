import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.LoadByte
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
import ZiskFv.EquivCore.Bridge.Mem
import ZiskFv.SailSpec.lb
import ZiskFv.SailSpec.BusEffect
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 LB (load byte, signed / sign-extended).
Uses structural bus hypotheses + `mem_load_correct_1byte` rather than
a monolithic bus-execute-matches-sail premise.
-/

namespace ZiskFv.EquivCore.Lb

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.LoadByte


lemma equiv_LB_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lb_state_assumptions lb_input state) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state
      = let output := PureSpec.execute_LOADB_pure lb_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADB_pure_equiv
    lb_input risc_v_assumptions h_opcode_assumptions

/-- LB equivalence with BinaryExtension table semantics supplied explicitly. -/
theorem equiv_LB_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    -- BinaryExtension AIR connection witnesses (Op-bus permutation handshake +
    -- per-byte lookup soundness).
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary : ℕ)
    (h_op_binary :
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes)
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
    (h_a0_match : (v.free_in_a_0 r_binary).val = bus.e1.x0.val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_ext, h_op⟩ := pins
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as⟩ := promises
  -- Step 0. Discharge the Mem-shape promise hypotheses via the
  -- Bridge.Mem entry point (consumes `main_sext_load_emission_bundle`
  -- — class #4 trust ledger).
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match,
          h_rd_zero_iff, h_rd_idx⟩ :=
    ZiskFv.EquivCore.Bridge.Mem.lb_discharge_full
      main r_main e1 e2 lb_input.r1_val lb_input.imm lb_input.rd
      h_ext h_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  rw [equiv_LB_sail state lb_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  have h_mem :=
    ZiskFv.ZiskCircuit.MemModel.mem_load_correct_1byte
      main mem r_main e1 state h_main_emit_b
  obtain ⟨_h_pc, _h_r1_read,
          h_d0,
          _h_bound⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  have hd0 : (e1.x0 : BitVec 8) = lb_input.data0 := by
    rw [h_d0] at h_mem; exact (Option.some.inj h_mem).symm
  have h_e1_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e1
  have h_e2_range := ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  have h_lb_packed :=
    ZiskFv.ZiskCircuit.SextLoadBridge.load_byte_c_packed_of_wf
      main r_main v r_binary e1 e2
      h_op_binary h_bytes h_wfs hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_main_emit_c
      h_e2_range.1 h_e2_range.2.1 h_e2_range.2.2.1 h_e2_range.2.2.2.1
      h_e2_range.2.2.2.2.1 h_e2_range.2.2.2.2.2.1
      h_e2_range.2.2.2.2.2.2.1 h_e2_range.2.2.2.2.2.2.2
      h_a0_match h_e1_range.1
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.signExtend 64 lb_input.data0 := by
    rw [h_lb_packed, hd0]
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_load_1byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        (BitVec.signExtend 64 lb_input.data0)
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  simp only [PureSpec.execute_LOADB_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : lb_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne]
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : lb_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := lb_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : lb_input.rd.toNat ≠ 0 := by
      intro h; apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq; simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨lb_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext; exact h_rd_idx.symm
    rw [h_idx_eq]

/-- **Canonical equivalence.** -/
theorem equiv_LB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary : ℕ)
    (h_op_binary :
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B)
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
    (h_a0_match : (v.free_in_a_0 r_binary).val = bus.e1.x0.val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  equiv_LB_of_wf state lb_input regs bus promises main mem r_main pins v r_binary
    h_op_binary h_bytes
    ⟨ ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e0 h_bytes.h0.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e1 h_bytes.h1.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e2 h_bytes.h2.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e3 h_bytes.h3.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e4 h_bytes.h4.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e5 h_bytes.h5.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e6 h_bytes.h6.1
    , ZiskFv.Airs.Tables.BinaryExtensionTable.bin_ext_table_consumer_wf h_bytes.e7 h_bytes.h7.1 ⟩
    hc_lo_sum_lt hc_hi_sum_lt h_match_clo h_match_chi h_a0_match

end ZiskFv.EquivCore.Lb
