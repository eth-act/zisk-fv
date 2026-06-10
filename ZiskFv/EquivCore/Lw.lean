import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.LoadWord
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.ZiskCircuit.SextLoadBridge
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.EquivCore.Bridge.Mem
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.SailSpec.lw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 LW (load word, signed / sign-extended).
Pilot of the `SignExtendLoadArchetype`; consumes
`PureSpec.execute_LOADW_pure_equiv` directly (RV64 LW is signed —
`is_unsigned = false`).

Parallels the LHU / LBU equivalence structure (same trio of theorems).
Uses structural bus hypotheses (shape (d) reduction
`bus_effect_matches_sail_load_4byte_rrrw`) plus a memory-model bridge
(`Circuit.MemModel.mem_load_correct_4byte`) that derives the bus-side
rd-write byte equalities from circuit primitives.
-/

namespace ZiskFv.EquivCore.Lw

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.LoadWord


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LW-shape LOAD reduces to the pure-function block supplied by
    `PureSpec.execute_LOADW_pure`, given the standard register/PC/memory
    assumptions. -/
lemma equiv_LW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lw_state_assumptions lw_input state) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state
      = let output := PureSpec.execute_LOADW_pure lw_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADW_pure_equiv (state := state)
    (mstatus := mstatus) (pmaRegion := pmaRegion) (misa := misa)
    (mseccfg := mseccfg) lw_input risc_v_assumptions h_opcode_assumptions

/-- Clean-backed LW equivalence for the Main/Mem load path.

This removes `main_sext_load_emission_bundle` and
`lookup_consumer_matches_provider_load` from the Main/Mem portion of LW. The
BinaryExtension witnesses still supply the signed-extension packing facts. -/
lemma equiv_LW_clean_provider_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lw_state_assumptions lw_input state)
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary : ℕ)
    (h_op_binary :
      (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W)
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
    (h_a0_match : (v.free_in_a_0 r_binary).val = (byteAt bus.e1 0).val)
    (h_a1_match : (v.free_in_a_1 r_binary).val = (byteAt bus.e1 1).val)
    (h_a2_match : (v.free_in_a_2 r_binary).val = (byteAt bus.e1 2).val)
    (h_a3_match : (v.free_in_a_3 r_binary).val = (byteAt bus.e1 3).val)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (memRow : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      memRow = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage mainRow) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 1))
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage memRow) 1 2))
    (h_addr1 :
      mainRow.rom.addr1.toNat =
        lw_input.r1_val.toNat + (BitVec.signExtend 64 lw_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx mainRow.rom.addr2 = 0 ↔ lw_input.rd = 0)
    (h_addr2_idx :
      lw_input.rd.toNat = (Transpiler.wrap_to_regidx mainRow.rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_mem_read⟩ := promises
  obtain ⟨h_bundle, h_mem8⟩ :=
    ZiskFv.EquivCore.Bridge.MemClean.ld_discharge_full_clean_provider
      main mem r_main r_mem mainRow memRow e1 e2 state
      lw_input.r1_val lw_input.imm lw_input.rd
      h_main_row h_mem_row h_main_spec h_store_pc
      h_main_b_match h_main_c_match h_mem_match
      h_addr1 h_addr2_zero_iff h_addr2_idx
      h_mem_sel h_mem_wr
      (ZiskFv.EquivCore.Promises.memoryTraceAgreement_of_loadByteAgreement
        state e1 h_mem_read)
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match,
          h_rd_zero_iff, h_rd_idx, _h_copy0, _h_copy1⟩ := h_bundle
  rw [equiv_LW_sail state lw_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  have h_mem :
      state.mem[e1.ptr.toNat]? = .some (byteAt e1 0)
      ∧ state.mem[e1.ptr.toNat + 1]? = .some (byteAt e1 1)
      ∧ state.mem[e1.ptr.toNat + 2]? = .some (byteAt e1 2)
      ∧ state.mem[e1.ptr.toNat + 3]? = .some (byteAt e1 3) :=
    ⟨h_mem8.1, h_mem8.2.1, h_mem8.2.2.1, h_mem8.2.2.2.1⟩
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1, h_d2, h_d3,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  obtain ⟨he0, he1, he2, he3⟩ := h_mem
  have hd0 : ((byteAt e1 0) : BitVec 8) = lw_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : ((byteAt e1 1) : BitVec 8) = lw_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have hd2 : ((byteAt e1 2) : BitVec 8) = lw_input.data2 := by
    rw [h_d2] at he2; exact (Option.some.inj he2).symm
  have hd3 : ((byteAt e1 3) : BitVec 8) = lw_input.data3 := by
    rw [h_d3] at he3; exact (Option.some.inj he3).symm
  have h_e1_0 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e1 0
  have h_e1_1 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e1 1
  have h_e1_2 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e1 2
  have h_e1_3 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e1 3
  have h_e2_0 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 0
  have h_e2_1 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 1
  have h_e2_2 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 2
  have h_e2_3 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 3
  have h_e2_4 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 4
  have h_e2_5 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 5
  have h_e2_6 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 6
  have h_e2_7 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 7
  have h_lw_packed :=
    ZiskFv.ZiskCircuit.SextLoadBridge.load_word_c_packed_of_wf
      main r_main v r_binary e1 e2
      h_op_binary h_bytes h_wfs hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_main_emit_c
      h_e2_0 h_e2_1 h_e2_2 h_e2_3
      h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a0_match h_a1_match h_a2_match h_a3_match
      h_e1_0 h_e1_1 h_e1_2 h_e1_3
  have h_rd_val_derived :
      U64.toBV #v[byteAt e2 0, byteAt e2 1, byteAt e2 2, byteAt e2 3,
                  byteAt e2 4, byteAt e2 5, byteAt e2 6, byteAt e2 7]
        = BitVec.signExtend 64
            (lw_input.data3 ++ lw_input.data2
             ++ lw_input.data1 ++ lw_input.data0) := by
    rw [h_lw_packed, hd0, hd1, hd2, hd3]
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_load_4byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        (BitVec.signExtend 64
          (lw_input.data3 ++ lw_input.data2
           ++ lw_input.data1 ++ lw_input.data0))
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  simp only [PureSpec.execute_LOADW_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : lw_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne]
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : lw_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := lw_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : lw_input.rd.toNat ≠ 0 := by
      intro h; apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq; simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨lw_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext; exact h_rd_idx.symm
    rw [h_idx_eq]

-- legacy equiv_LW (bin_ext_table_consumer_wf route) deleted in T4-purge P3.10.

end ZiskFv.EquivCore.Lw
