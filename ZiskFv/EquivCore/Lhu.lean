import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.LoadHU
import ZiskFv.ZiskCircuit.LoadDerivation
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.EquivCore.Bridge.Mem
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.SailSpec.lhu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 LHU (load halfword, unsigned / zero-extended).
Uses structural bus hypotheses + `mem_load_correct_2byte`.
LHU's pure-spec uses `BitVec.setWidth 32` (zero-extend to 32 bits) on
the 16-bit halfword.
-/

namespace ZiskFv.EquivCore.Lhu

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.ZiskCircuit.LoadHU


lemma equiv_LHU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lhu_state_assumptions lhu_input state) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state
      = let output := PureSpec.execute_LOADHU_pure lhu_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADHU_pure_equiv
    lhu_input risc_v_assumptions h_opcode_assumptions

/-- LHU equivalence from already-discharged Main/provider memory facts.

This proof core lets the Main-load and Mem-provider path be supplied either
by the legacy axiom-backed bridge or by the Clean memory-bus bridge. The
MemAlign zero-padding path is still the existing `MemAlignWitness`-based
derivation. -/
lemma equiv_LHU_of_discharged
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (h_main_emit_b :
      main.b_0 r_main = memory_entry_lo bus.e1
      ∧ main.b_1 r_main = memory_entry_hi bus.e1
      ∧ bus.e1.as = 2
      ∧ bus.e1.multiplicity = -1)
    (h_main_emit_c :
      main.c_0 r_main = memory_entry_lo bus.e2
      ∧ main.c_1 r_main = memory_entry_hi bus.e2)
    (h_ptr_match :
      bus.e1.ptr.toNat = lhu_input.r1_val.toNat
        + (BitVec.signExtend 64 lhu_input.imm).toNat)
    (h_rd_zero_iff :
      Transpiler.wrap_to_regidx bus.e2.ptr = 0 ↔ lhu_input.rd = 0)
    (h_rd_idx :
      lhu_input.rd.toNat = (Transpiler.wrap_to_regidx bus.e2.ptr).val)
    (h_copy0 : ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main)
    (h_copy1 : ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main)
    (h_mem :
      state.mem[bus.e1.ptr.toNat]? = .some (byteAt bus.e1 0)
      ∧ state.mem[bus.e1.ptr.toNat + 1]? = .some (byteAt bus.e1 1)) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_ext, h_op⟩ := pins
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨mab, marb, ma, mab_core, marb_core, mab_lookup, marb_lookup, h_provider⟩ := align
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          _h_mem_read⟩ := promises
  rw [equiv_LHU_sail state lhu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  obtain ⟨he0, he1⟩ := h_mem
  have hd0 : ((byteAt e1 0) : BitVec 8) = lhu_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : ((byteAt e1 1) : BitVec 8) = lhu_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have h_lhu_packed :=
    ZiskFv.ZiskCircuit.LoadDerivation.load_lhu_c_packed
      main r_main mab marb ma e1 e2 h_copy0 h_copy1 h_ext h_op h_width
      h_main_emit_b h_main_emit_c mab_core marb_core mab_lookup marb_lookup h_provider
  have h_rd_val_derived :
      U64.toBV #v[byteAt e2 0, byteAt e2 1, byteAt e2 2, byteAt e2 3,
                  byteAt e2 4, byteAt e2 5, byteAt e2 6, byteAt e2 7]
        = (BitVec.setWidth 32
            (lhu_input.data1 ++ lhu_input.data0)).setWidth 64 := by
    rw [h_lhu_packed, hd0, hd1]
  -- The narrow loadu_2byte_rrrw lemma takes rd_val as `BitVec 64`,
  -- so we use the setWidth-64'd LHU value as our rd_val.
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_loadu_2byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        ((BitVec.setWidth 32
            (lhu_input.data1 ++ lhu_input.data0)).setWidth 64)
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  -- Discharge the rd-match branch. LHU's pure spec writes `setWidth 32 ...`
  -- (a 32-bit BitVec); the do-block's `write_xreg` expects a 64-bit value.
  -- The implicit zero-extension to 64 bits is what `setWidth 64` produces.
  simp only [PureSpec.execute_LOADHU_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : lhu_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne]
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : lhu_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := lhu_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : lhu_input.rd.toNat ≠ 0 := by
      intro h; apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq; simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨lhu_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext; exact h_rd_idx.symm
    rw [h_idx_eq]

/-- Clean-backed LHU equivalence for the Main/Mem load path.

This removes `main_load_emission_bundle` and
`lookup_consumer_matches_provider_load` from the Main/Mem portion of LHU. The
existing MemAlign witness still supplies the zero-padding/packing derivation,
so the MemAlign T4 targets remain to be retired separately. -/
lemma equiv_LHU_clean_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
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
        lhu_input.r1_val.toNat + (BitVec.signExtend 64 lhu_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx mainRow.rom.addr2 = 0 ↔ lhu_input.rd = 0)
    (h_addr2_idx :
      lhu_input.rd.toNat = (Transpiler.wrap_to_regidx mainRow.rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_legacy_addr : mem.addr r_mem = bus.e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_bundle, h_mem8⟩ :=
    ZiskFv.EquivCore.Bridge.MemClean.ld_discharge_full_clean_provider
      main mem r_main r_mem mainRow memRow bus.e1 bus.e2 state
      lhu_input.r1_val lhu_input.imm lhu_input.rd
      h_main_row h_mem_row h_main_spec h_store_pc
      h_main_b_match h_main_c_match h_mem_match
      h_addr1 h_addr2_zero_iff h_addr2_idx
      h_mem_sel h_mem_legacy_addr h_mem_wr
      (ZiskFv.EquivCore.Promises.memoryTraceAgreement_of_loadByteAgreement
        state bus.e1 promises.mem_read)
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match, h_rd_zero_iff,
          h_rd_idx, h_copy0, h_copy1⟩ := h_bundle
  have h_mem :
      state.mem[bus.e1.ptr.toNat]? = .some (byteAt bus.e1 0)
      ∧ state.mem[bus.e1.ptr.toNat + 1]? = .some (byteAt bus.e1 1) :=
    ⟨h_mem8.1, h_mem8.2.1⟩
  exact equiv_LHU_of_discharged state lhu_input regs bus promises main r_main
    align pins h_width h_main_emit_b h_main_emit_c h_ptr_match h_rd_zero_iff
    h_rd_idx h_copy0 h_copy1 h_mem

/-- Clean-backed LHU equivalence from the bundled structural load witness. -/
lemma equiv_LHU_clean_provider_witness
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lhu_input : PureSpec.LhuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lhu_state_assumptions lhu_input state)
        (PureSpec.execute_LOADHU_pure lhu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness main r_main bus.e1)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (2 : FGL))
    (w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
      main mem r_main bus lhu_input.r1_val lhu_input.imm lhu_input.rd) :
    execute_instruction (instruction.LOAD (
      lhu_input.imm,
      regidx.Regidx lhu_input.r1,
      regidx.Regidx lhu_input.rd,
      true,
      2
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 :=
  equiv_LHU_clean_provider
    state lhu_input regs bus promises main mem r_main w.r_mem align pins h_width
    w.mainRow w.memRow w.main_row w.mem_row w.main_spec w.store_pc
    w.main_b_match w.main_c_match w.mem_match
    w.addr1 w.addr2_zero_iff w.addr2_idx
    w.mem_sel w.mem_legacy_addr w.mem_wr

end ZiskFv.EquivCore.Lhu
