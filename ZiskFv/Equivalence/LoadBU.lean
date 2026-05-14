import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Circuit.LoadBU
import ZiskFv.Circuit.LoadDerivation
import ZiskFv.Circuit.MemModel
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Airs.BusEmission
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Sail.lbu
import ZiskFv.Sail.BusEffect

/-!
End-to-end theorem for RV64 LBU (load byte, unsigned / zero-extended).
-/

namespace ZiskFv.Equivalence.LoadBU

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.LoadD
open ZiskFv.Circuit.LoadBU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

lemma equiv_LBU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lbu_state_assumptions lbu_input state) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state
      = let output := PureSpec.execute_LOADBU_pure lbu_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADBU_pure_equiv
    lbu_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** -/
theorem equiv_LBU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
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
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1)
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    -- MemAlign* providers for the sub-doubleword load (Phase F+ refactor).
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL)
    (h_low :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma)
    -- Circuit constraint witnesses (CIRCUIT-CONSTRAINT class).
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = (1 : FGL))
    (h_width : main.ind_width r_main = (1 : FGL)) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Discharge the Mem-shape promise hypotheses via the bridge entry point.
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match,
          h_rd_zero_iff, h_rd_idx, h_copy0, h_copy1⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.lbu_discharge_full
      main r_main e1 e2 lbu_input.r1_val lbu_input.imm lbu_input.rd
      h_ext h_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  rw [equiv_LBU_sail state lbu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  have h_mem :=
    ZiskFv.Circuit.MemModel.mem_load_correct_1byte
      main mem r_main e1 state h_main_emit_b
  obtain ⟨_h_pc, _h_r1_read,
          h_d0,
          _h_bound⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  have hd0 : (e1.x0 : BitVec 8) = lbu_input.data0 := by
    rw [h_d0] at h_mem; exact (Option.some.inj h_mem).symm
  -- Memory-bus entry byte ranges discharged via the byte-range bus
  -- protocol axiom (`memory_bus_entry_byte_range_perm_sound`).
  have h_e1_range : memory_entry_bytes_in_range e1 :=
    memory_bus_entry_byte_range_perm_sound e1
  have h_e2_range : memory_entry_bytes_in_range e2 :=
    memory_bus_entry_byte_range_perm_sound e2
  have h_lbu_packed :=
    ZiskFv.Circuit.LoadDerivation.load_lbu_c_packed
      main r_main mab marb ma e1 e2 h_copy0 h_copy1 h_ext h_op h_width
      h_main_emit_b h_main_emit_c h_e1_range h_e2_range h_low
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = (BitVec.setWidth 32 lbu_input.data0).setWidth 64 := by
    rw [h_lbu_packed, hd0]
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_loadu_1byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        ((BitVec.setWidth 32 lbu_input.data0).setWidth 64)
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  simp only [PureSpec.execute_LOADBU_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : lbu_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne]
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : lbu_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := lbu_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : lbu_input.rd.toNat ≠ 0 := by
      intro h; apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq; simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨lbu_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext; exact h_rd_idx.symm
    rw [h_idx_eq]

end ZiskFv.Equivalence.LoadBU
