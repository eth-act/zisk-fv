import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.LoadWU
import ZiskFv.ZiskCircuit.LoadDerivation
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.SailSpec.lwu
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Equivalence.Promises.Load
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 LWU (load word, unsigned / zero-extended).
Sibling of `Equivalence/LoadD.lean`; uses
`bus_effect_matches_sail_loadu_4byte_rrrw` and `mem_load_correct_4byte`.
-/

namespace ZiskFv.Equivalence.LoadWU

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.ZiskCircuit.LoadWU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** Wraps `PureSpec.execute_LOADWU_pure_equiv`. -/
lemma equiv_LWU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lwu_state_assumptions lwu_input state) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state
      = let output := PureSpec.execute_LOADWU_pure lwu_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADWU_pure_equiv
    lwu_input risc_v_assumptions h_opcode_assumptions

/-- **Canonical equivalence.** Uses structural bus hypotheses + a
    memory-model bridge with a zero-extension witness on the high bytes. -/
theorem equiv_LWU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lwu_state_assumptions lwu_input state)
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    -- Memory-bridge premises.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (4 : FGL)) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_ext, h_op⟩ := pins
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨mab, marb, ma, h_low⟩ := align
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as⟩ := promises
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match,
          h_rd_zero_iff, h_rd_idx, h_copy0, h_copy1⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.lwu_discharge_full
      main r_main e1 e2 lwu_input.r1_val lwu_input.imm lwu_input.rd
      h_ext h_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  rw [equiv_LWU_sail state lwu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  have h_mem :=
    ZiskFv.ZiskCircuit.MemModel.mem_load_correct_4byte
      main mem r_main e1 state h_main_emit_b
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1, h_d2, h_d3,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  obtain ⟨he0, he1, he2, he3⟩ := h_mem
  have hd0 : (e1.x0 : BitVec 8) = lwu_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : (e1.x1 : BitVec 8) = lwu_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have hd2 : (e1.x2 : BitVec 8) = lwu_input.data2 := by
    rw [h_d2] at he2; exact (Option.some.inj he2).symm
  have hd3 : (e1.x3 : BitVec 8) = lwu_input.data3 := by
    rw [h_d3] at he3; exact (Option.some.inj he3).symm
  -- Memory-bus entry byte ranges discharged via the byte-range bus
  -- protocol axiom (`memory_bus_entry_byte_range_perm_sound`).
  have h_e1_range : memory_entry_bytes_in_range e1 :=
    memory_bus_entry_byte_range_perm_sound e1
  have h_e2_range : memory_entry_bytes_in_range e2 :=
    memory_bus_entry_byte_range_perm_sound e2
  have h_lwu_packed :=
    ZiskFv.ZiskCircuit.LoadDerivation.load_lwu_c_packed
      main r_main mab marb ma e1 e2 h_copy0 h_copy1 h_ext h_op h_width
      h_main_emit_b h_main_emit_c h_e1_range h_e2_range h_low
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.zeroExtend 64
            (lwu_input.data3 ++ lwu_input.data2
             ++ lwu_input.data1 ++ lwu_input.data0) := by
    rw [h_lwu_packed, hd0, hd1, hd2, hd3]
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_loadu_4byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADWU_pure lwu_input).nextPC
        (BitVec.zeroExtend 64
          (lwu_input.data3 ++ lwu_input.data2
           ++ lwu_input.data1 ++ lwu_input.data0))
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  simp only [PureSpec.execute_LOADWU_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : lwu_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne]
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : lwu_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := lwu_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : lwu_input.rd.toNat ≠ 0 := by
      intro h; apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq; simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨lwu_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext; exact h_rd_idx.symm
    rw [h_idx_eq]

end ZiskFv.Equivalence.LoadWU
