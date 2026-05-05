import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.LoadWU
import ZiskFv.Circuit.MemModel
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.lwu
import ZiskFv.Sail.BusEffect

/-!
End-to-end theorem for RV64 LWU (load word, unsigned / zero-extended).
Phase 2.5 D4c sibling of `Equivalence/LoadD.lean`. `finishing3` S5b
retired the the bus-execute-matches-sail premise parameter from
`equiv_LWU_metaplan` (see `LoadD` for the analogous LD-side
retirement; LWU follows the same shape with
`bus_effect_matches_sail_loadu_4byte_rrrw` and
`mem_load_correct_4byte`).
-/

namespace ZiskFv.Equivalence.LoadWU

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.LoadD
open ZiskFv.Circuit.LoadWU

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LWU theorem.** With the LD-shape load hypotheses
    plus the memory-bus entry's high 4 byte lanes zeroed (the `ind_width
    = 4` bus-side zero-pad), the Main row's packed `c` cell encodes the
    32-bit loaded value (equal to `memory_entry_lo entry`).

    LWU-analogue of `equiv_LD`, narrowed via
    `load_wu_compositional`. -/
theorem equiv_LWU
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (entry : MemoryBusEntry FGL)
    (h_circuit : load_wu_circuit_holds m r_main next_pc entry) :
    main_c_packed m r_main = memory_entry_lo entry :=
  load_wu_compositional m r_main next_pc entry h_circuit

/-- **Sail-level companion.** Wraps `PureSpec.execute_LOADWU_pure_equiv`. -/
theorem equiv_LWU_sail
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

/-- **Metaplan theorem.** `finishing3` S5b: retired
    the bus-execute-matches-sail premise in favour of structural bus
    hypotheses + a memory-model bridge with a zero-extension witness on
    the high bytes. -/
theorem equiv_LWU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lwu_input : PureSpec.LwuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
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
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1)
    (h_rd_zero_iff :
      Transpiler.wrap_to_regidx e2.ptr = 0 ↔ lwu_input.rd = 0)
    (h_rd_idx : lwu_input.rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val)
    -- Memory-bridge premises (S5b).
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (h_main_emit_b :
      main.b_0 r_main = memory_entry_lo e1
      ∧ main.b_1 r_main = memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    (h_ptr_match :
      e1.ptr.toNat
        = lwu_input.r1_val.toNat + (BitVec.signExtend 64 lwu_input.imm).toNat)
    (h_high_bytes_zeroext :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.zeroExtend 64
            ((e1.x3 : BitVec 8) ++ (e1.x2 : BitVec 8)
             ++ (e1.x1 : BitVec 8) ++ (e1.x0 : BitVec 8))) :
    execute_instruction (instruction.LOAD (
      lwu_input.imm,
      regidx.Regidx lwu_input.r1,
      regidx.Regidx lwu_input.rd,
      true,
      4
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_LWU_sail state lwu_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  have h_mem :=
    ZiskFv.Circuit.MemModel.mem_load_correct_4byte
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
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.zeroExtend 64
            (lwu_input.data3 ++ lwu_input.data2
             ++ lwu_input.data1 ++ lwu_input.data0) := by
    rw [h_high_bytes_zeroext, hd0, hd1, hd2, hd3]
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_loadu_4byte_rrrw
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
