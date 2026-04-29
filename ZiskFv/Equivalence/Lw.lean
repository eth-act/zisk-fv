import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadWord
import ZiskFv.Spec.MemModel
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.lw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LW (load word, signed / sign-extended).
Phase 3C T-SL0 — pilot of the `SignExtendLoadArchetype`. Consumes
`PureSpec.execute_LOADW_pure_equiv` directly (C9 retired by Phase 4
T-LW; also fixed a Phase 3B statement bug that passed
`is_unsigned = true` — correct for RV64 LW is `false`).

Parallels the Phase 3A LHU / LBU equivalence structure (same trio
of theorems). `finishing3` S5b retired the the bus-execute-matches-sail premise
parameter from `equiv_LW_metaplan` in favour of structural bus
hypotheses (Phase 4.5 Track C shape (d) reduction
`bus_effect_matches_sail_load_4byte_rrrw`) plus a memory-model bridge
(`Spec.MemModel.mem_load_correct_4byte`) that derives the bus-side
rd-write byte equalities from circuit primitives.
-/

namespace ZiskFv.Equivalence.Lw

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.LoadWord

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LW theorem.** With the LW-shape Main constraints
    (`is_external_op = 1`, `op = OP_SIGNEXTEND_W`, `m32 = 1`, `flag = 0`,
    `set_pc = 0`) plus a bus-match to a secondary entry, the entry
    carries zeroed high `a` / `b` lanes: `a_hi = 0 ∧ b_hi = 0`. The
    32-bit source operand is conveyed via the low lanes; the
    BinaryExtension SM is responsible for the sign-extension
    computation which feeds back via the bus's `c` lanes. -/
theorem equiv_LW
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : lw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  lw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LW-shape LOAD reduces to the pure-function block supplied by
    `PureSpec.execute_LOADW_pure`, given the standard register/PC/memory
    assumptions. -/
theorem equiv_LW_sail
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

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 LW
    equals the state computed by applying `bus_effect` to the circuit's
    execution + memory bus rows.

    `finishing3` S5b: replaced the previous monolithic
    the bus-execute-matches-sail premise parameter with structural bus
    hypotheses + a memory-model bridge (Mem AIR + ptr-match + per-byte
    e1↔e2 passthrough). The Sail-side rd-write value
    `BitVec.signExtend 64 (data3 ++ data2 ++ data1 ++ data0)` is
    derived from `mem_load_correct_4byte` plus a sign-extension
    witness (`h_high_bytes_signext`) supplied by the caller as a
    LANE-MATCH-class fact about the high bytes of the rd-write
    entry. -/
theorem equiv_LW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lw_state_assumptions lw_input state)
    -- Structural bus hypotheses (Phase 4.5 Track C, shape d-4-signed).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADW_pure lw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1)
    -- Decomposed rd-match hypotheses.
    (h_rd_zero_iff :
      Transpiler.wrap_to_regidx e2.ptr = 0 ↔ lw_input.rd = 0)
    (h_rd_idx : lw_input.rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val)
    -- finishing3 S5b: circuit-level memory bridge + lane match.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (h_main_emit_b :
      main.b_0 r_main = memory_entry_lo e1
      ∧ main.b_1 r_main = memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    (h_ptr_match :
      e1.ptr.toNat
        = lw_input.r1_val.toNat + (BitVec.signExtend 64 lw_input.imm).toNat)
    (h_e1_e2_bytes :
      (e2.x0 : BitVec 8) = e1.x0
      ∧ (e2.x1 : BitVec 8) = e1.x1
      ∧ (e2.x2 : BitVec 8) = e1.x2
      ∧ (e2.x3 : BitVec 8) = e1.x3)
    (h_high_bytes_signext :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.signExtend 64
            ((e1.x3 : BitVec 8) ++ (e1.x2 : BitVec 8)
             ++ (e1.x1 : BitVec 8) ++ (e1.x0 : BitVec 8))) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm,
        regidx.Regidx lw_input.r1,
        regidx.Regidx lw_input.rd,
        false,
        4
      ))) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_LW_sail state lw_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  -- Derive the per-byte data ↔ e1.x_i agreement via mem_load_correct_4byte
  -- + lw_state_assumptions + h_ptr_match.
  have h_mem :=
    ZiskFv.Spec.MemModel.mem_load_correct_4byte
      main mem r_main e1 state h_main_emit_b
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1, h_d2, h_d3,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  rw [h_ptr_match] at h_mem
  obtain ⟨he0, he1, he2, he3⟩ := h_mem
  have hd0 : (e1.x0 : BitVec 8) = lw_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : (e1.x1 : BitVec 8) = lw_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have hd2 : (e1.x2 : BitVec 8) = lw_input.data2 := by
    rw [h_d2] at he2; exact (Option.some.inj he2).symm
  have hd3 : (e1.x3 : BitVec 8) = lw_input.data3 := by
    rw [h_d3] at he3; exact (Option.some.inj he3).symm
  -- Derive the rd-write value equality directly from h_high_bytes_signext
  -- + the per-byte e1.x_i = data_i facts (after rewriting through e1↔e2).
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = BitVec.signExtend 64
            (lw_input.data3 ++ lw_input.data2
             ++ lw_input.data1 ++ lw_input.data0) := by
    rw [h_high_bytes_signext, hd0, hd1, hd2, hd3]
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_load_4byte_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        (BitVec.signExtend 64
          (lw_input.data3 ++ lw_input.data2
           ++ lw_input.data1 ++ lw_input.data0))
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
        h_rd_val_derived]
  -- Discharge the rd-match branch via the decomposed hypotheses.
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

end ZiskFv.Equivalence.Lw
