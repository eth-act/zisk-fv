import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.ShiftR
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.srlw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 SRLW (Phase 2.5 D4f — `ShiftArchetype`
sibling validation of SLLW).

Mirrors `Equivalence.Shift` for SLLW, with the direction of the shift
swapped on the Sail side (`ropw.SRLW` vs `ropw.SLLW`). The Main-AIR
compositional lemma is the `ShiftArchetype` m32=1 instantiation at
`OP_SRL_W = 37`.

Emits three theorems matching the SLLW trio:

* `equiv_SRLW` — circuit-level: bus `a_hi = b_hi = 0` under m32=1.
* `equiv_SRLW_sail` — Sail-level: `execute_instruction` on an SRLW
  RTYPEW reduces to the pure spec block.
* `equiv_SRLW_metaplan` — metaplan target. Composes the Sail
  equivalence with the shape-(a) bus-effect lemma
  (`bus_effect_matches_sail_alu_rrw`) from Phase 2.5 D3.
-/

namespace ZiskFv.Equivalence.ShiftR

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.ShiftR

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SRLW theorem.** Given the SRLW-mode Main
    constraints (including `m32 = 1`) and the bus-match to a secondary
    entry, the entry carries zero high lanes. Direct instantiation of
    `ShiftArchetype`'s m32=1 macro at `OP_SRL_W`. -/
theorem equiv_SRLW
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : srlw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  srlw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SRLW reduces to the pure-function block. Wraps
    `PureSpec.execute_RTYPE_srlw_pure_equiv` at this module's export
    surface. -/
theorem equiv_SRLW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = let srlw_output := PureSpec.execute_RTYPE_srlw_pure srlw_input
        (do
          Sail.writeReg Register.nextPC srlw_output.nextPC
          match srlw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_srlw_pure_equiv
    srlw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 SRLW
    equals the state computed by applying `bus_effect` to the
    circuit's execution + memory bus rows.

    Same bus-shape as SLLW (shape (a) — register-read +
    register-read + register-write, discharged via
    `bus_effect_matches_sail_alu_rrw`). No `h_bus_execute_matches_sail`
    parameter remains. -/
theorem equiv_SRLW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    -- Phase 2.5 D3 structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_RTYPEW_pure srlw_input.r1_val srlw_input.r2_val ropw.SRLW) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SRLW_sail state srlw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_RTYPE_srlw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.ShiftR
