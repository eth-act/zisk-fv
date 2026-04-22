import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.ShiftRA
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.sraw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 SRAW (Phase 3A H2a — `ShiftArchetype`
sibling validation of SLLW/SRLW, register variant).

Mirrors `Equivalence.Shift` / `Equivalence.ShiftR`, with the direction of
the shift swapped on the Sail side (`ropw.SRAW` vs `ropw.SLLW` /
`ropw.SRLW`). The Main-AIR compositional lemma is the `ShiftArchetype`
m32=1 instantiation at `OP_SRA_W = 38`.

Emits three theorems matching the SLLW / SRLW trio:

* `equiv_SRAW` — circuit-level: bus `a_hi = b_hi = 0` under m32=1.
* `equiv_SRAW_sail` — Sail-level: `execute_instruction` on an SRAW
  RTYPEW reduces to the pure spec block.
* `equiv_SRAW_metaplan` — metaplan target. Composes the Sail
  equivalence with the shape-(a) bus-effect lemma
  (`bus_effect_matches_sail_alu_rrw`).
-/

namespace ZiskFv.Equivalence.ShiftRA

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.ShiftRA

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SRAW theorem.** Given the SRAW-mode Main
    constraints (including `m32 = 1`) and the bus-match to a secondary
    entry, the entry carries zero high lanes. Direct instantiation of
    `ShiftArchetype`'s m32=1 macro at `OP_SRA_W`. -/
theorem equiv_SRAW
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : sraw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  sraw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SRAW reduces to the pure-function block. Wraps
    `PureSpec.execute_RTYPE_sraw_pure_equiv` at this module's export
    surface. -/
theorem equiv_SRAW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraw_input : PureSpec.SrawInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sraw_input.r2_val state)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraw_input.PC) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state
      = let sraw_output := PureSpec.execute_RTYPE_sraw_pure sraw_input
        (do
          Sail.writeReg Register.nextPC sraw_output.nextPC
          match sraw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_sraw_pure_equiv
    sraw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 SRAW
    equals the state computed by applying `bus_effect` to the
    circuit's execution + memory bus rows.

    Same bus-shape as SLLW/SRLW (shape (a) — register-read +
    register-read + register-write, discharged via
    `bus_effect_matches_sail_alu_rrw`). No `h_bus_execute_matches_sail`
    parameter remains. -/
theorem equiv_SRAW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraw_input : PureSpec.SrawInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sraw_input.r2_val state)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraw_input.PC)
    -- Phase 2.5 D3 structural bus hypotheses (Phase-4 derivable).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_match :
      (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
        (pure () : SailM Unit)
      else
        let val := U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                                e2.x4, e2.x5, e2.x6, e2.x7]
        let reg_idx : Finset.Icc 1 31 :=
          ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
        write_xreg reg_idx val)
      =
      (match (PureSpec.execute_RTYPE_sraw_pure sraw_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SRAW_sail state sraw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_RTYPE_sraw_pure sraw_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.ShiftRA
