import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.Shift
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.sllw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 SLLW (Phase 2 A6 archetype).

Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_SLLW`, `m32 = 1`);
* the compositional SLLW Main-row spec
  (`ZiskFv.Spec.Shift.sllw_compositional` — high bus lanes zero);
* the Sail pure-function equivalence
  (`PureSpec.execute_RTYPE_sllw_pure_equiv`).

Emits three theorems mirroring the A1 (BEQ) shape:

* `equiv_SLLW` — circuit-level: the `m32 = 1` path zeroes the bus's
  `a_hi` and `b_hi` lanes, delegating to the `BinaryExtension` SM.
* `equiv_SLLW_sail` — Sail-level: `execute_instruction` on a SLLW
  RTYPEW reduces to the pure spec block.
* `equiv_SLLW_metaplan` — the metaplan target shape, composing the
  Sail equivalence with the bus-effect hypothesis.

The `BinaryExtension` bus-emission derivation is **deferred** to
Phase 4 (same decision as A1 for BEQ's Binary SM). `equiv_SLLW` takes
the match hypothesis as a parameter; Phase 4 wires it to a
`Valid_BinaryExtension` AIR.
-/

namespace ZiskFv.Equivalence.Shift

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Shift

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SLLW theorem.** Given the SLLW-mode Main
    constraints (including `m32 = 1`) and the bus-match to a
    secondary entry, the entry carries zero high lanes: `a_hi = 0`
    and `b_hi = 0`. This is the proof that the `m32 = 1` path
    performs the PIL-intended `(1 - m32) * a[1]` bus zeroing — the
    `BinaryExtension` SM sees only the low 32 bits.

    Companion to `equiv_SLLW_sail` below. -/
theorem equiv_SLLW
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : sllw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  sllw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SLLW reduces to the pure-function block supplied by
    `PureSpec.execute_RTYPE_sllw_pure`, given source-register
    readability and PC knowledge. Wraps
    `PureSpec.execute_RTYPE_sllw_pure_equiv` to expose the Sail chain
    at this module's export surface. -/
theorem equiv_SLLW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = let sllw_output := PureSpec.execute_RTYPE_sllw_pure sllw_input
        (do
          Sail.writeReg Register.nextPC sllw_output.nextPC
          match sllw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_RTYPE_sllw_pure_equiv
    sllw_input r1 r2 rd h_input_r1 h_input_r2 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64
    SLLW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Composes `equiv_SLLW_sail` with the bus-matching hypothesis
    `h_bus_execute_matches_sail`. Same shape as
    `equiv_BEQ_metaplan` / `equiv_ADD_metaplan`: the bus-emission-
    correctness obligation is parameterized and deferred to Phase 4.

    **Hypotheses.**
    * Sail side (from `equiv_SLLW_sail`): register readability
      (`h_input_r1`, `h_input_r2`), rd mapping (`h_input_rd`), PC
      (`h_input_pc`).
    * Bus side: `h_bus_execute_matches_sail` asserts that the
      execution + memory bus, fed through `bus_effect`, returns the
      same `EStateM.Result` as the concrete Sail monadic block in
      `equiv_SLLW_sail`'s conclusion. For SLLW the memory-bus
      component is empty (no memory access); the execution bus
      carries read PC + write nextPC + register write. -/
theorem equiv_SLLW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let sllw_output := PureSpec.execute_RTYPE_sllw_pure sllw_input
           (do
             Sail.writeReg Register.nextPC sllw_output.nextPC
             match sllw_output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_SLLW_sail state sllw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Shift
