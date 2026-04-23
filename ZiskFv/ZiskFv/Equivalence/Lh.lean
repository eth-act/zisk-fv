import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadHalf
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.lh
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LH (load halfword, signed / sign-extended).
Phase 3C T-SL1 — sibling of LW under `SignExtendLoadArchetype`.

LH's Phase 3B pure-spec equivalence
(`PureSpec.execute_LOADH_pure_equiv` in `ZiskFv/RV64D/lh.lean`) closes
directly — unlike LW, LH's tactic skeleton handles the residual
arithmetic cleanly. No escape-hatch helper axiom is required.

Parallels the Phase 3A LHU / LBU equivalence structure (same trio of
theorems) with LW's bus-passthrough corollary (`a_hi = m.a_1 r_main`,
`b_hi = m.b_1 r_main`) rather than LW's bus-zeroing corollary (since
LH has `m32 = 0`).
-/

namespace ZiskFv.Equivalence.Lh

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.LoadHalf

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LH theorem.** With the LH-shape Main constraints
    (`is_external_op = 1`, `op = OP_SIGNEXTEND_H`, `m32 = 0`,
    `flag = 0`, `set_pc = 0`) plus a bus-match to a secondary entry,
    the entry's `a_hi` / `b_hi` lanes equal the Main row's `a_1` /
    `b_1` lanes (`m32 = 0` passthrough). -/
theorem equiv_LH
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : lh_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main :=
  lh_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LH (`.LOAD (imm, rs1, rd, false, 2)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADH_pure`.
    Wraps `PureSpec.execute_LOADH_pure_equiv` (closes directly; no
    escape-hatch axiom). -/
theorem equiv_LH_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lh_state_assumptions lh_input state) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm,
        regidx.Regidx lh_input.r1,
        regidx.Regidx lh_input.rd,
        false,
        2
      ))) state
      = let output := PureSpec.execute_LOADH_pure lh_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADH_pure_equiv
    lh_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 LH
    equals the state computed by applying `bus_effect` to the
    circuit's execution + memory bus rows. Composes `equiv_LH_sail`
    with the bus-matching hypothesis `h_bus_execute_matches_sail`
    (Phase-4-deferred bus-emission derivation). -/
theorem equiv_LH_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lh_state_assumptions lh_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADH_pure lh_input
           (do
             Sail.writeReg Register.nextPC output.nextPC
             match output.rd with
               | .some (rd, rd_val) => write_xreg rd rd_val
               | .none => pure ()
             pure (ExecutionResult.Retire_Success ())) state)) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm,
        regidx.Regidx lh_input.r1,
        regidx.Regidx lh_input.rd,
        false,
        2
      ))) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LH_sail state lh_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Lh
