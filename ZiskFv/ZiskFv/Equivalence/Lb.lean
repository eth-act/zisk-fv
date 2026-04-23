import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.LoadByte
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.RV64D.lb
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 LB (load byte, signed / sign-extended).
Phase 3C T-SL2 — sibling of LW / LH under `SignExtendLoadArchetype`.

LB's Phase 3B pure-spec equivalence
(`PureSpec.execute_LOADB_pure_equiv` in `ZiskFv/RV64D/lb.lean`)
closes directly — the same tactic skeleton as LH, with alignment
vacuously satisfied for 1-byte loads. No escape-hatch axiom is
required.
-/

namespace ZiskFv.Equivalence.Lb

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.LoadByte

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level LB theorem.** `m32 = 0` bus-passthrough on the
    secondary-SM bus entry. -/
theorem equiv_LB
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : lb_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main :=
  lb_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** Wraps `PureSpec.execute_LOADB_pure_equiv`. -/
theorem equiv_LB_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lb_state_assumptions lb_input state) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state
      = let output := PureSpec.execute_LOADB_pure lb_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADB_pure_equiv
    lb_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** Composes `equiv_LB_sail` with a bus-matching
    hypothesis. -/
theorem equiv_LB_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (mem_row : List (Interaction.MemoryBusEntry FGL))
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.lb_state_assumptions lb_input state)
    (h_bus_execute_matches_sail :
      (bus_effect exec_row mem_row state).2
        = (let output := PureSpec.execute_LOADB_pure lb_input
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
        lb_input.imm,
        regidx.Regidx lb_input.r1,
        regidx.Regidx lb_input.rd,
        false,
        1
      ))) state = (bus_effect exec_row mem_row state).2 := by
  rw [equiv_LB_sail state lb_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  exact h_bus_execute_matches_sail.symm

end ZiskFv.Equivalence.Lb
