import ZiskFv.Compliance_v1
import ZiskFv.Equivalence.Divu

/-!
# Phase 5 partial — Compliance_v2 dispatcher (DIVU arm)

DIVU (Arith family representative). The other 12 Arith arms (DIV, REM,
REMU, DIVW, DIVUW, REMW, REMUW, MUL, MULH, MULHU, MULHSU, MULW)
follow the same multi-hypothesis ArithMul/ArithDiv pattern — each
needs its own v2 probe + dispatcher arm.

## Trust note

No new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Vm
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : ℕ}

def OpEnvelope.exec_eq_v2_divu
    : OpEnvelope state m r_main → Prop
  | .divu _ r1 r2 rd bus _ _ _ _ _ _ _ _ =>
      (do
        Sail.writeReg Register.nextPC
          (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
        = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state
  | _ => True

theorem zisk_riscv_compliant_program_bus_v2_divu
    (env : OpEnvelope state m r_main) :
    env.exec_eq_v2_divu := by
  cases env with
  | divu divu_input r1 r2 rd bus v r_a
         pins h_match_primary promises bounds h_row_constraints h_op2_ne =>
    simp only [OpEnvelope.exec_eq_v2_divu]
    exact ZiskFv.Equivalence.Divu.equiv_DIVU state divu_input r1 r2 rd bus m r_main v r_a
      pins h_match_primary promises bounds h_row_constraints h_op2_ne
  | _ => trivial

end ZiskFv.Compliance
