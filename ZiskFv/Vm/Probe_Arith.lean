import ZiskFv.Compliance.Wrappers.Divu
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probe — DIVU `equiv_<OP>_v2` corollary (Arith family representative)

One v2 wrapper for DIVU (unsigned 64-bit divide). The other Arith
opcodes (DIV, REM, REMU, DIVUW, REMUW, DIVW, REMW, MUL, MULH, MULU,
MULSUH, MULUH, MULW) follow the same Arith-shape pattern with
ArithMul or ArithDiv validators.

The DIVU wrapper exposes 10 parameters including `h_match_primary`
(a `matches_entry` predicate on the cross-AIR bus emission),
`bounds` (8 byte-range bounds on `bus.e2`), `h_row_constraints` (the
per-row ArithDiv constraint conjunction), and `h_op2_ne` (the
non-zero divisor precondition).

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithDiv (Valid_ArithDiv)
open ZiskFv.Trusted (OP_DIVU)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)

namespace ZiskFv.Vm.Probe

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_DIVU_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (divu_input : PureSpec.DivuInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_DIVU)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.Equivalence_v1.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_op2_ne : divu_input.r2_val.toNat ≠ 0) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_DIVU
    state divu_input r1 r2 rd bus m r_main v r_a
    pins h_match_primary promises bounds h_row_constraints h_op2_ne

end ZiskFv.Vm.Probe
