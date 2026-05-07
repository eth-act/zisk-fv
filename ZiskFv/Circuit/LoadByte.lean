import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.SignExtendLoadArchetype

/-!
Compositional LB (load byte, signed / sign-extended) spec.

Sibling of LW / LH under `SignExtendLoadArchetype`. Uses
`OP_SIGNEXTEND_B = 39`, `m32 = 0` (narrowest source width).
Bus-passthrough behaviour identical to LH.

See `Spec/LoadWord.lean` for the compositional rationale. The
Sail-level companion and equivalence theorem live in
`Equivalence/Lb.lean`.
-/

namespace ZiskFv.Circuit.LoadByte

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.SignExtendLoadArchetype
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- LB circuit hypotheses. Specializes
    `sign_extend_load_archetype_circuit_holds` to LB's opcode and
    `m32` pins (`OP_SIGNEXTEND_B`, `m32 = 0`). -/
@[simp]
def lb_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  sign_extend_load_archetype_circuit_holds m r_main bus_entry
    OP_SIGNEXTEND_B 0

/-- **Compositional LB theorem (bus-passthrough).** For an LB-shaped
    Main row (`m32 = 0`), the operation-bus entry's `a_hi` / `b_hi`
    lanes carry the Main row's `a_1` / `b_1` lanes verbatim. -/
theorem lb_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lb_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main :=
  sign_extend_load_archetype_m32_zero_passthrough_bus m r_main bus_entry
    OP_SIGNEXTEND_B h

/-- **LB bus-entry op passthrough.** -/
theorem lb_bus_op
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lb_circuit_holds m r_main bus_entry) :
    bus_entry.op = OP_SIGNEXTEND_B :=
  sign_extend_load_archetype_op_passthrough m r_main bus_entry
    OP_SIGNEXTEND_B 0 h

/-- **LB bus-entry multiplicity.** -/
theorem lb_bus_multiplicity
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lb_circuit_holds m r_main bus_entry) :
    bus_entry.multiplicity = 1 :=
  sign_extend_load_archetype_multiplicity_one m r_main bus_entry
    OP_SIGNEXTEND_B 0 h

end ZiskFv.Circuit.LoadByte
