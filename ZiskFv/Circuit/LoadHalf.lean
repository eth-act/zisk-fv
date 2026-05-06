import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.SignExtendLoadArchetype

/-!
Compositional LH (load halfword, signed / sign-extended) spec.

Sibling of LW under `SignExtendLoadArchetype`. Uses
`OP_SIGNEXTEND_H = 40`, `m32 = 0` (the `"signextend_h"` string does
not contain `"_w"`). Unlike LW the 32-bit bus-zeroing is not active;
the bus carries `a[1]` / `b[1]` verbatim via the `(1 - m32) = 1`
passthrough factor.

See `Spec/LoadWord.lean` for the compositional rationale (why signed
loads use the bus-entry side rather than the memory-bus / `c_packed`
side). The Sail-level companion and equivalence theorem live in
`Equivalence/Lh.lean`.
-/

namespace ZiskFv.Circuit.LoadHalf

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.SignExtendLoadArchetype
open ZiskFv.Trusted

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- LH circuit hypotheses. Specializes
    `sign_extend_load_archetype_circuit_holds` to LH's opcode and
    `m32` pins (`OP_SIGNEXTEND_H`, `m32 = 0`). -/
@[simp]
def lh_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  sign_extend_load_archetype_circuit_holds m r_main bus_entry
    OP_SIGNEXTEND_H 0

/-- **Compositional LH theorem (bus-passthrough).** For an LH-shaped
    Main row (`m32 = 0`), the operation-bus entry's `a_hi` / `b_hi`
    lanes carry the Main row's `a_1` / `b_1` lanes verbatim. -/
theorem lh_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lh_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main :=
  sign_extend_load_archetype_m32_zero_passthrough_bus m r_main bus_entry
    OP_SIGNEXTEND_H h

/-- **LH bus-entry op passthrough.** The bus entry's `op` field
    equals `OP_SIGNEXTEND_H`. -/
theorem lh_bus_op
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lh_circuit_holds m r_main bus_entry) :
    bus_entry.op = OP_SIGNEXTEND_H :=
  sign_extend_load_archetype_op_passthrough m r_main bus_entry
    OP_SIGNEXTEND_H 0 h

/-- **LH bus-entry multiplicity.** -/
theorem lh_bus_multiplicity
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lh_circuit_holds m r_main bus_entry) :
    bus_entry.multiplicity = 1 :=
  sign_extend_load_archetype_multiplicity_one m r_main bus_entry
    OP_SIGNEXTEND_H 0 h

end ZiskFv.Circuit.LoadHalf
