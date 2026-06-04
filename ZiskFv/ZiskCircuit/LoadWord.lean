import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.SignExtendLoadArchetype

/-!
Compositional LW (load word, signed / sign-extended) spec.

Pilot of the **`SignExtendLoadArchetype`**. LW differs structurally
from the zero-extension loads (LD/LWU/LHU/LBU) in the
`c`-population mechanism:

* Zero-extension loads (`OP_COPYB = 1`, `is_external_op = 0`): Main
  constraint 9 forces `c = b` directly, with `b` sourced from the
  memory-bus entry. `c_packed = memory_entry_toField entry`.
* Signed loads (LW: `OP_SIGNEXTEND_W = 41`, `is_external_op = 1`):
  the Main AIR emits an operation-bus entry; the BinaryExtension SM
  pops it, computes the sign-extended value, and pushes the result
  back via the bus reply. The Main row's `c` lanes land from the
  BinaryExtension-side bus push, not from the memory bus.

Consequently LW's compositional theorem lives on the **bus-entry**
side: the Main-emitted `OperationBusEntry` matches the
BinaryExtension SM's entry in shape, with the `m32 = 1` zeroing of
the high `a` / `b` lanes (since the source is 32-bit). The final
conclusion at the Equivalence layer composes this with an
audit-deferred `h_bus_execute_matches_sail` hypothesis tying the
circuit's bus effect to the Sail execution.

The Sail-level companion and equivalence theorem live in
`Equivalence/Lw.lean`; the `SignExtendLoadArchetype` macro is consumed
to discharge the `a_hi = b_hi = 0` bus-zeroing corollary.
-/

namespace ZiskFv.ZiskCircuit.LoadWord

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Tactics.SignExtendLoadArchetype
open ZiskFv.Trusted


/-- LW circuit hypotheses. Specializes
    `sign_extend_load_archetype_circuit_holds` to LW's opcode and
    `m32` pins (`OP_SIGNEXTEND_W`, `m32 = 1`). -/
@[simp]
def lw_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  sign_extend_load_archetype_circuit_holds m r_main bus_entry
    OP_SIGNEXTEND_W 1

/-- **Compositional LW theorem (bus-zeroing).** For an LW-shaped
    Main row (`m32 = 1`), the operation-bus entry emitted to the
    BinaryExtension SM has `a_hi = 0 ∧ b_hi = 0` — i.e. only the
    low 32 bits of `a` / `b` reach the SM, consistent with LW's
    32-bit operand semantics.

    Proof: archetype invocation. -/
lemma lw_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  sign_extend_load_archetype_m32_one_zeros_bus m r_main bus_entry
    OP_SIGNEXTEND_W h

/-- **LW bus-entry op passthrough.** The bus entry's `op` field
    equals `OP_SIGNEXTEND_W` — mirrors Shift-family's op
    passthrough. -/
lemma lw_bus_op
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lw_circuit_holds m r_main bus_entry) :
    bus_entry.op = OP_SIGNEXTEND_W :=
  sign_extend_load_archetype_op_passthrough m r_main bus_entry
    OP_SIGNEXTEND_W 1 h

/-- **LW bus-entry multiplicity.** The bus-entry multiplicity is
    `1` (the Main row pushes one entry per `is_external_op = 1`). -/
lemma lw_bus_multiplicity
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : lw_circuit_holds m r_main bus_entry) :
    bus_entry.multiplicity = 1 :=
  sign_extend_load_archetype_multiplicity_one m r_main bus_entry
    OP_SIGNEXTEND_W 1 h

end ZiskFv.ZiskCircuit.LoadWord
