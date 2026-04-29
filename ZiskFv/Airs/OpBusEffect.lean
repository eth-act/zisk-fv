import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Airs.OperationBus

/-!
# OpBusEffect — operation-bus precondition model (Track Q POC, branch shape)

Partner module to `RV64D/BusEffect.lean`. Where `bus_effect` captures the
**memory-bus** precondition (`.1`) and post-state (`.2`) for the
`[exec_pc_read, exec_nextpc_write]`-shaped execution bus paired with a
list of memory-bus entries, this module captures the **operation-bus**
precondition for branches (BEQ family).

For branch shapes (Track L), the Main AIR's *memory* bus is empty —
`bus_effect exec_row [] state` carries only the PC read in `.1`. The
register reads of `rs1`/`rs2` route instead through the *operation* bus
to the Binary state machine (via `OP_EQ`). The op-bus carries the
*values* of `rs1`/`rs2` directly (in the `a_lo`/`a_hi`/`b_lo`/`b_hi`
lanes), not pointer-indexed register-byte payloads as the memory bus
does for ALU/STORE shapes.

`op_bus_effect`'s `.1` therefore encodes a pair of register-read
equalities relating the bus's lane fields to `read_xreg rs1 / rs2 state`,
where the `BitVec 64` value is reassembled from the lanes via
`Goldilocks.lanes_to_bv64`.

This is the operation-bus analogue the Track Q POC requires: it lets a
branch metaplan theorem replace its scenario-binding `h_input_r1` /
`h_input_r2` parameters with a single `h_op_bus` precondition.

**Multiplicity convention.** Following `Airs/OperationBus.lean`: Main
emits with `multiplicity := is_external_op` (= 1 for an active
branch row). `op_bus_effect` treats `multiplicity = 1` as the
"assume-side" emission whose `.1` precondition fires; entries with
`multiplicity = 0` contribute no precondition; other multiplicities are
"impossible" (the precondition is `True`, the result is the
unreachable error).

**Scope.** This module ships only the *branch* shape (no `c`-write,
empty memory bus). ALU shapes (which already carry their rs1/rs2 via
the memory bus, see `chip_bus_hyps_alu_rrw`) do not need an op-bus
analogue at this layer — their op-bus interaction is the Main↔BinaryAdd
permutation which the existing `matches_entry` machinery handles.
-/

namespace ZiskFv.Airs.OpBusEffect

open Goldilocks
open ZiskFv.Airs.OperationBus

/-- Operation-bus precondition for the branch shape.

    Given a list of operation-bus entries and a Sail state, plus the
    `rs1`/`rs2` register indices the row's `a`/`b` lanes are claimed to
    correspond to (per `transpile_BEQ` and friends), `op_bus_effect`
    accumulates the per-entry `read_xreg`-equalities into `.1`.

    For each entry with `multiplicity = 1` (Main's assume-side branch
    emission), `.1` gains the conjuncts:

      * `read_xreg rs1 state = .ok (lanes_to_bv64 entry.a_lo entry.a_hi) state`
      * `read_xreg rs2 state = .ok (lanes_to_bv64 entry.b_lo entry.b_hi) state`

    Entries with `multiplicity = 0` are no-ops; other multiplicities
    are illegal under the structural-bus assumptions (the result is
    `False`, so any downstream proof closes vacuously).

    The `.2` field is unused for the branch shape (branches don't write
    a destination register on the op-bus side either) — we keep the
    `Prop × Prop` shape for symmetry with `bus_effect` so that future
    shapes can populate the second component without breaking callers. -/
def op_bus_effect
    (op_bus : List (OperationBusEntry FGL))
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) : Prop × Prop :=
  List.foldl
    (fun acc entry =>
      if entry.multiplicity = (1 : FGL) then
        let r1_val := Goldilocks.lanes_to_bv64 entry.a_lo entry.a_hi
        let r2_val := Goldilocks.lanes_to_bv64 entry.b_lo entry.b_hi
        ⟨ acc.1
          ∧ read_xreg rs1 state = EStateM.Result.ok r1_val state
          ∧ read_xreg rs2 state = EStateM.Result.ok r2_val state
        , acc.2 ⟩
      else if entry.multiplicity = (0 : FGL) then acc
      else ⟨ False, acc.2 ⟩)
    (⟨True, True⟩ : Prop × Prop)
    op_bus

end ZiskFv.Airs.OpBusEffect
