import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.Airs.BinaryTable
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Equivalence.RdValDerivation.Arith

/-!
# RdValDerivation.BinaryCompare — `h_rd_val` discharges for SLT / SLTU / SLTI / SLTIU

**finishing2.md S4 (N-ALU-Binary-Compare).** Currently empty pending an
S0 strengthening of `BinaryTable.wf_LT` / `wf_LTU` to carry final-byte
aggregation semantics.

## Why empty

The four signed/unsigned compare opcodes route through ZisK's `Binary`
AIR with `op_lit = OP_LT (= 7)` or `OP_LTU (= 6)` (per `BusShape.lean::
bus_shape_for_SLT`). The Binary SM's per-byte specification in
`Airs/BinaryTable.lean` currently carries only the **per-byte chain
clause** for these ops:

```
def wf_LTU (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_LTU →
    e.c_byte.val = 0 ∧
    -- chain semantics: cout encodes a < b / a = b / a > b
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0)
```

Critically missing: the **final-byte aggregation rule** that lifts the
8-byte cout chain to a single 64-bit comparison outcome. From
`vendor/zisk/state-machines/binary/pil/binary_table.pil`'s `for` loop
in the `OP_LTU` branch, the final byte (where `pos_ind = 1` for 64-bit
or `pos_ind = mode32` at the half-byte boundary) follows the same
chain rule and the **whole-result comparison value** is `c = cout` of
the final byte (the `use_last_cout_as_c` switch in the PIL).

Without that final-byte aggregation in `wf_LTU`, no Tier-1 derivation
of SLT/SLTU/SLTI/SLTIU is possible from the in-tree primitives:
* The K1-B lifts in `BinaryPackedCorrect.lean` cover only AND/OR/XOR
  (whose semantics is the simple per-byte equality `c = a OP b`); no
  compare lift exists because the per-byte clause alone cannot deliver
  the 64-bit comparison outcome.
* Adding a Compare K1-B lift requires `wf_LTU` to carry the
  `pos_ind = 1 → c_byte.val = ...` aggregation conjunct.

## Escalation

See `docs/fv/track-n-traps.md` § "S4 escalation: SLT/SLTU/SLTI/SLTIU
blocked on wf_LTU / wf_LT aggregation".

The four opcodes are out of scope for this S4 ship; their Tier-1
derivation lemmas land once S0 is strengthened. Until then, the
existing Tier-1.5 (parametric `OperationBusEntry`) lemmas continue to
hold (they accept the `h_input_val` chunk-level OUTPUT-EQ residual as
a parameter); see the metaplan theorem call sites for the current
shape.
-/

namespace ZiskFv.Equivalence.RdValDerivation.BinaryCompare

end ZiskFv.Equivalence.RdValDerivation.BinaryCompare
