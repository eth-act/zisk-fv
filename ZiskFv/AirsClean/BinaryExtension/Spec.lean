import ZiskFv.AirsClean.BinaryExtension.Row

/-!
# BinaryExtension Spec + Assumptions

**BinaryExtension has ZERO F-typed per-row constraints.** Per
`ZiskFv/Airs/Binary/BinaryExtension.lean:5-15`:

> The `BinaryExtension` AIR (pilout idx 12) has zero F-typed
> constraints — all 8 of its constraints are lookup arguments
> (`bus_id = 124` against the BinaryExtensionTable) and
> permutation / operation-bus interactions (mixed F/ExtF, skipped
> at the extraction layer).

So this Spec is `True`. The actual semantic content (sign-extension
of b/h/w slices, byte-chunk decomposition) is enforced entirely by
the lookup against `BinaryExtensionTable`. That lookup integration
is tracked separately at `ZiskFv/Airs/BinaryExtensionTable.lean`
and the Component instantiation for BinaryExtension goes through
the lookup-channel framework — not through `main`'s `assertZero`.

## Trust note

No axioms in Spec/Soundness. The lookup-channel soundness is the
trust assumption (`bin_ext_table_consumer_wf` in the trust ledger).
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

/-- No range constraints needed — selectors are validated by the
    lookup table containing only boolean entries. -/
def Assumptions (_row : BinaryExtensionRow FGL) : Prop := True

/-- No per-row F-typed Spec — all semantics flow through the
    BinaryExtensionTable lookup. -/
def Spec (_row : BinaryExtensionRow FGL) : Prop := True

end ZiskFv.AirsClean.BinaryExtension
