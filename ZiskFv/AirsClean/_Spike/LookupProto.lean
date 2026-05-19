import Clean.Circuit.Lookup
import Clean.Circuit.LookupCircuit
import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# Phase 0 spike — Clean lookup-channel composition prototype

Validates that Clean's `Lookup`/`Table`/`StaticTable`/`LookupCircuit`
APIs and `Air.Flat.Component` compose at the type level. This file
exists to confirm the modules **import and elaborate together** so
A6/A7/A8 can use the lookup-channel path (vs. the axiom-fallback per
plan decision #7).

If this file builds, the imports are sound and the API surface is
sufficient for per-AIR lookup integration. Building an actual sound
lookup is out of scope here — the per-AIR ports will construct
specific tables (`BinaryTable`, `BinaryExtensionTable`, `ArithTable`)
using these primitives.

## Trust note

No axioms. Pure spike.
-/

namespace ZiskFv.AirsClean.Spike

open Goldilocks

/-- A trivial 3-field row, used as a Provable row type for the spike. -/
structure AndRow (F : Type) where
  a : F
  b : F
  c : F
deriving ProvableStruct

/-- A `RawTable` instance exists for our field/arity choice. -/
example : Type := RawTable FGL

/-- A `Table FGL AndRow` instance is constructible. -/
example : Table FGL AndRow := {
  name := "spike_and_1bit"
  Contains := fun _ _ => True
}

/-- A `Lookup FGL` value is constructible from a `Table.toRaw` + entry. -/
example (t : Table FGL AndRow) (entry : Vector (Expression FGL) (size AndRow)) :
    Lookup FGL := {
  table := t.toRaw
  entry := entry
}

/-- `StaticTable FGL AndRow` is constructible (signature only — the spec
    machinery checks elsewhere; we just need to know the type compiles). -/
example : Type := StaticTable FGL AndRow

/-- `LookupCircuit` is constructible at the type level. -/
example : Type := LookupCircuit FGL AndRow AndRow

-- Note: `Air.Flat.Component FGL` is not imported here to avoid the known
-- `Fin.foldl_eq_foldl_finRange` collision with `Clean.Utils.Misc`. The
-- existing `ZiskFv/AirsClean/BinaryAdd/` files demonstrate Component
-- usage with narrower imports; per-AIR ports follow that precedent.

end ZiskFv.AirsClean.Spike
