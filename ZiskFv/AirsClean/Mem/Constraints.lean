import ZiskFv.AirsClean.Mem.Spec
import Clean.Circuit.Basic

/-!
# Mem circuit operations (the `main` field of the Component)

The 9 F-typed constraint emissions of ZisK's Mem AIR, expressed as
a Clean circuit do-block. Mirrors the per-row constraints in
`build/extraction/Extraction/Mem.lean`'s
`constraint_3_every_row` through `constraint_23_every_row`.

The `main` operation here is the constraint-emitting side; the
matching Spec proof (showing these constraints imply the per-row
Spec) is in `Soundness.lean`.

## Trust note

No axioms. Pure operational declaration.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open Circuit (assertZero)

/-- The 9 F-typed Mem constraints emitted per row. Returns `Unit`
    because Mem's main constraints introduce no fresh witnesses. -/
@[circuit_norm]
def main (row : Var MemRow FGL) : Circuit FGL Unit := do
  -- sel_dual boolean
  assertZero (row.sel_dual * (1 - row.sel_dual))
  -- sel_dual implies sel
  assertZero ((1 - row.sel) * row.sel_dual)
  -- sel boolean
  assertZero (row.sel * (1 - row.sel))
  -- addr_changes boolean
  assertZero (row.addr_changes * (1 - row.addr_changes))
  -- wr boolean
  assertZero (row.wr * (1 - row.wr))
  -- wr implies sel
  assertZero (row.wr * (1 - row.sel))
  -- read_same_addr definitional identity
  assertZero (row.read_same_addr - (1 - row.addr_changes) * (1 - row.wr))
  -- address change without write zeros low value chunk
  assertZero ((row.addr_changes * (1 - row.wr)) * row.value_0)
  -- address change without write zeros high value chunk
  assertZero ((row.addr_changes * (1 - row.wr)) * row.value_1)

end ZiskFv.AirsClean.Mem
