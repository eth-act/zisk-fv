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

/-- The 9 F-typed extracted Mem constraints + 2 byte-pack constraints
    tying the 8 byte-lane witnesses to `value_0` / `value_1`. -/
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
  -- value_0 byte-pack: ties the lo byte-lane witnesses to the extracted chunk
  assertZero (row.value_0 - (row.x0 + row.x1 * 256 + row.x2 * 65536 + row.x3 * 16777216))
  -- value_1 byte-pack: ties the hi byte-lane witnesses to the extracted chunk
  assertZero (row.value_1 - (row.x4 + row.x5 * 256 + row.x6 * 65536 + row.x7 * 16777216))

@[reducible] def memElaborated :
    ElaboratedCircuit FGL MemRow unit where
  name := "Mem"
  main := main
  localLength _ := 0
  output _ _ := ()

end ZiskFv.AirsClean.Mem
