import ZiskFv.AirsClean.Mem.Spec
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Channels.MemoryBus
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
open Circuit (assertZero lookup)
open ZiskFv.AirsClean.RangeTables

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

/-- Lookup-aware source for the ungated mutable-Mem row range facts:
    `l_increment : bits(22)`, `h_increment : bits(16)`, `addr : bits(29)`,
    and the three `MEM_STEP_BITS = 40` step columns. -/
@[circuit_norm]
def rowRangeLookups (row : Var MemRow FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable22) row.increment_0
  lookup (Table.fromStatic rangeTable16) row.increment_1
  lookup (Table.fromStatic rangeTable29) row.addr
  lookup (Table.fromStatic rangeTable40) row.step
  lookup (Table.fromStatic rangeTable40) row.step_dual
  lookup (Table.fromStatic rangeTable40) row.previous_step

/-- Lookup-aware source for the selector-gated dual-step delta range check.
    Callers should require this witness only on rows where `sel_dual = 1`,
    matching `mem.pil:397`. -/
@[circuit_norm]
def dualStepDeltaRangeLookup (row : Var MemRow FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable24) (row.step_dual - row.step - row.wr)

/-- Lookup-aware source for the segment-level `distance_base` range checks
    used by mutable-Mem continuation segments. -/
@[circuit_norm]
def distanceBaseRangeLookups (lo hi : Expression FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable16) lo
  lookup (Table.fromStatic rangeTable16) hi

@[reducible] def memElaborated :
    ElaboratedCircuit FGL MemRow unit where
  name := "Mem"
  main := main
  localLength _ := 0
  output _ _ := ()

/-! ## T4.0.7 — memory-bus provider emission

`memWithMemBus` extends Mem's per-row `main` circuit with the
provider-side memory-bus emission at `mem.pil:435-436`:

```
const expr mem_op = wr * (MEMORY_STORE_OP - MEMORY_LOAD_OP) + MEMORY_LOAD_OP;
permutation_proves(MEMORY_ID, expressions: [mem_op, addr * bytes, step, bytes, ...value], sel: sel);
```

For the Mem AIR specifically, `bytes = 8` always (aligned doublewords
only; sub-doubleword goes through MemAlign* on the same unified
MemoryBus). The byte address is `addr * 8`, `mem_op = wr + 1`
(read = 1, write = 2), and the multiplicity is `+sel` (provider side).

Modelled here as a `MemBusChannel.emit` with the 6-slot
`MemBusMessage` shape. The compatibility `memWithMemBus` circuit emits
only the primary row; `memWithDualMemBus` also models the pinned
`dual_mem = 1` push at `mem.pil:438-441`, using `MEMORY_LOAD_OP`,
`step_dual`, and `sel_dual`. -/

open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- Mem's provider-side memory-bus message: `mem_op = wr + 1` (LOAD=1,
    STORE=2), `ptr = addr * 8`, `width = 8`, `value` from the row's
    chunks, `timestamp = step`. -/
@[reducible]
def memBusMessageExpr (row : Var MemRow FGL) : MemBusMessage (Expression FGL) :=
  { mem_op := row.wr + 1
    ptr := row.addr * 8
    timestamp := row.step
    width := 8
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- Mem's dual-memory provider-side message when `dual_mem = 1`.
    The PIL row emits a read operation at the same byte address and
    value, but with `timestamp = step_dual` and selector `sel_dual`. -/
@[reducible]
def memBusDualMessageExpr (row : Var MemRow FGL) : MemBusMessage (Expression FGL) :=
  { mem_op := 1
    ptr := row.addr * 8
    timestamp := row.step_dual
    width := 8
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- Mem constraints + provider-side memory-bus emission.

    Clean's `pull` has fixed multiplicity `+1`; Mem needs the
    row-selector, so this uses `emit (+sel)` directly. -/
@[circuit_norm]
def memWithMemBus (row : Var MemRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit row.sel (memBusMessageExpr row)

/-- Mem constraints + both provider-side memory-bus emissions for the
    pinned `dual_mem = 1` PIL instance. -/
@[circuit_norm]
def memWithDualMemBus (row : Var MemRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit row.sel (memBusMessageExpr row)
  MemBusChannel.emit row.sel_dual (memBusDualMessageExpr row)

/-- Elaborated `memWithMemBus` circuit, ready for use in Clean
    memory-bus component assembly. -/
@[reducible] def memWithMemBusElaborated :
    ElaboratedCircuit FGL MemRow unit where
  name := "MemWithMemBus"
  main := memWithMemBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel [MemBusChannel.emitted row.sel (memBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, memWithMemBus, main, memBusMessageExpr, MemBusChannel]

/-- Elaborated dual-aware Mem circuit exposing both primary and dual
    memory-bus provider emissions. Kept separate from `memWithMemBusElaborated`
    so existing FullEnsemble proofs can migrate deliberately. -/
@[reducible] def memWithDualMemBusElaborated :
    ElaboratedCircuit FGL MemRow unit where
  name := "MemWithDualMemBus"
  main := memWithDualMemBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted row.sel (memBusMessageExpr row)
        , MemBusChannel.emitted row.sel_dual (memBusDualMessageExpr row) ]
  channelsLawful := by
    simp only [circuit_norm, memWithDualMemBus, main, memBusMessageExpr,
      memBusDualMessageExpr, MemBusChannel]

end ZiskFv.AirsClean.Mem
