import ZiskFv.AirsClean.Mem.Spec
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
only; sub-doubleword goes through MemAlign* on the separate
MemAlignBus). The byte address is `addr * 8`, `mem_op = wr + 1`
(read = 1, write = 2), and the multiplicity is `+sel` (provider side).

Modelled here as a `MemBusChannel.emit` with the 5-slot
`MemBusMessage` shape. The optional `dual_mem` emission at
`mem.pil:438-441` is not included; it adds a second push that's a
mirror of the primary one with `step_dual` and `sel_dual`. T4.1 will
include it once the dual_mem flag handling lands. -/

open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- Mem's provider-side memory-bus message: `as = wr + 1` (LOAD=1,
    STORE=2), `ptr = addr * 8`, `value` from the row's chunks,
    `timestamp = step`. -/
@[reducible]
def memBusMessageExpr (row : Var MemRow FGL) : MemBusMessage (Expression FGL) :=
  { as := row.wr + 1
    ptr := row.addr * 8
    value_0 := row.value_0
    value_1 := row.value_1
    timestamp := row.step }

/-- Mem constraints + provider-side memory-bus emission.

    Clean's `pull` has fixed multiplicity `+1`; Mem needs the
    row-selector, so this uses `emit (+sel)` directly. -/
@[circuit_norm]
def memWithMemBus (row : Var MemRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit row.sel (memBusMessageExpr row)

/-- Elaborated `memWithMemBus` circuit, ready for use in the
    memory-family ensemble (T4.1). -/
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

end ZiskFv.AirsClean.Mem
