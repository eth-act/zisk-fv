import ZiskFv.AirsClean.MemAlign.Spec
import Clean.Circuit.Basic
import ZiskFv.Channels.MemoryBus
import ZiskFv.Channels.MemAlignRom

/-!
# MemAlign circuit operations

The 16 per-row F-typed constraints captured here. The cross-row
constraints (`delta_addr_definition` + 8 `down_to_up_continuity_N`,
referencing `reg_*` / `addr` of `row - 1`) live in `CrossRow.lean`
as a standalone adjacency predicate consumed by downstream callers.

The memory-bus extension below mirrors `mem_align.pil:189`:

```
permutation(MEMORY_ID,
  [wr * (MEMORY_STORE_OP - MEMORY_LOAD_OP) + MEMORY_LOAD_OP,
   addr * CHUNK_NUM + offset, step, width, ...value],
  sel: sel_prove - sel_assume)
```

with `CHUNK_NUM = 8` and `sel_assume = sel_up_to_down + sel_down_to_up`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Circuit (assertZero)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel MemAlignRomMessage)

@[circuit_norm]
def main (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  assertZero (row.wr * (1 - row.wr))
  assertZero (row.reset * (1 - row.reset))
  assertZero (row.sel_up_to_down * (1 - row.sel_up_to_down))
  assertZero (row.sel_down_to_up * (1 - row.sel_down_to_up))
  assertZero (row.sel_0 * (1 - row.sel_0))
  assertZero (row.sel_1 * (1 - row.sel_1))
  assertZero (row.sel_2 * (1 - row.sel_2))
  assertZero (row.sel_3 * (1 - row.sel_3))
  assertZero (row.sel_4 * (1 - row.sel_4))
  assertZero (row.sel_5 * (1 - row.sel_5))
  assertZero (row.sel_6 * (1 - row.sel_6))
  assertZero (row.sel_7 * (1 - row.sel_7))
  assertZero (row.preL1 * row.pc)
  assertZero (row.sel_prove * (row.sel_up_to_down + row.sel_down_to_up))
  -- value_0 reconstruction: 8-way selector multiplexer over reg_0..7
  -- (sel_prove branch with byte-rotation) plus sel_assume branch
  -- (low 32-bit recombination of reg_0..3). Inlined factors below.
  assertZero (row.value_0 -
    (row.sel_prove *
      (row.sel_0 * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)
       + row.sel_1 * (row.reg_1 + row.reg_2 * 256 + row.reg_3 * 65536 + row.reg_4 * 16777216)
       + row.sel_2 * (row.reg_2 + row.reg_3 * 256 + row.reg_4 * 65536 + row.reg_5 * 16777216)
       + row.sel_3 * (row.reg_3 + row.reg_4 * 256 + row.reg_5 * 65536 + row.reg_6 * 16777216)
       + row.sel_4 * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)
       + row.sel_5 * (row.reg_5 + row.reg_6 * 256 + row.reg_7 * 65536 + row.reg_0 * 16777216)
       + row.sel_6 * (row.reg_6 + row.reg_7 * 256 + row.reg_0 * 65536 + row.reg_1 * 16777216)
       + row.sel_7 * (row.reg_7 + row.reg_0 * 256 + row.reg_1 * 65536 + row.reg_2 * 16777216))
     + (row.sel_up_to_down + row.sel_down_to_up)
       * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)))
  -- value_1 reconstruction: dual lane (cycles starting at reg_4).
  assertZero (row.value_1 -
    (row.sel_prove *
      (row.sel_0 * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)
       + row.sel_1 * (row.reg_5 + row.reg_6 * 256 + row.reg_7 * 65536 + row.reg_0 * 16777216)
       + row.sel_2 * (row.reg_6 + row.reg_7 * 256 + row.reg_0 * 65536 + row.reg_1 * 16777216)
       + row.sel_3 * (row.reg_7 + row.reg_0 * 256 + row.reg_1 * 65536 + row.reg_2 * 16777216)
       + row.sel_4 * (row.reg_0 + row.reg_1 * 256 + row.reg_2 * 65536 + row.reg_3 * 16777216)
       + row.sel_5 * (row.reg_1 + row.reg_2 * 256 + row.reg_3 * 65536 + row.reg_4 * 16777216)
       + row.sel_6 * (row.reg_2 + row.reg_3 * 256 + row.reg_4 * 65536 + row.reg_5 * 16777216)
       + row.sel_7 * (row.reg_3 + row.reg_4 * 256 + row.reg_5 * 65536 + row.reg_6 * 16777216))
     + (row.sel_up_to_down + row.sel_down_to_up)
       * (row.reg_4 + row.reg_5 * 256 + row.reg_6 * 65536 + row.reg_7 * 16777216)))

@[reducible]
def selAssumeExpr (row : Var MemAlignRow FGL) : Expression FGL :=
  row.sel_up_to_down + row.sel_down_to_up

@[reducible]
def memBusMessageExpr (row : Var MemAlignRow FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := row.wr + 1
    ptr := row.addr * 8 + row.offset
    timestamp := row.step
    width := row.width
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- The exact `FLAGS` slot of MemAlign hint #998.  This is the literal
    `mem_align.pil:139-143` packing, retained independently of the separate
    D3 successor relation for `delta_pc`. -/
@[reducible]
def memAlignRomFlagsExpr (row : Var MemAlignRow FGL) : Expression FGL :=
  row.sel_0 + row.sel_1 * 2 + row.sel_2 * 4 + row.sel_3 * 8 + row.sel_4 * 16 +
    row.sel_5 * 32 + row.sel_6 * 64 + row.sel_7 * 128 + row.wr * 256 +
      row.reset * 512 + row.sel_up_to_down * 1024 + row.sel_down_to_up * 2048

/-- The bus-133 assumes tuple from MemAlign hint #998.  Its `deltaPc` cell is
    constrained by the component's D3 cyclic-successor transition, so this is
    the source-linked `[pc, pc' - pc, delta_addr, offset, width, flags]`
    tuple on every effective row, including the final-to-zero wrap. -/
@[reducible]
def memAlignRomMessageExpr (row : Var MemAlignRow FGL) :
    MemAlignRomMessage (Expression FGL) :=
  { pc := row.pc
    deltaPc := row.delta_pc
    deltaAddr := row.delta_addr
    offset := row.offset
    width := row.width
    flags := memAlignRomFlagsExpr row }

@[circuit_norm]
def mainWithMemBus (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit (row.sel_prove - selAssumeExpr row) (memBusMessageExpr row)

@[circuit_norm]
def mainWithMemBusAndMemAlignRom (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  mainWithMemBus row
  MemAlignRomChannel.emit (-1) (memAlignRomMessageExpr row)

@[reducible] def memAlignWithMemBusElaborated :
    ElaboratedCircuit FGL MemAlignRow unit where
  name := "MemAlignWithMemBus"
  main := mainWithMemBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [MemBusChannel.emitted (row.sel_prove - selAssumeExpr row) (memBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, mainWithMemBus, main, selAssumeExpr,
      memBusMessageExpr, MemBusChannel]

@[reducible] def memAlignWithMemBusAndMemAlignRomElaborated :
    ElaboratedCircuit FGL MemAlignRow unit where
  name := "MemAlignWithMemBusAndMemAlignRom"
  main := mainWithMemBusAndMemAlignRom
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw, MemAlignRomChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [MemBusChannel.emitted (row.sel_prove - selAssumeExpr row) (memBusMessageExpr row)] ++
    expose MemAlignRomChannel
      [MemAlignRomChannel.emitted (-1) (memAlignRomMessageExpr row)]
  channelsLawful := by
    simp [circuit_norm, mainWithMemBusAndMemAlignRom, mainWithMemBus, main,
      selAssumeExpr, memBusMessageExpr, memAlignRomMessageExpr, memAlignRomFlagsExpr,
      MemBusChannel, MemAlignRomChannel]

end ZiskFv.AirsClean.MemAlign
