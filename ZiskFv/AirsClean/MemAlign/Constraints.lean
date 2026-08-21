import ZiskFv.AirsClean.MemAlign.Spec
import Clean.Circuit.Basic
import Clean.Circuit.Formal
import ZiskFv.Channels.MemoryBus
import ZiskFv.Channels.MemAlignRom
import ZiskFv.Channels.MemAlignRanges
import ZiskFv.AirsClean.RangeTables

/-!
# MemAlign circuit operations

The 16 per-row F-typed constraints captured here. The source's nine
predecessor/current constraints and eight successor/current constraints live
intrinsically on `MemAlign.component`'s D1/D3 transition predicates
(`Circuit.lean`), so accepted-trace certificates check them without a
caller-supplied adjacency promise.

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
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel MemAlignRangeMessage)

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
    row.sel_5 * 32 + row.sel_6 * 64 + row.sel_7 * 128 +
      (row.wr * 256 + row.reset * 512 + row.sel_up_to_down * 1024 +
        row.sel_down_to_up * 2048)

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

/-- One exact one-slot bus-107 tuple for a MemAlign register range hint.
    `mem_align.pil:113-118` emits one such Range Check for each `reg[i]`; the
    manifest records their actual hints as #982/#984/#986/#988/#990/#992/#994/#996. -/
@[reducible]
def memAlignRangeMessageExpr (value : Expression FGL) : MemAlignRangeMessage (Expression FGL) :=
  { value }

/-- The source-declared `value[RC] : bits(32)` constraints at
`mem_align.pil:185`. PILOUT does not retain these column declarations. -/
@[circuit_norm]
def valueRangeLookups (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic ZiskFv.AirsClean.RangeTables.rangeTable32) row.value_0
  lookup (Table.fromStatic ZiskFv.AirsClean.RangeTables.rangeTable32) row.value_1

@[circuit_norm]
def mainWithMemBus (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit (row.sel_prove - selAssumeExpr row) (memBusMessageExpr row)

@[circuit_norm]
def mainWithMemBusAndMemAlignRomAndRanges (row : Var MemAlignRow FGL) : Circuit FGL Unit := do
  mainWithMemBus row
  valueRangeLookups row
  MemAlignRomChannel.emit (-1) (memAlignRomMessageExpr row)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_0)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_1)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_2)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_3)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_4)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_5)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_6)
  MemAlignRangeChannel.emit (-1) (memAlignRangeMessageExpr row.reg_7)

/-- Project the source-declared value-column bounds from the live local
MemAlign operations. -/
theorem value_ranges_of_mainWithMemBusAndMemAlignRomAndRanges_constraints
    (row : Var MemAlignRow FGL) (offset : ℕ) (env : Environment FGL)
    (h_constraints : Operations.ConstraintsHold env
      ((mainWithMemBusAndMemAlignRomAndRanges row).operations offset)) :
    (eval env row).value_0.val < 2 ^ 32 ∧ (eval env row).value_1.val < 2 ^ 32 := by
  simp only [mainWithMemBusAndMemAlignRomAndRanges, mainWithMemBus, main,
    valueRangeLookups, memBusMessageExpr, selAssumeExpr, memAlignRomMessageExpr,
    memAlignRomFlagsExpr, memAlignRangeMessageExpr, MemBusChannel,
    MemAlignRomChannel, MemAlignRangeChannel, circuit_norm] at h_constraints
  let valueTable := Table.fromStatic ZiskFv.AirsClean.RangeTables.rangeTable32
  let value0Lookup : Lookup FGL := { table := valueTable.toRaw, entry := #v[row.value_0] }
  let value1Lookup : Lookup FGL := { table := valueTable.toRaw, entry := #v[row.value_1] }
  have h_value_0_contains : value0Lookup.Contains env := by
    apply h_constraints.2 value0Lookup
    dsimp [value0Lookup, valueTable, Table.fromStatic, StaticTable.toTable]
    left
    rfl
  have h_value_1_contains : value1Lookup.Contains env := by
    apply h_constraints.2 value1Lookup
    dsimp [value1Lookup, valueTable, Table.fromStatic, StaticTable.toTable]
    exact Or.inr rfl
  have staticRange := fun (table : Table FGL field) (entry : Expression FGL)
      (h_sound :
        let lookup : Lookup FGL := { table := table.toRaw, entry := #v[entry] }
        lookup.Soundness env) =>
    (Lookup.soundess_def_field table env entry).mp h_sound
  have h_value_0 := staticRange valueTable row.value_0
    (value0Lookup.table.imply_soundness _ _ h_value_0_contains)
  have h_value_1 := staticRange valueTable row.value_1
    (value1Lookup.table.imply_soundness _ _ h_value_1_contains)
  have h_eval_value_0 :
      (eval env row).value_0 = Expression.eval env row.value_0 := by
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]
  have h_eval_value_1 :
      (eval env row).value_1 = Expression.eval env row.value_1 := by
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]
  constructor
  · rw [h_eval_value_0]
    simpa [value0Lookup, valueTable, Table.fromStatic, StaticTable.toTable,
      ZiskFv.AirsClean.RangeTables.rangeTable32,
      ZiskFv.AirsClean.RangeTables.rangeStaticTable] using h_value_0
  · rw [h_eval_value_1]
    simpa [value1Lookup, valueTable, Table.fromStatic, StaticTable.toTable,
      ZiskFv.AirsClean.RangeTables.rangeTable32,
      ZiskFv.AirsClean.RangeTables.rangeStaticTable] using h_value_1

@[reducible] def memAlignWithMemBusElaborated :
    FormalCircuitBase FGL MemAlignRow unit where
  name := "MemAlignWithMemBus"
  main := mainWithMemBus
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [MemBusChannel.emitted (row.sel_prove - selAssumeExpr row) (memBusMessageExpr row)]
  exposedChannels_eq := by
    simp only [circuit_norm, mainWithMemBus, main, selAssumeExpr,
      memBusMessageExpr, MemBusChannel]

end ZiskFv.AirsClean.MemAlign
