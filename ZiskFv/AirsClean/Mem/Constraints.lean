import ZiskFv.AirsClean.Mem.Spec
import ZiskFv.AirsClean.Mem.SidecarColumns
import ZiskFv.AirsClean.Mem.RangeWiring
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Airs.Mem
import ZiskFv.Channels.MemoryBus
import ZiskFv.Channels.SpecifiedRanges
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
open ZiskFv.Channels.SpecifiedRanges

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

/-- Row-level facts for the range checks that `mem.pil:384-385,397` places on
    the live dual-Mem component. The completeness witness supplies these
    constructibly; accepted traces derive them from component constraints. -/
@[reducible]
def dualMemRowRangeFacts (row : MemRow FGL) : Prop :=
  row.increment_0.val < 2 ^ 22
    ∧ row.increment_1.val < 2 ^ 16
    ∧ row.addr.val < 2 ^ 29
    ∧ row.step.val < 2 ^ 40
    ∧ row.step_dual.val < 2 ^ 40
    ∧ row.previous_step.val < 2 ^ 40
    ∧ (row.sel_dual = 1 → (row.step_dual - row.step - row.wr).val < 2 ^ 24)

/-- Lookup-aware source for the ungated mutable-Mem row range facts: increment
    chunks mirror `mem.pil:384-385`; `addr : bits(29)` mirrors `mem.pil:109`;
    and the three `MEM_STEP_BITS = 40` step columns mirror `mem.pil:110,122`. -/
@[circuit_norm]
def rowRangeLookups (row : Var MemRow FGL) : Circuit FGL Unit := do
  -- `l_increment : bits(22)` / `h_increment : bits(16)`, `mem.pil:384-385`.
  lookup (Table.fromStatic rangeTable22) row.increment_0
  lookup (Table.fromStatic rangeTable16) row.increment_1
  -- `addr : bits(29)`, `mem.pil:109`.
  lookup (Table.fromStatic rangeTable29) row.addr
  -- `step : bits(MEM_STEP_BITS)`, `mem.pil:110`.
  lookup (Table.fromStatic rangeTable40) row.step
  -- `step_dual : bits(MEM_STEP_BITS)`, `mem.pil:122`.
  lookup (Table.fromStatic rangeTable40) row.step_dual
  -- `previous_step : bits(40)`, `mem.pil:365`.
  lookup (Table.fromStatic rangeTable40) row.previous_step

/-- Lookup-aware source for the selector-gated dual-step delta range check.
    Callers should require this witness only on rows where `sel_dual = 1`,
    matching `mem.pil:397`. -/
@[circuit_norm]
def dualStepDeltaRangeLookup (row : Var MemRow FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable24) (row.step_dual - row.step - row.wr)

/-- Live selector-gated form of `mem.pil:397`'s dual-step delta range check.
    Multiplying by `sel_dual` makes inactive rows check the in-range zero while
    retaining the original expression on active rows. -/
@[circuit_norm]
def gatedDualStepDeltaRangeLookup (row : Var MemRow FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable24)
    (row.sel_dual * (row.step_dual - row.step - row.wr))

/-- Lookup-aware source for the segment-level `distance_base` range checks
    used by mutable-Mem continuation segments. -/
@[circuit_norm]
def distanceBaseRangeLookups (lo hi : Expression FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable16) lo
  lookup (Table.fromStatic rangeTable16) hi

/-- Lookup-independent generated Mem constraints `0..=23`, rendered as a
    Clean assertion source over concrete named columns. -/
@[circuit_norm]
def segmentGeneratedConstraintAssertions
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (row : ℕ) : Circuit FGL Unit := do
  assertZero (.const (segment.is_first_segment * (1 - segment.is_first_segment)))
  assertZero (.const (segment.is_last_segment * (1 - segment.is_last_segment)))
  assertZero (.const (segment.is_first_segment * segment.segment_id))
  assertZero (.const (mem.sel_dual row * (1 - mem.sel_dual row)))
  assertZero (.const ((1 - mem.sel row) * mem.sel_dual row))
  assertZero (.const (mem.sel row * (1 - mem.sel row)))
  assertZero (.const (mem.addr_changes row * (1 - mem.addr_changes row)))
  assertZero (.const (mem.wr row * (1 - mem.wr row)))
  assertZero (.const (mem.wr row * (1 - mem.sel row)))
  assertZero (.const (segment.segment_l1 (row + 1) *
    (mem.value_0 row - segment.segment_last_value_0)))
  assertZero (.const (segment.segment_l1 (row + 1) *
    (mem.value_1 row - segment.segment_last_value_1)))
  assertZero (.const (segment.segment_l1 (row + 1) *
    (mem.addr row - segment.segment_last_addr)))
  assertZero (.const (segment.segment_l1 (row + 1) *
    (mem.sel_dual row * (mem.step_dual row - mem.step row) + mem.step row
      - segment.segment_last_step)))
  assertZero (.const ((segment.previous_segment_addr - 335544320)
    - (segment.distance_base_0 + 65536 * segment.distance_base_1)))
  assertZero (.const ((402653183 - segment.segment_last_addr)
    - (segment.distance_end_0 + 65536 * segment.distance_end_1)))
  assertZero (.const (mem.previous_step row
    - (segment.segment_l1 row *
        (segment.previous_segment_step - ZiskFv.Airs.Mem.previous_row_step mem row)
      + ZiskFv.Airs.Mem.previous_row_step mem row)))
  assertZero (.const ((mem.increment_0 row + 4194304 * mem.increment_1 row + 1)
    - (mem.addr_changes row *
        (ZiskFv.Airs.Mem.delta_addr segment mem row - ZiskFv.Airs.Mem.delta_step mem row)
      + ZiskFv.Airs.Mem.delta_step mem row)))
  assertZero (.const ((segment.is_first_segment * segment.segment_l1 row) *
    (1 - mem.addr_changes row)))
  assertZero (.const (mem.read_same_addr row
    - (1 - mem.addr_changes row) * (1 - mem.wr row)))
  assertZero (.const ((1 - mem.addr_changes row) *
    (mem.addr row - ZiskFv.Airs.Mem.segment_previous_addr segment mem row)))
  assertZero (.const (mem.read_same_addr row *
    (mem.value_0 row - ZiskFv.Airs.Mem.segment_previous_value_0 segment mem row)))
  assertZero (.const ((mem.addr_changes row * (1 - mem.wr row)) * mem.value_0 row))
  assertZero (.const (mem.read_same_addr row *
    (mem.value_1 row - ZiskFv.Airs.Mem.segment_previous_value_1 segment mem row)))
  assertZero (.const ((mem.addr_changes row * (1 - mem.wr row)) * mem.value_1 row))

/-- Generated Mem permutation/accumulator constraints `24..=33`, rendered as
    a Clean assertion source over concrete named columns. -/
@[circuit_norm]
def permutationGeneratedConstraintAssertions
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (row : ℕ) : Circuit FGL Unit := do
  assertZero (.const (mem.im_0 row *
    (ZiskFv.Airs.Mem.gsum_increment_1 permutation mem row *
      ZiskFv.Airs.Mem.gsum_dual_step permutation mem row)
    - ((18446744069414584320 * ZiskFv.Airs.Mem.gsum_dual_step permutation mem row)
      + ((0 - mem.sel_dual row) *
        ZiskFv.Airs.Mem.gsum_increment_1 permutation mem row))))
  assertZero (.const (mem.im_1 row *
    (ZiskFv.Airs.Mem.gsum_primary_mem permutation mem row *
      ZiskFv.Airs.Mem.gsum_dual_mem permutation mem row)
    - (mem.sel row * ZiskFv.Airs.Mem.gsum_dual_mem permutation mem row
      + mem.sel_dual row * ZiskFv.Airs.Mem.gsum_primary_mem permutation mem row)))
  assertZero (.const (ZiskFv.Airs.Mem.gsum_accumulator_delta permutation mem row *
    ZiskFv.Airs.Mem.gsum_increment_0 permutation mem row + 1))
  assertZero (.const (permutation.im_direct_0 *
    ZiskFv.Airs.Mem.direct_gsum_0 segment permutation + 1))
  assertZero (.const (permutation.im_direct_1 *
    ZiskFv.Airs.Mem.direct_gsum_1 segment permutation
      - (1 - segment.is_last_segment)))
  assertZero (.const (permutation.im_direct_2 *
    ZiskFv.Airs.Mem.direct_gsum_distance_base_0 segment permutation + 1))
  assertZero (.const (permutation.im_direct_3 *
    ZiskFv.Airs.Mem.direct_gsum_distance_base_1 segment permutation + 1))
  assertZero (.const (permutation.im_direct_4 *
    ZiskFv.Airs.Mem.direct_gsum_distance_end_0 segment permutation + 1))
  assertZero (.const (permutation.im_direct_5 *
    ZiskFv.Airs.Mem.direct_gsum_distance_end_1 segment permutation + 1))
  assertZero (.const (permutation.l1 (row + 1) *
    (segment.segment_id - mem.gsum row
      - (((((permutation.im_direct_0 + permutation.im_direct_1)
        + permutation.im_direct_2) + permutation.im_direct_3)
        + permutation.im_direct_4) + permutation.im_direct_5))))


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
  rowRangeLookups row
  gatedDualStepDeltaRangeLookup row
  MemBusChannel.emit row.sel (memBusMessageExpr row)
  MemBusChannel.emit row.sel_dual (memBusDualMessageExpr row)

/-- Project the live dual-Mem static lookups to the row-level range facts they
    mirror in `mem.pil:384-385,397`. -/
theorem dualMemRowRangeFacts_of_memWithDualMemBus_constraints
    (row : Var MemRow FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env ((memWithDualMemBus row).operations offset)) :
    dualMemRowRangeFacts (eval env row) := by
  simp only [memWithDualMemBus, main, rowRangeLookups,
    gatedDualStepDeltaRangeLookup, MemBusChannel, circuit_norm] at h_holds
  have staticRange := fun (table : Table FGL field) (entry : Expression FGL)
      (h_sound :
        let lookup : Lookup FGL := { table := table.toRaw, entry := #v[entry] }
        lookup.Soundness env) =>
    (Lookup.soundess_def_field table env entry).mp h_sound
  let increment0Table := Table.fromStatic rangeTable22
  let increment0Lookup : Lookup FGL :=
    { table := increment0Table.toRaw, entry := #v[row.increment_0] }
  let increment1Table := Table.fromStatic rangeTable16
  let increment1Lookup : Lookup FGL :=
    { table := increment1Table.toRaw, entry := #v[row.increment_1] }
  let addrTable := Table.fromStatic rangeTable29
  let addrLookup : Lookup FGL := { table := addrTable.toRaw, entry := #v[row.addr] }
  let stepTable := Table.fromStatic rangeTable40
  let stepLookup : Lookup FGL := { table := stepTable.toRaw, entry := #v[row.step] }
  let stepDualTable := Table.fromStatic rangeTable40
  let stepDualLookup : Lookup FGL :=
    { table := stepDualTable.toRaw, entry := #v[row.step_dual] }
  let previousStepTable := Table.fromStatic rangeTable40
  let previousStepLookup : Lookup FGL :=
    { table := previousStepTable.toRaw, entry := #v[row.previous_step] }
  let deltaTable := Table.fromStatic rangeTable24
  let deltaLookup : Lookup FGL :=
    { table := deltaTable.toRaw,
      entry := #v[row.sel_dual * (row.step_dual - row.step - row.wr)] }
  have h_increment_0_contains : increment0Lookup.Contains env := by
    apply h_holds.2 increment0Lookup
    dsimp [increment0Lookup, increment0Table, Table.fromStatic, StaticTable.toTable]
    left
    rfl
  have h_increment_1_contains : increment1Lookup.Contains env := by
    apply h_holds.2 increment1Lookup
    dsimp [increment1Lookup, increment1Table, Table.fromStatic, StaticTable.toTable]
    right; left
    rfl
  have h_addr_contains : addrLookup.Contains env := by
    apply h_holds.2 addrLookup
    dsimp [addrLookup, addrTable, Table.fromStatic, StaticTable.toTable]
    right; right; left
    rfl
  have h_step_contains : stepLookup.Contains env := by
    apply h_holds.2 stepLookup
    dsimp [stepLookup, stepTable, Table.fromStatic, StaticTable.toTable]
    right; right; right; left
    rfl
  have h_step_dual_contains : stepDualLookup.Contains env := by
    apply h_holds.2 stepDualLookup
    dsimp [stepDualLookup, stepDualTable, Table.fromStatic, StaticTable.toTable]
    right; right; right; right; left
    rfl
  have h_previous_step_contains : previousStepLookup.Contains env := by
    apply h_holds.2 previousStepLookup
    dsimp [previousStepLookup, previousStepTable, Table.fromStatic, StaticTable.toTable]
    right; right; right; right; right; left
    rfl
  have h_delta_contains : deltaLookup.Contains env := by
    apply h_holds.2 deltaLookup
    dsimp [deltaLookup, deltaTable, Table.fromStatic, StaticTable.toTable]
    right; right; right; right; right; right
    rfl
  have h_increment_0 := staticRange increment0Table row.increment_0
    (increment0Lookup.table.imply_soundness _ _ h_increment_0_contains)
  have h_increment_1 := staticRange increment1Table row.increment_1
    (increment1Lookup.table.imply_soundness _ _ h_increment_1_contains)
  have h_addr := staticRange addrTable row.addr
    (addrLookup.table.imply_soundness _ _ h_addr_contains)
  have h_step := staticRange stepTable row.step
    (stepLookup.table.imply_soundness _ _ h_step_contains)
  have h_step_dual := staticRange stepDualTable row.step_dual
    (stepDualLookup.table.imply_soundness _ _ h_step_dual_contains)
  have h_previous_step := staticRange previousStepTable row.previous_step
    (previousStepLookup.table.imply_soundness _ _ h_previous_step_contains)
  have h_delta := staticRange deltaTable
    (row.sel_dual * (row.step_dual - row.step - row.wr))
    (deltaLookup.table.imply_soundness _ _ h_delta_contains)
  cases row with
  | mk addr step sel addr_changes step_dual sel_dual value_0 value_1 wr previous_step
      increment_0 increment_1 read_same_addr =>
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
      ProvableStruct.components, ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field] at *
    refine ⟨by simpa [CircuitType.eval_expr, increment0Table, Table.fromStatic,
        StaticTable.toTable, rangeTable22, rangeStaticTable] using h_increment_0,
      by simpa [CircuitType.eval_expr, increment1Table, Table.fromStatic,
        StaticTable.toTable, rangeTable16, rangeStaticTable] using h_increment_1,
      by simpa [CircuitType.eval_expr, addrTable, Table.fromStatic,
        StaticTable.toTable, rangeTable29, rangeStaticTable] using h_addr,
      by simpa [CircuitType.eval_expr, stepTable, Table.fromStatic,
        StaticTable.toTable, rangeTable40, rangeStaticTable] using h_step,
      by simpa [CircuitType.eval_expr, stepDualTable, Table.fromStatic,
        StaticTable.toTable, rangeTable40, rangeStaticTable] using h_step_dual,
      by simpa [CircuitType.eval_expr, previousStepTable, Table.fromStatic,
        StaticTable.toTable, rangeTable40, rangeStaticTable] using h_previous_step, ?_⟩
    have h_delta_range :
        rangeTable24.Spec
          (Expression.eval env sel_dual *
            (Expression.eval env step_dual + -Expression.eval env step + -Expression.eval env wr)) := by
      simpa [Expression.eval, deltaTable, Table.fromStatic, StaticTable.toTable] using h_delta
    intro h_sel_dual
    change Expression.eval env sel_dual = 1 at h_sel_dual
    rw [h_sel_dual] at h_delta_range
    simpa [sub_eq_add_neg, rangeTable24, rangeStaticTable] using h_delta_range

/-- Elaborated dual-aware Mem circuit exposing both primary and dual
    memory-bus provider emissions. Kept separate from `Mem.circuitWithMemBus`
    so existing FullEnsemble proofs can migrate deliberately. -/
@[reducible] def memWithDualMemBusElaborated :
    FormalCircuitBase FGL MemRow unit where
  name := "MemWithDualMemBus"
  main := memWithDualMemBus
  -- `elaborate_circuit` cannot derive this: the gated `sel_dual` range lookup has
  -- no `ExplicitCircuit` instance. These are the same two values the pre-migration
  -- `ElaboratedCircuit` stated by hand.
  elaborated :=
    { localLength _ := 0
      output _ _ := () }
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted row.sel (memBusMessageExpr row)
        , MemBusChannel.emitted row.sel_dual (memBusDualMessageExpr row) ]
  exposedChannels_eq := by
    simp only [circuit_norm, memWithDualMemBus, main, rowRangeLookups,
      gatedDualStepDeltaRangeLookup, memBusMessageExpr, memBusDualMessageExpr, MemBusChannel]

/-- The four source-linked bus-103 range messages retained by the validated
Mem c29--c32 manifest links.  They are negative consumer emissions: as for
Main's consumer channels, this component supplies no local membership
guarantee; the static provider and finished-channel balance own that fact. -/
@[reducible]
def memRangeMessages : List (SpecifiedRangeMessage (Expression FGL)) :=
  rangeMessages

@[circuit_norm]
def memWithDualMemBusAndRange (row : Var MemRow FGL) : Circuit FGL Unit := do
  memWithDualMemBus row
  SpecifiedRangesSliceChannel.emit (-1) (memDistanceMessage distanceBase0Wiring.source)
  SpecifiedRangesSliceChannel.emit (-1) (memDistanceMessage distanceBase1Wiring.source)
  SpecifiedRangesSliceChannel.emit (-1) (memDistanceMessage distanceEnd0Wiring.source)
  SpecifiedRangesSliceChannel.emit (-1) (memDistanceMessage distanceEnd1Wiring.source)

end ZiskFv.AirsClean.Mem
