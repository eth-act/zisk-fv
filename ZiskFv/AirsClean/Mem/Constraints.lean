import ZiskFv.AirsClean.Mem.Spec
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Airs.Mem
import ZiskFv.Channels.MemoryBus
import ZiskFv.Channels.SegmentContinuation
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
open ZiskFv.Channels.SegmentContinuation (SeamContChannel SeamMessage)

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

/-- The incoming-boundary seam message PULLed by a segment (the raw
    `previous_segment_*` tuple, tagged with `segment_id`). Mirrors the
    `direct_gsum_0` tag (`ZiskFv/Airs/Mem.lean:1351-1358`). -/
@[reducible]
def prevSeamMessageExpr (row : Var MemRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := row.previous_segment_value_0
    value_1 := row.previous_segment_value_1
    addr := row.previous_segment_addr
    step := row.previous_segment_step
    segment_id := row.segment_id }

/-- The outgoing-boundary seam message PUSHed by a segment (the raw
    `segment_last_*` tuple, tagged with `segment_id + 1`). Mirrors the
    `direct_gsum_1` tag (`ZiskFv/Airs/Mem.lean:1361-1368`). -/
@[reducible]
def lastSeamMessageExpr (row : Var MemRow FGL) : SeamMessage (Expression FGL) :=
  { value_0 := row.segment_last_value_0
    value_1 := row.segment_last_value_1
    addr := row.segment_last_addr
    step := row.segment_last_step
    segment_id := row.segment_id + 1 }

/-- Mem constraints + provider-side memory-bus emission.

    Clean's `pull` has fixed multiplicity `+1`; Mem needs the
    row-selector, so this uses `emit (+sel)` directly. -/
@[circuit_norm]
def memWithMemBus (row : Var MemRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit row.sel (memBusMessageExpr row)

/-- Mem constraints + both provider-side memory-bus emissions for the
    pinned `dual_mem = 1` PIL instance, PLUS the cross-segment continuation
    seam emission (XCAP #103, route (b)).

    The two MemBus emits are IDENTICAL to the bus-only component, so the Mem
    timeline machinery (keyed on those emissions + the per-row `Spec`) is
    unaffected. The seam interactions use `emit` (NOT `pull`/`push`): both go
    into `channelsWithRequirements` (`assumeGuarantees = false`), keeping the
    seam OUT of `channelsWithGuarantees` (PLAN §4 gotcha — a `pull` would land in
    guarantees, which `SoundEnsemble.subset_finished` drags into `finished`).
    The incoming boundary is pulled (mult `-seg_last`, tag `segment_id`); the
    outgoing boundary is pushed gated by `seg_last * (1 - is_last_segment)`
    (tag `segment_id + 1`, `mem.pil:198/235/241`).

    XCAP #103 deep refactor (steps B/A): BOTH seam emissions are now gated by
    `seg_last` (`SEGMENT_LAST`, `mem.pil:87`). A multi-row segment therefore emits
    exactly ONE live pull + ONE live push (its `seg_last = 1` last row) and `k - 1`
    DEAD (multiplicity-0) emissions — making the cross-segment continuation
    faithful to a real multi-row Mem trace (the ungated per-row emission only
    balanced at k = 1). The dead rows are balance-inert (`balanceOf` of a
    multiplicity-0 interaction is `0`), so global balance is unaffected by them. -/
@[circuit_norm]
def memWithDualMemBus (row : Var MemRow FGL) : Circuit FGL Unit := do
  main row
  MemBusChannel.emit row.sel (memBusMessageExpr row)
  MemBusChannel.emit row.sel_dual (memBusDualMessageExpr row)
  SeamContChannel.emit (-row.seg_last) (prevSeamMessageExpr row)
  SeamContChannel.emit (row.seg_last * (1 - row.is_last_segment)) (lastSeamMessageExpr row)

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
  channelsWithRequirements := [MemBusChannel.toRaw, SeamContChannel.toRaw]
  -- Expose BOTH the MemBus provider emissions (unchanged) AND the seam pull/push.
  -- Listing MemBus first keeps `componentWithDualMemBus_interactionsWith_memBus`
  -- selecting the MemBus entry by `interactionsWith MemBusChannel.toRaw`; the seam
  -- entry is reached by `interactionsWith SeamContChannel.toRaw`.
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted row.sel (memBusMessageExpr row)
        , MemBusChannel.emitted row.sel_dual (memBusDualMessageExpr row) ]
    ++ expose SeamContChannel
      [ SeamContChannel.emitted (-row.seg_last) (prevSeamMessageExpr row),
        SeamContChannel.emitted (row.seg_last * (1 - row.is_last_segment))
          (lastSeamMessageExpr row) ]
  channelsLawful := by
    simp [circuit_norm, memWithDualMemBus, main, memBusMessageExpr,
      memBusDualMessageExpr, prevSeamMessageExpr, lastSeamMessageExpr,
      MemBusChannel, SeamContChannel, Channel.toRaw, RawChannel.mk.injEq]

end ZiskFv.AirsClean.Mem
