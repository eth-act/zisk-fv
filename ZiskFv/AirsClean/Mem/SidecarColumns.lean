import Clean.Circuit.Expression
import ZiskFv.Airs.Mem

/-!
# Mem sidecar column accessors

Low-level decoding of the Mem AIR's stage-2 and scalar sidecar data.  This
module deliberately depends only on Clean's prover-data carrier and the named
Mem AIR types, so the live Mem component can use the same source without an
import cycle through the full-ensemble balance layer.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

/-! `ProverData` keys for generated Mem sidecar columns. Each key stores a
one-column array (`n = 1`); row zero supplies scalars and row indices supply
table columns. -/
namespace MemRawSidecarDataKey

abbrev gsum : String := "Mem.sidecar.gsum"
abbrev im0 : String := "Mem.sidecar.im0"
abbrev im1 : String := "Mem.sidecar.im1"

namespace Segment

abbrev segmentId : String := "Mem.sidecar.segment.segment_id"
abbrev isFirstSegment : String := "Mem.sidecar.segment.is_first_segment"
abbrev isLastSegment : String := "Mem.sidecar.segment.is_last_segment"
abbrev previousSegmentValue0 : String := "Mem.sidecar.segment.previous_segment_value_0"
abbrev previousSegmentValue1 : String := "Mem.sidecar.segment.previous_segment_value_1"
abbrev previousSegmentStep : String := "Mem.sidecar.segment.previous_segment_step"
abbrev previousSegmentAddr : String := "Mem.sidecar.segment.previous_segment_addr"
abbrev segmentLastValue0 : String := "Mem.sidecar.segment.segment_last_value_0"
abbrev segmentLastValue1 : String := "Mem.sidecar.segment.segment_last_value_1"
abbrev segmentLastStep : String := "Mem.sidecar.segment.segment_last_step"
abbrev segmentLastAddr : String := "Mem.sidecar.segment.segment_last_addr"
abbrev distanceBase0 : String := "Mem.sidecar.segment.distance_base_0"
abbrev distanceBase1 : String := "Mem.sidecar.segment.distance_base_1"
abbrev distanceEnd0 : String := "Mem.sidecar.segment.distance_end_0"
abbrev distanceEnd1 : String := "Mem.sidecar.segment.distance_end_1"
abbrev segmentL1 : String := "Mem.sidecar.segment.segment_l1"

end Segment

namespace Permutation

abbrev stdAlpha : String := "Mem.sidecar.permutation.std_alpha"
abbrev stdGamma : String := "Mem.sidecar.permutation.std_gamma"
abbrev l1 : String := "Mem.sidecar.permutation.l1"
abbrev imDirect0 : String := "Mem.sidecar.permutation.im_direct_0"
abbrev imDirect1 : String := "Mem.sidecar.permutation.im_direct_1"
abbrev imDirect2 : String := "Mem.sidecar.permutation.im_direct_2"
abbrev imDirect3 : String := "Mem.sidecar.permutation.im_direct_3"
abbrev imDirect4 : String := "Mem.sidecar.permutation.im_direct_4"
abbrev imDirect5 : String := "Mem.sidecar.permutation.im_direct_5"

end Permutation

end MemRawSidecarDataKey

/-! Fixed-column slots in the component-owned Mem schema. `SEGMENT_L1` and
`__L1__` are physical fixed columns, not prover-data sidecars. -/
namespace MemFixedColumn

abbrev segmentL1 : Nat := 0
abbrev l1 : Nat := 1

end MemFixedColumn

/-! Raw Mem witness slots materializing the four bus-103 range values. These
remain table-resident cells; `generatedTransition` pins them to their
canonical `ProverData` source. -/
namespace MemRangeSidecarRawColumn

abbrev distanceBase0 : Nat := 13
abbrev distanceBase1 : Nat := 14
abbrev distanceEnd0 : Nat := 15
abbrev distanceEnd1 : Nat := 16

end MemRangeSidecarRawColumn

@[reducible]
def memDistanceBase0Expr : Expression FGL := var ⟨MemRangeSidecarRawColumn.distanceBase0⟩

@[reducible]
def memDistanceBase1Expr : Expression FGL := var ⟨MemRangeSidecarRawColumn.distanceBase1⟩

@[reducible]
def memDistanceEnd0Expr : Expression FGL := var ⟨MemRangeSidecarRawColumn.distanceEnd0⟩

@[reducible]
def memDistanceEnd1Expr : Expression FGL := var ⟨MemRangeSidecarRawColumn.distanceEnd1⟩

/-- Read one field element from a one-column `ProverData` array. Missing keys
or out-of-range rows default to zero, matching Clean's `Environment.fromArray`
convention for absent witness cells. -/
@[reducible]
def proverDataColumn (data : ProverData FGL) (key : String) (row : Nat) : FGL :=
  match (data key 1)[row]? with
  | some values => values[0]
  | none => 0

/-- Read a scalar sidecar value from row zero of a one-column `ProverData`
array. -/
@[reducible]
def proverDataScalar (data : ProverData FGL) (key : String) : FGL :=
  proverDataColumn data key 0

@[reducible]
def memSidecarGsumOfProverData (data : ProverData FGL) : Nat -> FGL :=
  proverDataColumn data MemRawSidecarDataKey.gsum

@[reducible]
def memSidecarIm0OfProverData (data : ProverData FGL) : Nat -> FGL :=
  proverDataColumn data MemRawSidecarDataKey.im0

@[reducible]
def memSidecarIm1OfProverData (data : ProverData FGL) : Nat -> FGL :=
  proverDataColumn data MemRawSidecarDataKey.im1

/-- Segment sidecar columns decoded from shared prover data, with
`SEGMENT_L1` supplied by the component-owned fixed schema. -/
@[reducible]
def memSegmentColumnsOfProverDataAndFixed
    (data : ProverData FGL) (segmentL1 : Nat -> FGL) :
    ZiskFv.Airs.Mem.SegmentColumns FGL where
  segment_id := proverDataScalar data MemRawSidecarDataKey.Segment.segmentId
  is_first_segment := proverDataScalar data MemRawSidecarDataKey.Segment.isFirstSegment
  is_last_segment := proverDataScalar data MemRawSidecarDataKey.Segment.isLastSegment
  previous_segment_value_0 :=
    proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentValue0
  previous_segment_value_1 :=
    proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentValue1
  previous_segment_step := proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentStep
  previous_segment_addr := proverDataScalar data MemRawSidecarDataKey.Segment.previousSegmentAddr
  segment_last_value_0 := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastValue0
  segment_last_value_1 := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastValue1
  segment_last_step := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastStep
  segment_last_addr := proverDataScalar data MemRawSidecarDataKey.Segment.segmentLastAddr
  distance_base_0 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase0
  distance_base_1 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase1
  distance_end_0 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd0
  distance_end_1 := proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd1
  segment_l1 := segmentL1

/-- Permutation/direct-update sidecar columns decoded from shared prover data,
with `__L1__` supplied by the component-owned fixed schema. -/
@[reducible]
def memPermutationColumnsOfProverDataAndFixed
    (data : ProverData FGL) (l1 : Nat -> FGL) :
    ZiskFv.Airs.Mem.PermutationColumns FGL where
  std_alpha := proverDataScalar data MemRawSidecarDataKey.Permutation.stdAlpha
  std_gamma := proverDataScalar data MemRawSidecarDataKey.Permutation.stdGamma
  l1 := l1
  im_direct_0 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect0
  im_direct_1 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect1
  im_direct_2 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect2
  im_direct_3 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect3
  im_direct_4 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect4
  im_direct_5 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect5

/-- Legacy all-prover-data decoder retained for the existing high-level
sidecar package. New live-component code must use
`memSegmentColumnsOfProverDataAndFixed`. -/
@[reducible]
def memSegmentColumnsOfProverData
    (data : ProverData FGL) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  memSegmentColumnsOfProverDataAndFixed data
    (proverDataColumn data MemRawSidecarDataKey.Segment.segmentL1)

/-- Legacy all-prover-data decoder retained for the existing high-level
sidecar package. New live-component code must use
`memPermutationColumnsOfProverDataAndFixed`. -/
@[reducible]
def memPermutationColumnsOfProverData
    (data : ProverData FGL) :
    ZiskFv.Airs.Mem.PermutationColumns FGL :=
  memPermutationColumnsOfProverDataAndFixed data
    (proverDataColumn data MemRawSidecarDataKey.Permutation.l1)

end ZiskFv.AirsClean.Mem
