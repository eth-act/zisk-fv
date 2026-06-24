import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction
import ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridges
import ZiskFv.AirsClean.FullEnsemble.Balance.MemRowReplayProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-! ### Prover-data-backed Mem sidecar columns -/

/- `ProverData` keys for the generated Mem sidecar columns.

   These names are the Lean-side contract for generated/full-ensemble code:
   each key stores a one-column array (`n = 1`) whose row `0` is used for
   scalars and whose row index is used for table columns. The source map in
   `MemAirFacts.md` ties these keys to pilout witness columns, fixed columns,
   AIR_VALUE entries, and challenges. -/
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

/-- Read one field element from a one-column `ProverData` array.

    Missing keys or out-of-range rows default to zero, matching Clean's
    `Environment.fromArray` convention for absent witness cells. Correctness
    is not hidden here: generated code must still prove
    `MemTableGeneratedRawSourceFacts` for the columns read by this function. -/
@[reducible]
def proverDataColumn (data : ProverData FGL) (key : String) (row : ℕ) : FGL :=
  match (data key 1)[row]? with
  | some values => values[0]
  | none => 0

/-- Read a scalar sidecar value from row `0` of a one-column `ProverData`
    array. -/
@[reducible]
def proverDataScalar (data : ProverData FGL) (key : String) : FGL :=
  proverDataColumn data key 0

@[reducible]
def memSidecarGsumOfProverData (data : ProverData FGL) : ℕ → FGL :=
  proverDataColumn data MemRawSidecarDataKey.gsum

@[reducible]
def memSidecarIm0OfProverData (data : ProverData FGL) : ℕ → FGL :=
  proverDataColumn data MemRawSidecarDataKey.im0

@[reducible]
def memSidecarIm1OfProverData (data : ProverData FGL) : ℕ → FGL :=
  proverDataColumn data MemRawSidecarDataKey.im1

/-- Segment sidecar columns read from the shared Clean `ProverData` map. -/
@[reducible]
def memSegmentColumnsOfProverData
    (data : ProverData FGL) :
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
  segment_l1 := proverDataColumn data MemRawSidecarDataKey.Segment.segmentL1

/-- Permutation/direct-update sidecar columns read from the shared Clean
    `ProverData` map. -/
@[reducible]
def memPermutationColumnsOfProverData
    (data : ProverData FGL) :
    ZiskFv.Airs.Mem.PermutationColumns FGL where
  std_alpha := proverDataScalar data MemRawSidecarDataKey.Permutation.stdAlpha
  std_gamma := proverDataScalar data MemRawSidecarDataKey.Permutation.stdGamma
  l1 := proverDataColumn data MemRawSidecarDataKey.Permutation.l1
  im_direct_0 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect0
  im_direct_1 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect1
  im_direct_2 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect2
  im_direct_3 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect3
  im_direct_4 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect4
  im_direct_5 := proverDataScalar data MemRawSidecarDataKey.Permutation.imDirect5

/-- Table-level sidecar for generated raw Mem AIR source data.

    Generated/full-ensemble code can use this object when it has the concrete
    stage-2 columns and raw split facts for one witness table, but has not yet
    packaged them into the witness-wide `FullWitnessMemAirSourceRawFacts`
    callback. This remains a source-data contract: the raw facts are supplied
    explicitly, and replay evidence is still derived downstream. -/
structure MemTableGeneratedRawSourceSidecar
    (table : Table FGL) : Type 1 where
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  gsum : ℕ → FGL
  im0 : ℕ → FGL
  im1 : ℕ → FGL
  facts :
    MemTableGeneratedRawSourceFacts
      table (memOfTable table gsum im0 im1)
      (segmentWithFixedL1 segment) permutation

namespace MemTableGeneratedRawSourceSidecar

@[reducible]
def mem {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL :=
  memOfTable table sidecar.gsum sidecar.im0 sidecar.im1

@[reducible]
def fixedSegment {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  segmentWithFixedL1 sidecar.segment

def toRawFacts {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    MemTableGeneratedRawSourceFacts
      table sidecar.mem sidecar.fixedSegment sidecar.permutation :=
  sidecar.facts

def toAirFacts {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    MemTableGeneratedAirFacts table sidecar.mem sidecar.fixedSegment sidecar.permutation :=
  memTableGeneratedAirFacts_of_constraintFacts
    sidecar.facts.constraints
    sidecar.facts.rowRanges
    sidecar.facts.segmentRanges

def toAirSource {table : Table FGL} (sidecar : MemTableGeneratedRawSourceSidecar table) :
    MemTableGeneratedAirSource table where
  segment := sidecar.segment
  permutation := sidecar.permutation
  gsum := sidecar.gsum
  im0 := sidecar.im0
  im1 := sidecar.im1
  facts := sidecar.toAirFacts

end MemTableGeneratedRawSourceSidecar

/-- Build a raw Mem sidecar from the shared Clean `ProverData` map.

    This is the generated/full-ensemble entry point when sidecar columns are
    stored in `witness.data`: the raw facts must be proved for the exact
    ProverData-backed columns defined above, then this constructor packages
    them as a `MemTableGeneratedRawSourceSidecar`. -/
def memTableGeneratedRawSourceSidecar_of_proverData
    (table : Table FGL)
    (data : ProverData FGL)
    (h_facts :
      MemTableGeneratedRawSourceFacts
        table
        (memOfTable table
          (memSidecarGsumOfProverData data)
          (memSidecarIm0OfProverData data)
          (memSidecarIm1OfProverData data))
        (segmentWithFixedL1 (memSegmentColumnsOfProverData data))
        (memPermutationColumnsOfProverData data)) :
    MemTableGeneratedRawSourceSidecar table where
  segment := memSegmentColumnsOfProverData data
  permutation := memPermutationColumnsOfProverData data
  gsum := memSidecarGsumOfProverData data
  im0 := memSidecarIm0OfProverData data
  im1 := memSidecarIm1OfProverData data
  facts := h_facts

/-- Build a raw Mem sidecar from `ProverData` columns plus concrete Clean
    assertion and lookup witnesses for those columns. -/
def memTableGeneratedRawSourceSidecar_of_proverDataWitnessFacts
    (table : Table FGL)
    (data : ProverData FGL)
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts
        table
        (memOfTable table
          (memSidecarGsumOfProverData data)
          (memSidecarIm0OfProverData data)
          (memSidecarIm1OfProverData data))
        (segmentWithFixedL1 (memSegmentColumnsOfProverData data))
        (memPermutationColumnsOfProverData data))
    (h_rowRanges :
      MemTableGeneratedRangeLookupFacts
        table
        (memOfTable table
          (memSidecarGsumOfProverData data)
          (memSidecarIm0OfProverData data)
          (memSidecarIm1OfProverData data)))
    (h_segmentRanges :
      MemSegmentGeneratedRangeLookupFacts
        (segmentWithFixedL1 (memSegmentColumnsOfProverData data))) :
    MemTableGeneratedRawSourceSidecar table :=
  memTableGeneratedRawSourceSidecar_of_proverData
    table
    data
    (memTableGeneratedRawSourceFacts_of_witnessFacts
      h_constraints
      h_rowRanges
      h_segmentRanges)

/-- Build the typed Mem AIR source from the three extractor-facing fact
    families. This is the narrow constructor a future generated Lean module can
    call after proving the pilout-generated row constraints and range facts for
    the concrete table projection. -/
def memTableGeneratedAirSource_of_parts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          (segmentWithFixedL1 segment) permutation
          (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment)) :
    MemTableGeneratedAirSource table where
  segment := segment
  permutation := permutation
  gsum := gsum
  im0 := im0
  im1 := im1
  facts :=
    { generatedAt := h_generatedAt
      rowRanges := h_rowRanges
      segmentRanges := h_segmentRanges }

/-- Build the typed Mem AIR source from the extractor's split generated
    constraint groups. This mirrors the generated constraint grouping reported
    by `pil-extract mem-air-facts`: segment constraints `0..=23`, permutation
    constraints `24..=33`, and the explicit range-check facts. -/
def memTableGeneratedAirSource_of_constraintFacts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_constraints :
      MemTableGeneratedConstraintFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment)) :
    MemTableGeneratedAirSource table :=
  memTableGeneratedAirSource_of_parts
    table segment permutation gsum im0 im1
    (generatedAt_of_memTableGeneratedConstraintFacts h_constraints)
    h_rowRanges
    h_segmentRanges

/-- Build the typed Mem AIR source from concrete Clean assertion and lookup
    witnesses.

    This is the narrow generated/full-ensemble target after the Mem source
    surface has been made lookup-aware: generated code supplies assertion
    witnesses for the split generated constraints plus lookup witnesses for the
    row and segment range facts, and Lean projects those witnesses to the raw
    AIR facts consumed by replay. -/
def memTableGeneratedAirSource_of_witnessFacts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_rowRanges :
      MemTableGeneratedRangeLookupFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges :
      MemSegmentGeneratedRangeLookupFacts (segmentWithFixedL1 segment)) :
    MemTableGeneratedAirSource table :=
  memTableGeneratedAirSource_of_constraintFacts
    table segment permutation gsum im0 im1
    (memTableGeneratedConstraintFacts_of_assertionFacts h_constraints)
    (memTableGeneratedRangeFacts_of_lookupFacts h_rowRanges)
    (memSegmentGeneratedRangeFacts_of_lookupFacts h_segmentRanges)

end ZiskFv.AirsClean.FullEnsemble
