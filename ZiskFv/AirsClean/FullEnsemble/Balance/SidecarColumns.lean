import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.ConsumerFacts
import ZiskFv.AirsClean.BinaryAdd.Interface
import ZiskFv.AirsClean.BinaryExtension.ConsumerFacts
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.SidecarColumns
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

/-- Compatibility re-exports for balance-layer callers. The implementations
live with the Mem component so canonical fixed-column source constructors can
be used without importing the full-ensemble layer. -/
abbrev memSidecarGsumOfProverData (data : ProverData FGL) : Nat -> FGL :=
  ZiskFv.AirsClean.Mem.memSidecarGsumOfProverData data

abbrev memSidecarIm0OfProverData (data : ProverData FGL) : Nat -> FGL :=
  ZiskFv.AirsClean.Mem.memSidecarIm0OfProverData data

abbrev memSidecarIm1OfProverData (data : ProverData FGL) : Nat -> FGL :=
  ZiskFv.AirsClean.Mem.memSidecarIm1OfProverData data

abbrev memSegmentColumnsOfProverData (data : ProverData FGL) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  ZiskFv.AirsClean.Mem.memSegmentColumnsOfProverData data

abbrev memPermutationColumnsOfProverData (data : ProverData FGL) :
    ZiskFv.Airs.Mem.PermutationColumns FGL :=
  ZiskFv.AirsClean.Mem.memPermutationColumnsOfProverData data

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
