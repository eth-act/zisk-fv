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
import ZiskFv.AirsClean.FullEnsemble.Balance.SidecarColumns

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- Any active replay entry from a generated Mem table row is either at the
    same byte pointer as the selected primary row or byte-disjoint from it.

    This packages the `mem.pil:109` address range (`addrColumns`) with the
    provider pointer conversion `addr * 8`. -/
theorem activeMemReplayEntry_same_ptr_or_byteDisjoint_of_rowAt
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (selectedIdx otherIdx : Fin table.table.length)
    {entry : Interaction.MemoryBusEntry FGL}
    (h_entry :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val)) :
    entry.ptr =
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val)).ptr
      ∨ ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val))
        entry := by
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry with
    h_entry_primary | h_entry_dual
  · by_cases h_addr :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr =
        (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr
    · left
      have h_addr_mem : mem.addr otherIdx.val = mem.addr selectedIdx.val := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr
      simp [h_entry_primary, memPrimaryReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.memBusMessage, h_addr_mem]
    · right
      have h_selected_range :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns selectedIdx
      have h_other_range :
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
      have h_addr_ne :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr ≠
            (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
        intro h_eq
        exact h_addr h_eq.symm
      simpa [h_entry_primary] using
        memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
          h_selected_range h_other_range h_addr_ne
  · by_cases h_addr :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr =
        (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr
    · left
      have h_addr_mem : mem.addr otherIdx.val = mem.addr selectedIdx.val := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr
      simp [h_entry_dual, memDualReadReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.memBusDualMessage, h_addr_mem]
    · right
      have h_selected_range :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns selectedIdx
      have h_other_range :
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
        simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
      have h_addr_ne :
          (ZiskFv.AirsClean.Mem.rowAt mem selectedIdx.val).addr ≠
            (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
        intro h_eq
        exact h_addr h_eq.symm
      simpa [h_entry_dual] using
        memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
          h_selected_range h_other_range h_addr_ne

/-- The indexed table bridge projects the generated row range required by
    the Mem trace spec. -/
theorem generatedMemRows_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount) :
    ZiskFv.AirsClean.Mem.GeneratedMemRows mem segment permutation rowCount := by
  intro row h_row
  have h_len : row < table.table.length := by
    rw [h_bridge.length_eq]
    exact h_row
  exact h_bridge.generatedAt ⟨row, h_len⟩

/-- Full-ensemble witness obligation for the concrete mutable Mem table:
    one witness table must be the dual-aware Mem component and must satisfy the
    indexed `Valid_Mem` bridge above. -/
def FullWitnessMemTableGeneratedRowsBridge
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop :=
  ∃ table ∈ witness.allTables,
    MemTableGeneratedRowsBridge table mem segment permutation rowCount

/-- Full-ensemble witness obligation for constructing circuit-side accepted
    memory replay evidence from the concrete mutable Mem table.

    This is intentionally a compact extractor-facing bridge rather than a
    replay-soundness field. It exposes every remaining concrete fact needed by
    `acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts`:
    the table selected from the full witness, the active replay row projection,
    generated Mem row constraints, row/segment range checks, fixed-column shape,
    and nonempty segment evidence. -/
structure FullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Type 2 where
  table : Table FGL
  table_mem : table ∈ witness.allTables
  mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  rowCount : ℕ
  rows_eq : rows = activeMemReplayRowsOfTable table
  generatedRows : MemTableGeneratedRowsBridge table mem segment permutation rowCount
  rowRanges : MemTableGeneratedRangeFacts table mem
  segmentRanges : MemSegmentGeneratedRangeFacts segment
  fixedColumns : MemTableGeneratedFixedColumnFacts table segment
  nonempty : 0 < table.table.length

/-- Construct the full-witness replay bridge from the concrete Mem table
    projection and the remaining generated/range/fixed-column facts.

    This is the intended extractor-facing constructor: table membership,
    component identity, row projection, row count, and accepted-row projection
    are no longer independent bridge fields. -/
def fullWitnessMemReplayBridge_of_memTable
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          segment permutation (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts segment)
    (h_fixedColumns : MemTableGeneratedFixedColumnFacts table segment)
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  { table := table
    table_mem := h_table
    mem := memOfTable table gsum im0 im1
    segment := segment
    permutation := permutation
    rowCount := table.table.length
    rows_eq := rfl
    generatedRows :=
      memTableGeneratedRowsBridge_of_memOfTable h_component h_generatedAt
    rowRanges := h_rowRanges
    segmentRanges := h_segmentRanges
    fixedColumns := h_fixedColumns
    nonempty := h_nonempty }

/-- Construct the full-witness replay bridge using the deterministic
    `SEGMENT_L1` fixed-column shape. The remaining caller-facing inputs are the
    generated every-row facts, row/segment range facts, and nonempty table
    evidence. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          (segmentWithFixedL1 segment) permutation
          (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment))
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable
    h_table
    h_component
    h_generatedAt
    h_rowRanges
    h_segmentRanges
    (memTableGeneratedFixedColumnFacts_of_segmentWithFixedL1 table segment)
    h_nonempty

/-- Construct the full-witness replay bridge from the compact generated AIR
    fact package, using the deterministic `SEGMENT_L1` shape. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1
    h_table
    h_component
    h_air.generatedAt
    h_air.rowRanges
    h_air.segmentRanges
    h_nonempty

/-- Construct the full-witness replay bridge from the typed Mem AIR source
    package. This is the Lean-facing target for generated/extractor output:
    callers supply the concrete table membership/component facts plus one
    `MemTableGeneratedAirSource`, not loose stage-2/source columns. -/
def fullWitnessMemReplayBridge_of_memAirSource
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (source : MemTableGeneratedAirSource table)
    (h_nonempty : 0 < table.table.length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts
    (segment := source.segment) (permutation := source.permutation)
    (gsum := source.gsum) (im0 := source.im0) (im1 := source.im1)
    h_table
    h_component
    source.facts
    h_nonempty

/-- Variant of `fullWitnessMemReplayBridge_of_memTable_fixedL1` that derives
    concrete-table nonemptiness from the active replay projection. This is the
    shape used when a selected-load timeline split is already available. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          (segmentWithFixedL1 segment) permutation
          (memOfTable table gsum im0 im1) idx.val)
    (h_rowRanges :
      MemTableGeneratedRangeFacts table (memOfTable table gsum im0 im1))
    (h_segmentRanges : MemSegmentGeneratedRangeFacts (segmentWithFixedL1 segment))
    (h_activeRows : 0 < (activeMemReplayRowsOfTable table).length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1
    h_table
    h_component
    h_generatedAt
    h_rowRanges
    h_segmentRanges
    (table_nonempty_of_activeMemReplayRowsOfTable_nonempty h_activeRows)

/-- Active-row variant of
    `fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts`: the table
    nonemptiness needed by accepted replay is derived from the accepted active
    row projection. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows_airFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_activeRows : 0 < (activeMemReplayRowsOfTable table).length) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts
    h_table
    h_component
    h_air
    (table_nonempty_of_activeMemReplayRowsOfTable_nonempty h_activeRows)

/-- Trace-split variant of
    `fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows_airFacts`.
    The selected-entry split proves the active Mem replay projection is
    nonempty, so callers only supply the generated AIR facts and residual
    timeline split. -/
def fullWitnessMemReplayBridge_of_memTable_fixedL1_traceSplit_airFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation)
    (h_traceSplit :
      activeMemReplayRowsOfTable table = priorRows ++ entry :: laterRows) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memTable_fixedL1_activeRows_airFacts
    h_table
    h_component
    h_air
    (activeMemReplayRowsOfTable_nonempty_of_split h_traceSplit)

/-- Trace-split variant of `fullWitnessMemReplayBridge_of_memAirSource`.
    The source object supplies the generated AIR facts, and the selected-entry
    split supplies table nonemptiness. -/
def fullWitnessMemReplayBridge_of_memAirSource_traceSplit
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (source : MemTableGeneratedAirSource table)
    (h_traceSplit :
      activeMemReplayRowsOfTable table = priorRows ++ entry :: laterRows) :
    FullWitnessMemReplayBridge witness (activeMemReplayRowsOfTable table) :=
  fullWitnessMemReplayBridge_of_memAirSource
    h_table
    h_component
    source
    (table_nonempty_of_activeMemReplayRowsOfTable_nonempty
      (activeMemReplayRowsOfTable_nonempty_of_split h_traceSplit))

/-- Full-witness Mem AIR source for one mutable Mem table.

    This is the generated/full-ensemble source object: it identifies the
    witness-selected mutable Mem table and carries the `MemTableGeneratedAirSource`
    that derives the replay bridge. -/
structure FullWitnessMemAirSource
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 2 where
  table : Table FGL
  table_mem : table ∈ witness.allTables
  component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
  source : MemTableGeneratedAirSource table

namespace FullWitnessMemAirSource

@[reducible]
def rows
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (source : FullWitnessMemAirSource witness) :
    List (Interaction.MemoryBusEntry FGL) :=
  activeMemReplayRowsOfTable source.table

@[reducible]
def replayBridgeOfTraceSplit
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {entry : Interaction.MemoryBusEntry FGL}
    {priorRows laterRows : List (Interaction.MemoryBusEntry FGL)}
    (source : FullWitnessMemAirSource witness)
    (h_traceSplit : source.rows = priorRows ++ entry :: laterRows) :
    FullWitnessMemReplayBridge witness source.rows :=
  fullWitnessMemReplayBridge_of_memAirSource_traceSplit
    source.table_mem
    source.component
    source.source
    h_traceSplit

end FullWitnessMemAirSource

/-- Build the full-witness Mem AIR source from concrete assertion and lookup
    witnesses for the witness-selected mutable Mem table. -/
def fullWitnessMemAirSource_of_witnessFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
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
    FullWitnessMemAirSource witness where
  table := table
  table_mem := h_table
  component := h_component
  source :=
    memTableGeneratedAirSource_of_witnessFacts
      table segment permutation gsum im0 im1
      h_constraints
      h_rowRanges
      h_segmentRanges

/-- Build the full-witness Mem AIR source from raw generated facts for the
    witness-selected mutable Mem table. -/
def fullWitnessMemAirSource_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL}
    (h_table : table ∈ witness.allTables)
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (gsum im0 im1 : ℕ → FGL)
    (h_raw :
      MemTableGeneratedRawSourceFacts
        table (memOfTable table gsum im0 im1)
        (segmentWithFixedL1 segment) permutation) :
    FullWitnessMemAirSource witness :=
  fullWitnessMemAirSource_of_witnessFacts
    h_table
    h_component
    segment
    permutation
    gsum
    im0
    im1
    (memTableGeneratedConstraintAssertionFacts_of_constraintFacts h_raw.constraints)
    (memTableGeneratedRangeLookupFacts_of_rangeFacts h_raw.rowRanges)
    (memSegmentGeneratedRangeLookupFacts_of_rangeFacts h_raw.segmentRanges)

/-- Generated/full-ensemble Mem AIR source facts for every mutable Mem table in
    one full witness. The table membership and component identity are supplied
    by the full witness; this callback supplies only the source columns and the
    concrete assertion/lookup witnesses. -/
def FullWitnessMemAirSourceFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        Σ segment : ZiskFv.Airs.Mem.SegmentColumns FGL,
        Σ permutation : ZiskFv.Airs.Mem.PermutationColumns FGL,
        Σ gsum : ℕ → FGL,
        Σ im0 : ℕ → FGL,
        Σ im1 : ℕ → FGL,
          MemTableGeneratedConstraintAssertionFacts
            table (memOfTable table gsum im0 im1)
            (segmentWithFixedL1 segment) permutation
          × MemTableGeneratedRangeLookupFacts
            table (memOfTable table gsum im0 im1)
          × MemSegmentGeneratedRangeLookupFacts (segmentWithFixedL1 segment)

/-- Raw generated/full-ensemble Mem AIR source facts for every mutable Mem
    table in one full witness.

    This is the shape a generated Lean module may prove first when it derives
    raw split constraints and raw range facts directly from pilout/PIL source.
    `fullWitnessMemAirSourceFacts_of_rawFacts` packages it into the
    witness-aware callback consumed by `exists_fullWitnessMemAirSource_of_facts`. -/
def FullWitnessMemAirSourceRawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        Σ segment : ZiskFv.Airs.Mem.SegmentColumns FGL,
        Σ permutation : ZiskFv.Airs.Mem.PermutationColumns FGL,
        Σ gsum : ℕ → FGL,
        Σ im0 : ℕ → FGL,
        Σ im1 : ℕ → FGL,
          MemTableGeneratedRawSourceFacts
            table (memOfTable table gsum im0 im1)
            (segmentWithFixedL1 segment) permutation

/-- Generated/full-ensemble raw Mem source sidecars for every mutable Mem table
    in one full witness.

    This is a structured generated-code target for the current sidecar route:
    the full witness supplies table membership and component identity, while the
    sidecar supplies the concrete stage-2 columns and raw split facts for that
    table. -/
def FullWitnessMemAirSourceRawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        MemTableGeneratedRawSourceSidecar table

/-- Generated/full-ensemble raw Mem facts whose source columns are read from
    the shared `witness.data` prover-data map.

    `EnsembleWitness.same_data` already requires every table in the witness to
    share this map. This callback is therefore the concrete generated target
    for the sidecar route: generated code proves raw Mem facts for the named
    ProverData keys, and Lean packages those facts into the stored sidecar
    boundary. -/
def FullWitnessMemAirSourceProverDataFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        MemTableGeneratedRawSourceFacts
          table
          (memOfTable table
            (memSidecarGsumOfProverData witness.data)
            (memSidecarIm0OfProverData witness.data)
            (memSidecarIm1OfProverData witness.data))
          (segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data))
          (memPermutationColumnsOfProverData witness.data)

/-- Generated/full-ensemble Mem assertion and lookup witnesses whose source
    columns are read from the shared `witness.data` prover-data map. -/
def FullWitnessMemAirSourceProverDataWitnessFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) : Type 1 :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        MemTableGeneratedConstraintAssertionFacts
          table
          (memOfTable table
            (memSidecarGsumOfProverData witness.data)
            (memSidecarIm0OfProverData witness.data)
            (memSidecarIm1OfProverData witness.data))
          (segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data))
          (memPermutationColumnsOfProverData witness.data)
        × MemTableGeneratedRangeLookupFacts
          table
          (memOfTable table
            (memSidecarGsumOfProverData witness.data)
            (memSidecarIm0OfProverData witness.data)
            (memSidecarIm1OfProverData witness.data))
        × MemSegmentGeneratedRangeLookupFacts
          (segmentWithFixedL1 (memSegmentColumnsOfProverData witness.data))

/-- Project ProverData-backed Clean assertion/lookup witnesses to raw generated
    Mem source facts. -/
def fullWitnessMemAirSourceProverDataFacts_of_witnessFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness) :
    FullWitnessMemAirSourceProverDataFacts witness := by
  intro table h_table h_component
  rcases h_witnessFacts table h_table h_component with
    ⟨h_constraints, h_rowRanges, h_segmentRanges⟩
  exact
    memTableGeneratedRawSourceFacts_of_witnessFacts
      h_constraints
      h_rowRanges
      h_segmentRanges

/-- Build ProverData-backed Clean assertion/lookup witnesses from raw generated
    Mem facts over the same `witness.data` sidecar columns.

    This is the generated-artifact adapter for modules that prove the raw
    pilout/PIL propositions first: Lean repackages those propositions as the
    assertion and lookup witnesses required by
    `FullWitnessMemAirSourceProverDataWitnessFacts`. -/
def fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_rawFacts : FullWitnessMemAirSourceProverDataFacts witness) :
    FullWitnessMemAirSourceProverDataWitnessFacts witness := by
  intro table h_table h_component
  let h_raw := h_rawFacts table h_table h_component
  exact
    ⟨ memTableGeneratedConstraintAssertionFacts_of_constraintFacts h_raw.constraints,
      memTableGeneratedRangeLookupFacts_of_rangeFacts h_raw.rowRanges,
      memSegmentGeneratedRangeLookupFacts_of_rangeFacts h_raw.segmentRanges ⟩

/-- Package generated raw Mem facts over the named `witness.data` sidecar keys
    into the stored full-witness sidecar callback. -/
def fullWitnessMemAirSourceRawSidecars_of_proverData
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_facts : FullWitnessMemAirSourceProverDataFacts witness) :
    FullWitnessMemAirSourceRawSidecars witness := by
  intro table h_table h_component
  exact
    memTableGeneratedRawSourceSidecar_of_proverData
      table
      witness.data
      (h_facts table h_table h_component)

/-- Package ProverData-backed Clean assertion/lookup witnesses into the stored
    full-witness sidecar callback. -/
def fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_witnessFacts : FullWitnessMemAirSourceProverDataWitnessFacts witness) :
    FullWitnessMemAirSourceRawSidecars witness :=
  fullWitnessMemAirSourceRawSidecars_of_proverData
    (fullWitnessMemAirSourceProverDataFacts_of_witnessFacts h_witnessFacts)

/-- Package generated raw Mem source sidecars into the existing raw full-witness
    callback. -/
def fullWitnessMemAirSourceRawFacts_of_sidecars
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    FullWitnessMemAirSourceRawFacts witness := by
  intro table h_table h_component
  let sidecar := h_sidecars table h_table h_component
  exact
    ⟨ sidecar.segment, sidecar.permutation, sidecar.gsum, sidecar.im0, sidecar.im1,
      sidecar.facts ⟩

/-- Package raw generated/full-ensemble Mem facts into sidecar form.

    This is a compatibility adapter for callers that can still prove the raw
    sigma callback directly. The full-witness timeline boundary stores
    sidecars, so generated artifacts should prefer
    `FullWitnessMemAirSourceRawSidecars` when possible. -/
def fullWitnessMemAirSourceRawSidecars_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    FullWitnessMemAirSourceRawSidecars witness := by
  intro table h_table h_component
  rcases h_raw table h_table h_component with
    ⟨segment, permutation, gsum, im0, im1, h_rawFacts⟩
  exact
    { segment := segment
      permutation := permutation
      gsum := gsum
      im0 := im0
      im1 := im1
      facts := h_rawFacts }

/-- Package raw generated/full-ensemble Mem facts into the witness-aware source
    callback. -/
def fullWitnessMemAirSourceFacts_of_rawFacts
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    FullWitnessMemAirSourceFacts witness := by
  intro table h_table h_component
  rcases h_raw table h_table h_component with
    ⟨segment, permutation, gsum, im0, im1, h_rawFacts⟩
  exact
    ⟨ segment, permutation, gsum, im0, im1,
      memTableGeneratedConstraintAssertionFacts_of_constraintFacts h_rawFacts.constraints,
      memTableGeneratedRangeLookupFacts_of_rangeFacts h_rawFacts.rowRanges,
      memSegmentGeneratedRangeLookupFacts_of_rangeFacts h_rawFacts.segmentRanges ⟩

/-- Select the concrete mutable Mem table from a full witness and build its
    Mem AIR source from the generated/full-ensemble source facts. -/
theorem exists_fullWitnessMemAirSource_of_facts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_facts : FullWitnessMemAirSourceFacts witness) :
    Nonempty (FullWitnessMemAirSource witness) := by
  rcases exists_mem_table_of_fullRv64im_witness witness with
    ⟨table, h_table, h_component⟩
  rcases h_facts table h_table h_component with
    ⟨segment, permutation, gsum, im0, im1, h_constraints, h_rowRanges, h_segmentRanges⟩
  exact ⟨fullWitnessMemAirSource_of_witnessFacts
    h_table h_component segment permutation gsum im0 im1
    h_constraints h_rowRanges h_segmentRanges⟩

/-- Select the concrete mutable Mem table from a full witness and build its
    Mem AIR source directly from raw generated/full-ensemble source facts. -/
theorem exists_fullWitnessMemAirSource_of_rawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    Nonempty (FullWitnessMemAirSource witness) :=
  exists_fullWitnessMemAirSource_of_facts
    witness
    (fullWitnessMemAirSourceFacts_of_rawFacts h_raw)

/-- Select the concrete mutable Mem table from sidecar-form raw source facts. -/
theorem exists_fullWitnessMemAirSource_of_rawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    Nonempty (FullWitnessMemAirSource witness) :=
  exists_fullWitnessMemAirSource_of_rawFacts
    witness
    (fullWitnessMemAirSourceRawFacts_of_sidecars h_sidecars)

/-- A named Mem AIR source selected from raw full-witness facts.

    This is only a choice of the concrete mutable Mem table already proved to
    exist in the full witness. Residual timeline facts that use this source
    should refer to this name so the selection is explicit. -/
noncomputable def fullWitnessMemAirSourceOfRawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_raw : FullWitnessMemAirSourceRawFacts witness) :
    FullWitnessMemAirSource witness :=
  Classical.choice (exists_fullWitnessMemAirSource_of_rawFacts witness h_raw)

/-- A named Mem AIR source selected from sidecar-form raw full-witness facts. -/
noncomputable def fullWitnessMemAirSourceOfRawSidecars
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    FullWitnessMemAirSource witness :=
  Classical.choice (exists_fullWitnessMemAirSource_of_rawSidecars witness h_sidecars)

/-- The sidecar-selected source is exactly the raw-facts selected source after
    applying the sidecar-to-raw adapter. -/
@[simp]
theorem fullWitnessMemAirSourceOfRawSidecars_eq_rawFacts
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_sidecars : FullWitnessMemAirSourceRawSidecars witness) :
    fullWitnessMemAirSourceOfRawSidecars witness h_sidecars =
      fullWitnessMemAirSourceOfRawFacts witness
        (fullWitnessMemAirSourceRawFacts_of_sidecars h_sidecars) := by
  rfl

/-- The compact full-witness replay bridge includes the older generated-row
    bridge obligation. -/
theorem fullWitnessMemTableGeneratedRowsBridge_of_fullWitnessMemReplayBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_bridge : FullWitnessMemReplayBridge witness rows) :
    FullWitnessMemTableGeneratedRowsBridge witness
      h_bridge.mem h_bridge.segment h_bridge.permutation h_bridge.rowCount :=
  ⟨h_bridge.table, h_bridge.table_mem, h_bridge.generatedRows⟩

/-- The full-witness bridge projects the generated row range required by the
    Mem trace spec. -/
theorem generatedMemRows_of_fullWitnessMemTableGeneratedRowsBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge :
      FullWitnessMemTableGeneratedRowsBridge
        witness mem segment permutation rowCount) :
    ZiskFv.AirsClean.Mem.GeneratedMemRows mem segment permutation rowCount := by
  rcases h_bridge with ⟨table, _h_table, h_table_bridge⟩
  exact generatedMemRows_of_memTableGeneratedRowsBridge h_table_bridge

/-- Project the generated Mem row fact at one concrete Clean table position. -/
theorem generated_every_row_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val :=
  h_bridge.generatedAt idx

/-- Project the local Clean bridge constraints at one concrete table
    position, via the generated Mem row surface. -/
theorem constraints_at_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.constraints_at mem idx.val :=
  ZiskFv.AirsClean.Mem.constraints_at_of_generated_every_row
    mem segment permutation idx.val (h_bridge.generatedAt idx)

/-- The indexed table bridge projects the Clean Mem row `Spec` at one
    `Valid_Mem` row. -/
theorem rowAt_spec_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.Spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) := by
  have h_constraints :=
    constraints_at_of_memTableGeneratedRowsBridge h_bridge idx
  simpa [ZiskFv.AirsClean.Mem.Spec, ZiskFv.AirsClean.Mem.constraints_at,
    ZiskFv.AirsClean.Mem.rowAt] using h_constraints

/-- The indexed table bridge projects the Clean Mem row `Spec` for the
    concrete evaluated table row at a list position. -/
theorem tableRow_spec_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.Spec
      (eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rw [h_bridge.rowAt_eq idx]
  exact h_spec

/-- The indexed table bridge supplies generated row specs for every concrete
    table row, in the membership form consumed by table-level `flatMap`
    inductions. -/
theorem tableRow_specs_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount) :
    ∀ providerRow, providerRow ∈ table.table →
      ZiskFv.AirsClean.Mem.Spec
        (eval (table.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
  intro providerRow h_mem
  rcases List.mem_iff_get.mp h_mem with ⟨idx, h_get⟩
  rw [← h_get]
  exact tableRow_spec_of_memTableGeneratedRowsBridge h_bridge idx

/-- A bridged generated Mem table position has a boolean current-row write
    flag at the Nat-value level. -/
theorem wr_val_lt_two_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    (mem.wr idx.val).val < 2 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_wr_zero | h_wr_one
  · have h_wr_zero_mem : mem.wr idx.val = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero
    rw [h_wr_zero_mem]
    norm_num
  · have h_wr_one_mem : mem.wr idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_one
    rw [h_wr_one_mem]
    norm_num

/-- A generated Mem table row with inactive primary selector cannot be a
    primary write, because `mem.pil` has the `wr * (1 - sel) = 0` constraint. -/
theorem wr_eq_zero_of_sel_zero_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_sel_zero : mem.sel idx.val = 0) :
    mem.wr idx.val = 0 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_wr_zero | h_wr_one
  · simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero
  · have h_sel_one :=
      ZiskFv.AirsClean.Mem.sel_of_wr_one_of_spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec h_wr_one
    have h_sel_one_mem : mem.sel idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_sel_one
    rw [h_sel_zero] at h_sel_one_mem
    norm_num at h_sel_one_mem

/-- The indexed table bridge lifts the generated non-boundary same-address
    address-carry constraint to a concrete Mem table position. -/
theorem addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.addr idx.val = mem.addr (idx.val - 1) := by
  exact
    ZiskFv.Airs.Mem.addr_eq_previous_of_same_addr_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary

/-- On a bridged concrete Mem table row, the Clean row-spec identity
    `read_same_addr = (1 - addr_changes) * (1 - wr)` turns a read at the same
    address into the generated `read_same_addr = 1` witness. -/
theorem read_same_addr_eq_one_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0) :
    mem.read_same_addr idx.val = 1 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_read_same_addr :=
    ZiskFv.AirsClean.Mem.read_same_addr_eq_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
  simpa [ZiskFv.AirsClean.Mem.rowAt, h_same_addr, h_read] using h_read_same_addr

/-- The indexed table bridge lifts the generated non-boundary same-address read
    value-carry constraints to a concrete Mem table position. -/
theorem values_eq_previous_of_read_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_read_same_addr : mem.read_same_addr idx.val = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.value_0 idx.val = mem.value_0 (idx.val - 1)
      ∧ mem.value_1 idx.val = mem.value_1 (idx.val - 1) := by
  exact
    ZiskFv.Airs.Mem.values_eq_previous_of_read_same_addr_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_read_same_addr h_not_boundary

/-- Same-address reads at non-boundary bridged Mem table rows carry both value
    chunks from the previous row. This is the table-level form needed by the
    per-address prefix-read proof. -/
theorem values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.value_0 idx.val = mem.value_0 (idx.val - 1)
      ∧ mem.value_1 idx.val = mem.value_1 (idx.val - 1) := by
  exact values_eq_previous_of_read_same_addr_memTableGeneratedRowsBridge
    h_bridge idx
    (read_same_addr_eq_one_of_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read)
    h_not_boundary

/-- A bridged non-boundary same-address read is byte-for-byte justified by
    replaying the previous primary row when that previous row is a write.

    This is the adjacent write→read replay step behind the per-address
    `MemoryBusRowsPrefixReadSound` induction. -/
theorem readEventReplayAgreement_after_previous_primary_write_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_write : mem.wr (idx.val - 1) = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_addr :=
    addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_not_boundary
  have h_values :=
    values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read h_not_boundary
  let writeEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    dsimp [readEntry, writeEntry]
    simp [h_addr]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry initialMemory writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      initialMemory h_ptr h_value_0 h_value_1
  simpa [writeEntry, readEntry, ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
    ZiskFv.AirsClean.Mem.rowAt, h_previous_write,
    ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent_storeEventOfEntry] using h_replay

/-- A bridged non-boundary same-address read is byte-for-byte justified by a
    previous primary read that was already replay-sound, because the previous
    read leaves replay memory unchanged and the generated value-carry
    constraints identify the current read's bytes with the previous row. -/
theorem readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_read : mem.wr (idx.val - 1) = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_agreement :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_addr :=
    addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_not_boundary
  have h_values :=
    values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read h_not_boundary
  let sourceEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))
  let targetEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_ptr : targetEntry.ptr = sourceEntry.ptr := by
    dsimp [targetEntry, sourceEntry]
    simp [h_addr]
  have h_value_0 : targetEntry.value_0 = sourceEntry.value_0 := by
    dsimp [targetEntry, sourceEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : targetEntry.value_1 = sourceEntry.value_1 := by
    dsimp [targetEntry, sourceEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_carried :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry targetEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_entry_same
      (by simpa [sourceEntry] using h_previous_agreement)
      h_ptr h_value_0 h_value_1
  have h_source_as : sourceEntry.as = (2 : FGL) := by
    simp [sourceEntry]
  have h_source_read : sourceEntry.multiplicity = (-1 : FGL) := by
    simp [sourceEntry, h_previous_read]
  have h_source_replay :=
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
      initialMemory sourceEntry h_source_as h_source_read
  rw [h_source_replay]
  simpa [targetEntry]

/-- A selected previous Mem row justifies a non-boundary same-address current
    read after replaying that previous row's active chunk.

    If the previous primary emission was a write, the write sets the bytes
    carried by the current read. If it was a read, the caller supplies the
    previous read agreement. A selected previous dual emission is replay-neutral
    because dual Mem emissions are pinned reads. -/
theorem readEventReplayAgreement_after_previous_selected_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_sel : mem.sel (idx.val - 1) = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
        (activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  let previousRow := ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1)
  let previousPrimaryEntry := memPrimaryReplayEntryOfRow previousRow
  let previousDualEntry := memDualReadReplayEntryOfRow previousRow
  have h_previous_spec :
      ZiskFv.AirsClean.Mem.Spec previousRow := by
    simpa [previousRow, previousIdx] using
      rowAt_spec_of_memTableGeneratedRowsBridge h_bridge previousIdx
  have h_previous_sel_row : previousRow.sel = 1 := by
    simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_sel
  have h_after_primary :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
          previousPrimaryEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
    rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec previousRow h_previous_spec with
      h_previous_wr_zero_row | h_previous_wr_one_row
    · have h_previous_wr_zero : mem.wr (idx.val - 1) = 0 := by
        simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_wr_zero_row
      simpa [previousPrimaryEntry, previousRow] using
        readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge
          initialMemory h_bridge idx h_same_addr h_read h_previous_wr_zero
          h_not_boundary (h_previous_read_agreement h_previous_wr_zero)
    · have h_previous_wr_one : mem.wr (idx.val - 1) = 1 := by
        simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_wr_one_row
      simpa [previousPrimaryEntry, previousRow] using
        readEventReplayAgreement_after_previous_primary_write_memTableGeneratedRowsBridge
          initialMemory h_bridge idx h_same_addr h_read h_previous_wr_one
          h_not_boundary
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec previousRow h_previous_spec with
    h_previous_sel_dual_zero | h_previous_sel_dual_one
  · have h_previous_sel_dual_ne : previousRow.sel_dual ≠ 1 := by
      simp [h_previous_sel_dual_zero]
    rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
      h_previous_sel_row h_previous_sel_dual_ne]
    simpa [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows,
      previousPrimaryEntry, previousRow] using h_after_primary
  · rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
      h_previous_sel_row h_previous_sel_dual_one]
    have h_dual_as : previousDualEntry.as = (2 : FGL) := by
      simp [previousDualEntry]
    have h_dual_read : previousDualEntry.multiplicity = (-1 : FGL) := by
      simp [previousDualEntry]
    have h_dual_replay :=
      ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
          previousPrimaryEntry)
        previousDualEntry h_dual_as h_dual_read
    rw [show
      ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
          [previousPrimaryEntry, previousDualEntry] =
        ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
            previousPrimaryEntry)
          previousDualEntry by
        rfl]
    rw [h_dual_replay]
    simpa [previousPrimaryEntry, previousRow] using h_after_primary

/-- An inactive previous Mem row carries a non-boundary same-address current
    read without changing the replay memory.

    The generated row spec forces an inactive row to have no active primary or
    dual replay emissions; if its primary polarity is read, the existing
    previous-primary-read carry lemma transports the supplied previous-row
    agreement to the current row. -/
theorem readEventReplayAgreement_after_previous_inactive_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_inactive : mem.sel (idx.val - 1) = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_agreement :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
        (activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  let previousRow := ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1)
  let previousPrimaryEntry := memPrimaryReplayEntryOfRow previousRow
  have h_previous_spec :
      ZiskFv.AirsClean.Mem.Spec previousRow := by
    simpa [previousRow, previousIdx] using
      rowAt_spec_of_memTableGeneratedRowsBridge h_bridge previousIdx
  have h_previous_sel_zero_row : previousRow.sel = 0 := by
    simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_inactive
  have h_previous_wr_zero : mem.wr (idx.val - 1) = 0 := by
    rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec previousRow h_previous_spec with
      h_wr_zero_row | h_wr_one_row
    · simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero_row
    · have h_sel_one :=
        ZiskFv.AirsClean.Mem.sel_of_wr_one_of_spec
          previousRow h_previous_spec h_wr_one_row
      rw [h_previous_sel_zero_row] at h_sel_one
      norm_num at h_sel_one
  have h_current_after_previous_primary :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
          previousPrimaryEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow
            (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
    simpa [previousPrimaryEntry, previousRow] using
      readEventReplayAgreement_after_previous_primary_read_memTableGeneratedRowsBridge
        initialMemory h_bridge idx h_same_addr h_read h_previous_wr_zero
        h_not_boundary h_previous_agreement
  have h_previous_primary_as : previousPrimaryEntry.as = (2 : FGL) := by
    simp [previousPrimaryEntry]
  have h_previous_primary_read :
      previousPrimaryEntry.multiplicity = (-1 : FGL) := by
    simp [previousPrimaryEntry, previousRow, h_previous_wr_zero]
  have h_previous_primary_replay :=
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
      initialMemory previousPrimaryEntry h_previous_primary_as
      h_previous_primary_read
  rw [h_previous_primary_replay] at h_current_after_previous_primary
  have h_previous_sel_ne : previousRow.sel ≠ 1 := by
    simp [h_previous_sel_zero_row]
  have h_previous_sel_dual_ne : previousRow.sel_dual ≠ 1 := by
    intro h_sel_dual_one
    have h_sel_one :=
      ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec
        previousRow h_previous_spec h_sel_dual_one
    rw [h_previous_sel_zero_row] at h_sel_one
    norm_num at h_sel_one
  rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
    h_previous_sel_ne h_previous_sel_dual_ne]
  simpa [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows] using
    h_current_after_previous_primary

/-- One-step same-address carry across the previous table row.

    This packages the selected and inactive predecessor cases. If the previous
    row's primary event is a read, the caller supplies its replay agreement;
    if it is a write, the selected-row lemma uses the write update directly. -/
theorem readEventReplayAgreement_after_previous_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_idx_pos : 0 < idx.val)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory
        (activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  let previousRow := ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1)
  have h_previous_spec :
      ZiskFv.AirsClean.Mem.Spec previousRow := by
    simpa [previousRow, previousIdx] using
      rowAt_spec_of_memTableGeneratedRowsBridge h_bridge previousIdx
  rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec previousRow h_previous_spec with
    h_previous_sel_zero_row | h_previous_sel_one_row
  · have h_previous_sel_zero : mem.sel (idx.val - 1) = 0 := by
      simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_sel_zero_row
    have h_previous_wr_zero : mem.wr (idx.val - 1) = 0 :=
      wr_eq_zero_of_sel_zero_memTableGeneratedRowsBridge
        h_bridge previousIdx (by simpa [previousIdx] using h_previous_sel_zero)
    exact
      readEventReplayAgreement_after_previous_inactive_row_memTableGeneratedRowsBridge
        initialMemory h_bridge idx h_idx_pos h_same_addr h_read
        h_previous_sel_zero h_not_boundary
        (h_previous_read_agreement h_previous_wr_zero)
  · have h_previous_sel_one : mem.sel (idx.val - 1) = 1 := by
      simpa [previousRow, ZiskFv.AirsClean.Mem.rowAt] using h_previous_sel_one_row
    exact
      readEventReplayAgreement_after_previous_selected_row_memTableGeneratedRowsBridge
        initialMemory h_bridge idx h_idx_pos h_same_addr h_read
        h_previous_sel_one h_not_boundary h_previous_read_agreement

/-- Split-shaped same-address predecessor step for table prefixes over an
    arbitrary initial memory.

If the current provider row is immediately after `previousProviderRow` in the
concrete table split, the one-step predecessor lemma composes with the replay
append law to justify the current read against the whole split prefix
`priorPrefix ++ [previousProviderRow]`. -/
theorem readEventReplayAgreement_after_initialMemory_splitPrefix_previous_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (priorPrefix : List (Array FGL))
    (previousProviderRow providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split :
      table.table = priorPrefix ++ previousProviderRow :: providerRow :: laterRows)
    (h_idx_val : idx.val = priorPrefix.length + 1)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
            initialMemory
            (priorPrefix.flatMap fun priorProviderRow =>
              activeMemReplayEntriesOfRow
                (eval (table.environment priorProviderRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        initialMemory
        ((priorPrefix ++ [previousProviderRow]).flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_idx_pos : 0 < idx.val := by omega
  have h_not_boundary := h_fixed.segmentL1_nonfirst idx h_idx_pos
  let previousIdx : Fin table.table.length := ⟨idx.val - 1, by omega⟩
  have h_previous_get : table.table.get previousIdx = previousProviderRow := by
    have h_previous_val : previousIdx.val = priorPrefix.length := by
      simp [previousIdx]
      omega
    have h_previous_get?_prior :
        table.table[priorPrefix.length]? = some previousProviderRow := by
      have h_lookup :=
        congrArg (fun rows : List (Array FGL) => rows[priorPrefix.length]?)
          h_split
      have h_lookup' :
          table.table[priorPrefix.length]? =
            (priorPrefix ++ previousProviderRow :: providerRow :: laterRows)[priorPrefix.length]? := by
        simpa using h_lookup
      rw [h_lookup']
      simp
    have h_previous_get? :
        table.table[previousIdx.val]? = some previousProviderRow := by
      rw [h_previous_val]
      exact h_previous_get?_prior
    have h_get_current :
        table.table[previousIdx.val]? = some (table.table.get previousIdx) := by
      exact List.getElem?_eq_getElem previousIdx.isLt
    rw [h_get_current] at h_previous_get?
    exact Option.some.inj h_previous_get?
  have h_previous_rowAt :
      eval (table.environment previousProviderRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1) := by
    rw [← h_previous_get]
    simpa [previousIdx] using h_bridge.rowAt_eq previousIdx
  have h_step :=
    readEventReplayAgreement_after_previous_row_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        initialMemory
        (priorPrefix.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      h_bridge idx h_idx_pos h_same_addr h_read h_not_boundary
      h_previous_read_agreement
  simpa [List.flatMap_append, h_previous_rowAt,
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows_append] using h_step

/-- Split-shaped same-address predecessor step specialized to the finite
    zero-preloaded Mem-table memory. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_previous_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_fixed : MemTableGeneratedFixedColumnFacts table segment)
    (idx : Fin table.table.length)
    (priorPrefix : List (Array FGL))
    (previousProviderRow providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split :
      table.table = priorPrefix ++ previousProviderRow :: providerRow :: laterRows)
    (h_idx_val : idx.val = priorPrefix.length + 1)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_read_agreement :
      mem.wr (idx.val - 1) = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
          (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
            (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
              (activeMemReplayRowsOfTable table))
            (priorPrefix.flatMap fun priorProviderRow =>
              activeMemReplayEntriesOfRow
                (eval (table.environment priorProviderRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        ((priorPrefix ++ [previousProviderRow]).flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  exact
    readEventReplayAgreement_after_initialMemory_splitPrefix_previous_row_memTableGeneratedRowsBridge
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table))
      h_bridge h_fixed idx priorPrefix previousProviderRow providerRow laterRows
      h_split h_idx_val h_same_addr h_read h_previous_read_agreement

/-- Replaying a primary write from one Mem row justifies the pinned dual read
    emitted by the same row, because the dual message has the same pointer and
    value chunks and appears after the primary emission. -/
theorem readEventReplayAgreement_after_primary_write_dual_read_of_row
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (row : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_write : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memDualReadReplayEntryOfRow row)) := by
  let writeEntry := memPrimaryReplayEntryOfRow row
  let readEntry := memDualReadReplayEntryOfRow row
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    simp [readEntry, writeEntry]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    simp [readEntry, writeEntry]
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    simp [readEntry, writeEntry]
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry initialMemory writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      initialMemory h_ptr h_value_0 h_value_1
  simpa [writeEntry, readEntry, ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage, h_write,
    ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent_storeEventOfEntry] using h_replay

/-- A replay-sound primary read justifies the pinned dual read emitted by the
    same Mem row when the primary event is also a read. The primary read leaves
    replay memory unchanged, and the dual message carries the same pointer and
    value chunks. -/
theorem readEventReplayAgreement_after_primary_read_dual_read_of_row
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (row : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_read : row.wr = 0)
    (h_primary_agreement :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
          (memPrimaryReplayEntryOfRow row))) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memDualReadReplayEntryOfRow row)) := by
  let sourceEntry := memPrimaryReplayEntryOfRow row
  let targetEntry := memDualReadReplayEntryOfRow row
  have h_ptr : targetEntry.ptr = sourceEntry.ptr := by
    simp [targetEntry, sourceEntry]
  have h_value_0 : targetEntry.value_0 = sourceEntry.value_0 := by
    simp [targetEntry, sourceEntry]
  have h_value_1 : targetEntry.value_1 = sourceEntry.value_1 := by
    simp [targetEntry, sourceEntry]
  have h_carried :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry targetEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_entry_same
      (by simpa [sourceEntry] using h_primary_agreement)
      h_ptr h_value_0 h_value_1
  have h_source_as : sourceEntry.as = (2 : FGL) := by
    simp [sourceEntry]
  have h_source_read : sourceEntry.multiplicity = (-1 : FGL) := by
    simp [sourceEntry, h_read]
  have h_source_replay :=
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow_eq_self_of_read
      initialMemory sourceEntry h_source_as h_source_read
  rw [h_source_replay]
  simpa [targetEntry]

/-- An address-change primary read is locally justified by the finite
    zero-preload memory at its pointer. The generated row spec forces both
    value chunks to zero when `addr_changes = 1` and `wr = 0`. -/
theorem readEventReplayAgreement_after_zeroMemoryOfEntry_primary_read_of_addr_change
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_addr_change : row.addr_changes = 1)
    (h_read : row.wr = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfEntry initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow row)) := by
  have h_value_0 :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_0_zero_of_spec
      row h_spec h_addr_change h_read
  have h_value_1 :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_1_zero_of_spec
      row h_spec h_addr_change h_read
  exact
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_zeroMemoryOfEntry
      initialMemory
      (by
        simpa [memPrimaryReplayEntryOfRow,
          ZiskFv.AirsClean.Mem.memBusMessage] using h_value_0)
      (by
        simpa [memPrimaryReplayEntryOfRow,
          ZiskFv.AirsClean.Mem.memBusMessage] using h_value_1)

/-- The indexed table bridge projects the address-change zero-read
    justification to a concrete Mem table row. -/
theorem readEventReplayAgreement_after_zeroMemoryOfEntry_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfEntry initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  exact
    readEventReplayAgreement_after_zeroMemoryOfEntry_primary_read_of_addr_change
      initialMemory h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)

/-- A selected address-change primary read is justified by the finite
    zero-preload memory built from all active Mem table replay rows.

    This is the table-shaped zero-preload fact. It does not yet replay the
    selected row's prior prefix; that follow-on step additionally needs the
    prior-prefix rows to be byte-disjoint from the selected read. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_value_0_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_0_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_1_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_1_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_0 : readEntry.value_0 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_0_row
  have h_value_1 : readEntry.value_1 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_1_row
  have h_row_mem : table.table.get idx ∈ table.table := by
    exact List.mem_iff_get.mpr ⟨idx, rfl⟩
  have h_readEntry_mem : readEntry ∈ activeMemReplayRowsOfTable table := by
    unfold activeMemReplayRowsOfTable
    exact List.mem_flatMap.mpr
      ⟨table.table.get idx, h_row_mem, by
        rw [h_bridge.rowAt_eq idx]
        simp [activeMemReplayEntriesOfRow, readEntry,
          ZiskFv.AirsClean.Mem.rowAt, h_sel]⟩
  have h_same_or_disjoint :
      ∀ entry, entry ∈ activeMemReplayRowsOfTable table →
        entry.ptr = readEntry.ptr
          ∨ ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint readEntry entry := by
    intro entry h_entry
    unfold activeMemReplayRowsOfTable at h_entry
    rcases List.mem_flatMap.mp h_entry with
      ⟨providerRow, h_provider_mem, h_entry_row⟩
    rcases List.mem_iff_get.mp h_provider_mem with ⟨otherIdx, h_get⟩
    have h_entry_rowAt :
        entry ∈ activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
      rw [← h_get] at h_entry_row
      rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
      exact h_entry_row
    simpa [readEntry] using
      activeMemReplayEntry_same_ptr_or_byteDisjoint_of_rowAt
        h_ranges idx otherIdx h_entry_rowAt
  simpa [readEntry] using
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_zeroMemoryOfRows_mem
      h_value_0 h_value_1 h_readEntry_mem h_same_or_disjoint

/-- A read row whose address changes is justified by the whole-table
zero-preload memory when any selected row at the same Mem address contributes a
primary active replay entry.

This same-pointer preload form is needed for inactive same-address predecessor
rows: they may not themselves appear in `activeMemReplayRowsOfTable`, but the
eventual selected row at the same pointer does. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx preloadIdx : Fin table.table.length)
    (h_preload_sel : mem.sel preloadIdx.val = 1)
    (h_addr_eq : mem.addr idx.val = mem.addr preloadIdx.val)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
        (activeMemReplayRowsOfTable table))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  let preloadEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem preloadIdx.val)
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_value_0_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_0_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_1_row :=
    ZiskFv.AirsClean.Mem.read_addr_change_value_1_zero_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_change)
      (by simpa [ZiskFv.AirsClean.Mem.rowAt] using h_read)
  have h_value_0 : readEntry.value_0 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_0_row
  have h_value_1 : readEntry.value_1 = 0 := by
    simpa [readEntry, memPrimaryReplayEntryOfRow,
      ZiskFv.AirsClean.Mem.memBusMessage] using h_value_1_row
  have h_preload_mem : preloadEntry ∈ activeMemReplayRowsOfTable table := by
    have h_row_mem : table.table.get preloadIdx ∈ table.table := by
      exact List.mem_iff_get.mpr ⟨preloadIdx, rfl⟩
    unfold activeMemReplayRowsOfTable
    exact List.mem_flatMap.mpr
      ⟨table.table.get preloadIdx, h_row_mem, by
        rw [h_bridge.rowAt_eq preloadIdx]
        simp [activeMemReplayEntriesOfRow, preloadEntry,
          ZiskFv.AirsClean.Mem.rowAt, h_preload_sel]⟩
  have h_ptr : preloadEntry.ptr = readEntry.ptr := by
    simp [preloadEntry, readEntry, h_addr_eq.symm]
  have h_same_or_disjoint :
      ∀ entry, entry ∈ activeMemReplayRowsOfTable table →
        entry.ptr = readEntry.ptr
          ∨ ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint readEntry entry := by
    intro entry h_entry
    unfold activeMemReplayRowsOfTable at h_entry
    rcases List.mem_flatMap.mp h_entry with
      ⟨providerRow, h_provider_mem, h_entry_row⟩
    rcases List.mem_iff_get.mp h_provider_mem with ⟨otherIdx, h_get⟩
    have h_entry_rowAt :
        entry ∈ activeMemReplayEntriesOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
      rw [← h_get] at h_entry_row
      rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
      exact h_entry_row
    simpa [readEntry] using
      activeMemReplayEntry_same_ptr_or_byteDisjoint_of_rowAt
        h_ranges idx otherIdx h_entry_rowAt
  simpa [readEntry, preloadEntry] using
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_zeroMemoryOfRows_same_ptr_mem
      h_value_0 h_value_1 h_preload_mem h_ptr h_same_or_disjoint

/-- The table-shaped zero-preload fact lifts through any prior active replay
    prefix whose rows are byte-disjoint from the selected address-change read.

    The remaining AIR-ordering work is to prove the `h_prior_disjoint`
    premise for the concrete prefix of an address-sorted Mem table. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_disjoint_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_prior_disjoint :
      ∀ entry,
        entry ∈
            (priorRows.flatMap fun priorProviderRow =>
              activeMemReplayEntriesOfRow
                (eval (table.environment priorProviderRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) →
          ZiskFv.ZiskCircuit.MemTrace.MemoryBusEntryByteDisjoint
            (memPrimaryReplayEntryOfRow
              (ZiskFv.AirsClean.Mem.rowAt mem idx.val))
            entry) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_zero :=
    readEventReplayAgreement_after_zeroMemoryOfRows_memTableGeneratedRowsBridge
      h_bridge h_ranges idx h_sel h_addr_change h_read
  exact
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint
      h_zero h_prior_disjoint

/-- If a table list is split as `priorRows ++ providerRow :: laterRows`, every
    member of `priorRows` has an occurrence at an index before the split point. -/
theorem priorRows_mem_index_lt_of_split
    {α : Type}
    {xs priorRows laterRows : List α}
    {providerRow priorProviderRow : α}
    (h_split : xs = priorRows ++ providerRow :: laterRows)
    (h_prior_mem : priorProviderRow ∈ priorRows) :
    ∃ idx : Fin xs.length,
      xs.get idx = priorProviderRow ∧ idx.val < priorRows.length := by
  subst xs
  rcases List.mem_iff_get.mp h_prior_mem with ⟨priorIdx, h_get_prior⟩
  have h_idx_lt : priorIdx.val < (priorRows ++ providerRow :: laterRows).length := by
    simp [List.length_append]
    omega
  let idx : Fin (priorRows ++ providerRow :: laterRows).length :=
    ⟨priorIdx.val, h_idx_lt⟩
  refine ⟨idx, ?_, ?_⟩
  · simpa [idx] using h_get_prior
  · exact priorIdx.isLt

/-- In a split `xs = priorRows ++ providerRow :: laterRows`, the element at the
split index is `providerRow`. The proof uses `getElem?` to avoid dependent
rewrites through the `Fin` proof term. -/
theorem providerRow_get_eq_of_split
    {α : Type}
    {xs priorRows laterRows : List α}
    {providerRow : α}
    (idx : Fin xs.length)
    (h_split : xs = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length) :
    xs.get idx = providerRow := by
  have h_get_prior : xs[priorRows.length]? = some providerRow := by
    have h_lookup :=
      congrArg (fun rows : List α => rows[priorRows.length]?) h_split
    have h_lookup' :
        xs[priorRows.length]? =
          (priorRows ++ providerRow :: laterRows)[priorRows.length]? := by
      simpa using h_lookup
    rw [h_lookup']
    simp
  have h_get_idx : xs[idx.val]? = some providerRow := by
    rw [h_idx_val]
    exact h_get_prior
  have h_get_current : xs[idx.val]? = some (xs.get idx) := by
    exact List.getElem?_eq_getElem idx.isLt
  rw [h_get_current] at h_get_idx
  exact Option.some.inj h_get_idx

/-- The zero-preload prior-prefix lift only needs the concrete AIR ordering
    proof to rule out equal Mem addresses in the prior prefix.

    This theorem turns that address-separation statement into the byte-range
    disjointness required by the replay core. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_addr_ne_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_prior_addr_ne :
      ∀ priorProviderRow, priorProviderRow ∈ priorRows →
        ∃ otherIdx : Fin table.table.length,
          table.table.get otherIdx = priorProviderRow ∧
            mem.addr otherIdx.val ≠ mem.addr idx.val) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  apply
    readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_disjoint_memTableGeneratedRowsBridge
      h_bridge h_ranges idx priorRows h_sel h_addr_change h_read
  intro entry h_entry
  rcases List.mem_flatMap.mp h_entry with
    ⟨priorProviderRow, h_prior_mem, h_entry_row⟩
  rcases h_prior_addr_ne priorProviderRow h_prior_mem with
    ⟨otherIdx, h_get, h_addr_ne_mem⟩
  have h_entry_rowAt :
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val) := by
    rw [← h_get] at h_entry_row
    rw [h_bridge.rowAt_eq otherIdx] at h_entry_row
    exact h_entry_row
  have h_selected_range :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns idx
  have h_other_range :
      (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr.val < 2 ^ 29 := by
    simpa [ZiskFv.AirsClean.Mem.rowAt] using h_ranges.addrColumns otherIdx
  have h_addr_ne :
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val).addr ≠
        (ZiskFv.AirsClean.Mem.rowAt mem otherIdx.val).addr := by
    intro h_addr_eq
    exact h_addr_ne_mem (by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq.symm)
  rcases activeMemReplayEntriesOfRow_mem_eq_primary_or_dual h_entry_rowAt with
    h_entry_primary | h_entry_dual
  · simpa [h_entry_primary] using
      memoryBusEntryByteDisjoint_primary_primary_of_addr_ne
        h_selected_range h_other_range h_addr_ne
  · simpa [h_entry_dual] using
      memoryBusEntryByteDisjoint_primary_dual_of_addr_ne
        h_selected_range h_other_range h_addr_ne

/-- A split-shaped version of the address-separation zero-preload lift.

    The remaining semantic input is the indexed all-prior address inequality;
    list-prefix bookkeeping is discharged here from the concrete split. -/
theorem readEventReplayAgreement_after_zeroMemoryOfRows_splitPrefix_addr_ne_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (priorRows : List (Array FGL))
    (providerRow : Array FGL)
    (laterRows : List (Array FGL))
    (h_split : table.table = priorRows ++ providerRow :: laterRows)
    (h_idx_val : idx.val = priorRows.length)
    (h_sel : mem.sel idx.val = 1)
    (h_addr_change : mem.addr_changes idx.val = 1)
    (h_read : mem.wr idx.val = 0)
    (h_prior_addr_ne :
      ∀ otherIdx : Fin table.table.length,
        otherIdx.val < idx.val → mem.addr otherIdx.val ≠ mem.addr idx.val) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows
        (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (activeMemReplayRowsOfTable table))
        (priorRows.flatMap fun priorProviderRow =>
          activeMemReplayEntriesOfRow
            (eval (table.environment priorProviderRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  exact
    readEventReplayAgreement_after_zeroMemoryOfRows_priorPrefix_addr_ne_memTableGeneratedRowsBridge
      h_bridge h_ranges idx priorRows h_sel h_addr_change h_read
      (fun priorProviderRow h_prior_mem => by
        rcases priorRows_mem_index_lt_of_split
            (xs := table.table) (priorRows := priorRows)
            (laterRows := laterRows) (providerRow := providerRow)
            h_split h_prior_mem with
          ⟨otherIdx, h_get, h_other_lt_prior_length⟩
        refine ⟨otherIdx, h_get, h_prior_addr_ne otherIdx ?_⟩
        omega)

/-- A generated Mem row's active replay chunk is recursively read/write-sound
    once any selected primary read has already been justified against the
    incoming replay memory.

    The same-row dual read is then discharged from the primary event: writes
    use the row-local write→read replay theorem, and reads use read-no-mutation
    plus equal pointer/value transport. -/
theorem memoryBusRowsReadWriteSound_activeMemReplayEntriesOfRow_of_spec
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_primary_read :
      row.sel = 1 →
      row.wr = 0 →
        ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement initialMemory
          (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
            (memPrimaryReplayEntryOfRow row))) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound
      initialMemory (activeMemReplayEntriesOfRow row) := by
  have h_primary_write_not_read :
      row.wr = 1 →
        ¬(memPrimaryReplayEntryOfRow row).multiplicity = (-1 : FGL) := by
    intro h_wr_one h_mult
    have h_mult_one :
        (memPrimaryReplayEntryOfRow row).multiplicity = (1 : FGL) := by
      simp [h_wr_one]
    have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
      decide
    exact h_one_ne_neg_one (h_mult_one.symm.trans h_mult)
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec row h_spec with
    h_sel_dual_zero | h_sel_dual_one
  · rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec row h_spec with
      h_sel_zero | h_sel_one
    · have h_sel_ne : row.sel ≠ 1 := by
        simp [h_sel_zero]
      have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
        h_sel_ne h_sel_dual_ne]
      simp [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
    · have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
        h_sel_one h_sel_dual_ne]
      simp only [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
      constructor
      · intro _h_as h_mult
        rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec row h_spec with
          h_wr_zero | h_wr_one
        · exact h_primary_read h_sel_one h_wr_zero
        · exact False.elim (h_primary_write_not_read h_wr_one h_mult)
      · simp
  · have h_sel_one :=
      ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec
        row h_spec h_sel_dual_one
    rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
      h_sel_one h_sel_dual_one]
    simp only [ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsReadWriteSound]
    constructor
    · intro _h_as h_mult
      rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec row h_spec with
        h_wr_zero | h_wr_one
      · exact h_primary_read h_sel_one h_wr_zero
      · exact False.elim (h_primary_write_not_read h_wr_one h_mult)
    · rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec row h_spec with
        h_wr_zero | h_wr_one
      · constructor
        · intro _h_as _h_mult
          exact
            readEventReplayAgreement_after_primary_read_dual_read_of_row
              initialMemory row h_wr_zero
              (h_primary_read h_sel_one h_wr_zero)
        · simp
      · constructor
        · intro _h_as _h_mult
          exact
            readEventReplayAgreement_after_primary_write_dual_read_of_row
              initialMemory row h_wr_one
        · simp

end ZiskFv.AirsClean.FullEnsemble
