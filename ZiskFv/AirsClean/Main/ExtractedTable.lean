import ZiskFv.AirsClean.MainMirrorWeld

/-!
# Physical single-segment Main rows as a Clean table

This module constructs the raw Main table boundary. A `SingleSegmentSource`
contains a finite prefix of the 38 committed stage-1 cells from
`Extraction.Main`, together with uninterpreted storage for every other circuit
lane. Its type fixes only `main_segment` to zero, matching the existing Clean
Main component's single-segment scope.

The two physical fixed columns are the actual modeled `Main.SEGMENT_L1` and
`Main.SEGMENT_STEP` columns: the first is `[1, 0, ...]`, and the second is the
row index over `mainFixedCapacity` (`main/pil/main.pil:90` gives
`STEP = main_segment * 4194304 + SEGMENT_STEP`). The resulting `Air.Flat.Table`
is a construction only. No generated-constraint acceptance, lookup membership,
or channel-balance claim is made here.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- A finite physical prefix of the Main extraction circuit in the modeled
    single-segment scope. Values outside the physical prefix remain total
    because generated predicates use a total circuit interface. -/
structure SingleSegmentSource (F ExtF : Type) where
  height : Nat
  height_le_capacity : height ≤ mainFixedCapacity
  /-- The 38 committed stage-1 cells. Only rows below `height` are placed in
      the physical table. -/
  stage1 : Nat → Fin 38 → F
  /-- Stage 2, out-of-layout columns, rotations, and other witness stages.
      Keeping this lane arbitrary avoids silently replacing observable cells
      with zero. -/
  otherMain : (id column row rotation : Nat) → F
  /-- Preprocessed cells other than the two modeled Main fixed columns, and
      nonzero rotation requests. -/
  otherPreprocessed : (column row rotation : Nat) → F
  /-- All extraction challenges remain represented. -/
  challenges : Nat → ExtF
  /-- Every public value except `main_segment` (index 1), which is zero by the
      source type's single-segment scope. -/
  otherExposed : { index : Nat // index ≠ 1 } → ExtF

@[reducible]
def singleSegmentMainValue (source : SingleSegmentSource FGL FGL)
    (id column row rotation : Nat) : FGL :=
  if id = 1 then
    if h_column : column < 38 then
      if rotation = 0 then
        source.stage1 row ⟨column, h_column⟩
      else
        source.otherMain id column row rotation
    else
      source.otherMain id column row rotation
  else
    source.otherMain id column row rotation

@[reducible]
def singleSegmentPreprocessedValue (source : SingleSegmentSource FGL FGL)
    (column row rotation : Nat) : FGL :=
  if rotation = 0 ∧ column < 2 then
    mainFixedColumns.fixedAt column row
  else
    source.otherPreprocessed column row rotation

@[reducible]
def singleSegmentExposedValue (source : SingleSegmentSource FGL FGL) (index : Nat) : FGL :=
  if h : index = 1 then 0 else source.otherExposed ⟨index, h⟩

instance singleSegmentSourceCircuit : Extraction.Circuit FGL FGL SingleSegmentSource where
  main := singleSegmentMainValue
  preprocessed := singleSegmentPreprocessedValue
  challenge := fun source index => source.challenges index
  exposed := singleSegmentExposedValue

@[simp] theorem singleSegmentSourceCircuit_main
    (source : SingleSegmentSource FGL FGL) (id column row rotation : Nat) :
    Extraction.Circuit.main source (id := id) (column := column)
        (row := row) (rotation := rotation) =
      singleSegmentMainValue source id column row rotation := rfl

@[simp] theorem singleSegmentSourceCircuit_preprocessed
    (source : SingleSegmentSource FGL FGL) (column row rotation : Nat) :
    Extraction.Circuit.preprocessed source (column := column)
        (row := row) (rotation := rotation) =
      singleSegmentPreprocessedValue source column row rotation := rfl

@[simp] theorem singleSegmentSourceCircuit_challenge
    (source : SingleSegmentSource FGL FGL) (index : Nat) :
    Extraction.Circuit.challenge source (index := index) = source.challenges index := rfl

@[simp] theorem singleSegmentSourceCircuit_exposed
    (source : SingleSegmentSource FGL FGL) (index : Nat) :
    Extraction.Circuit.exposed source (index := index) =
      singleSegmentExposedValue source index := rfl

/-- One raw 38-cell physical stage-1 source row. -/
def sourceStage1Row (source : SingleSegmentSource FGL FGL) (row : Nat) : Vector FGL 38 :=
  Vector.ofFn (source.stage1 row)

/-- The extraction circuit projection reads every physical stage-1 source
    cell exactly. -/
theorem sourceStage1Cell_preserved (source : SingleSegmentSource FGL FGL) (row : Nat)
    (column : Fin 38) :
    Extraction.Circuit.main source (id := 1) (column := column)
        (row := row) (rotation := 0) =
      (sourceStage1Row source row)[column] := by
  change singleSegmentMainValue source 1 column row 0 = _
  simp [singleSegmentMainValue, sourceStage1Row]

/-- Stage-2 cells are retained in the source rather than stubbed. -/
theorem sourceStage2Cell_preserved (source : SingleSegmentSource FGL FGL)
    (column row rotation : Nat) :
    Extraction.Circuit.main source (id := 2) (column := column)
        (row := row) (rotation := rotation) =
      source.otherMain 2 column row rotation := by
  simp [singleSegmentMainValue]

/-- `main_segment` is zero by the source's single-segment scope. -/
theorem sourceMainSegment_zero (source : SingleSegmentSource FGL FGL) :
    Extraction.Circuit.exposed source (index := 1) = 0 := by
  simp [singleSegmentExposedValue]

/-- All other public values are retained in the source rather than stubbed. -/
theorem sourceOtherExposed_preserved (source : SingleSegmentSource FGL FGL)
    (index : { index : Nat // index ≠ 1 }) :
    Extraction.Circuit.exposed source (index := index) = source.otherExposed index := by
  simp [singleSegmentExposedValue, index.property]

/-- Construct the effective Clean row from one physical source row. -/
def mainRowOfCircuit (source : SingleSegmentSource FGL FGL) (row : Nat) : MainRowWithRom FGL :=
  materializeExtractedMainRow source row

/-- The constructor is an inverse for every one of the 38 committed cells. -/
theorem mainRowOfCircuit_sourceCell (source : SingleSegmentSource FGL FGL) (row : Nat)
    (column : Fin 38) :
    mainValue (extractedMainRow (mainRowOfCircuit source row)) 1 column row 0 =
      source.stage1 row column := by
  unfold mainRowOfCircuit
  rw [materializeExtractedMainRow_mainValue]
  change singleSegmentMainValue source 1 column row 0 = _
  simp [singleSegmentMainValue]

/-- The source type's segment-zero scope and preprocessing projection supply
    exactly the component-owned fixed cells. -/
theorem mainRowOfCircuit_fixedCells (source : SingleSegmentSource FGL FGL) (row : Nat) :
    (mainRowOfCircuit source row).core.segment_l1 =
        mainFixedColumns.fixedAt 0 row ∧
      (mainRowOfCircuit source row).rom.main_step =
        mainFixedColumns.fixedAt 1 row := by
  constructor <;>
    simp [mainRowOfCircuit, materializeExtractedMainRow,
      singleSegmentPreprocessedValue, singleSegmentExposedValue]

/-- The two model-only address cells are constructed from their physical
    stage-1 operands; neither is a new source witness or premise. -/
theorem mainRowOfCircuit_addresses (source : SingleSegmentSource FGL FGL) (row : Nat) :
    (mainRowOfCircuit source row).rom.addr0 = source.stage1 row 10 ∧
      (mainRowOfCircuit source row).rom.addr2 =
        source.stage1 row 24 + source.stage1 row 23 * source.stage1 row 0 := by
  constructor <;>
    simp [mainRowOfCircuit, materializeExtractedMainRow, extractedMainCell,
      singleSegmentMainValue]

/-- The 41-cell raw Clean rows obtained from the finite physical prefix. -/
def mainSourceRawRows (source : SingleSegmentSource FGL FGL) : List (Array FGL) :=
  List.ofFn fun row : Fin source.height => mainRawRow (mainRowOfCircuit source row)

@[simp] theorem mainSourceRawRows_length (source : SingleSegmentSource FGL FGL) :
    (mainSourceRawRows source).length = source.height := by
  simp [mainSourceRawRows]

/-- A concrete Clean Main table whose rows are entirely constructed from the
    physical source and the component-owned fixed schema. -/
def extractedMainTable (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL) : Air.Flat.Table FGL where
  component := componentWithRomMemAndOpBus length program
  rawRows := mainSourceRawRows source
  data := data
  raw_uniform_width := by
    intro raw hraw
    unfold mainSourceRawRows at hraw
    rw [List.mem_ofFn] at hraw
    obtain ⟨row, rfl⟩ := hraw
    change (mainRawRow (mainRowOfCircuit source row)).size = 41
    exact mainRawRow_size _
  fixed_domain := by
    intro columns hcolumns
    have hcolumns' : columns = mainFixedColumns := by
      simpa [componentWithRomMemAndOpBus] using hcolumns.symm
    subst columns
    simpa [mainFixedColumns] using source.height_le_capacity

@[simp] theorem extractedMainTable_length (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL) :
    (extractedMainTable source length program data).length = source.height := by
  change (mainSourceRawRows source).length = source.height
  exact mainSourceRawRows_length source

/-- The effective array at each physical index is the fixed-schema
    materialization of the corresponding constructed 41-cell raw row. -/
theorem extractedMainTable_effectiveRow (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height) :
    (extractedMainTable source length program data).table.get
        ⟨row, by simp⟩ =
      mainFixedColumns.materialize row
        (mainRawRow (mainRowOfCircuit source row)) := by
  simp [extractedMainTable, Air.Flat.Table.table, mainSourceRawRows,
    componentWithRomMemAndOpBus]

/-- Decoding an effective table row reconstructs the same materialized source
    row, including both fixed cells and both model-only addresses. -/
theorem extractedMainTable_rowInput (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height) :
    (componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩) =
      mainRowOfCircuit source row := by
  rw [Air.Flat.Table.environmentAt, extractedMainTable_effectiveRow]
  exact componentWithRomMemAndOpBus_rowInput_materialize length program row data
    (mainRowOfCircuit source row) (mainRowOfCircuit_fixedCells source row).1
    (mainRowOfCircuit_fixedCells source row).2

end ZiskFv.AirsClean.Main
