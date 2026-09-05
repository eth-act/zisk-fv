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

/-- The expression-level row decoder used by the component transition reads
    the same constructed effective row. -/
theorem extractedMainTable_evalRow (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height) :
    Eval.eval
        ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩)
        (varFromOffset (F := FGL) MainRowWithRom 0) =
      mainRowOfCircuit source row := by
  simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar,
    eval_varFromOffset_valueFromOffset] using
    extractedMainTable_rowInput source length program data row

/-! ## Generated physical predicates imply the constructed local assertions

The conclusions below stop at the exact obligations supplied by the generated
Main polynomials. `Operations.ConstraintsHold` additionally requires every ROM
lookup to be contained in its concrete table. Ensemble acceptance additionally
requires the emitted operation, memory, register, and range interactions to be
balanced by their provider tables. Neither fact follows from the row-local
polynomials, so neither is assumed or claimed here. -/

/-- At one physical index, the 29 generated row-local predicates imply every
    `assertZero` in the instantiated Main component. This is stated against the
    component's actual `operations.constraints`, including its concrete row
    variable and offset. -/
theorem extractedMainTable_localAssertionsAt (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height) (h : GeneratedLocalConstraintsAt source row) :
    ∀ e ∈ (componentWithRomMemAndOpBus length program).operations.constraints,
      (extractedMainTable source length program data).environmentAt ⟨row, by simp⟩ e = 0 := by
  let component := componentWithRomMemAndOpBus length program
  let env := (extractedMainTable source length program data).environmentAt ⟨row, by simp⟩
  have hrow : component.rowInput env = mainRowOfCircuit source row := by
    exact extractedMainTable_rowInput source length program data row
  have hv : eval env component.rowInputVar = mainRowOfCircuit source row := by
    simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar,
      eval_varFromOffset_valueFromOffset] using hrow
  rw [Air.Flat.Component.constraints_eq]
  exact assertions_of_extractedGeneratedLocalConstraints source row length program
    component.rowInputVar component.rowOffset env h hv

/-- The local assertion conclusion holds at every physical table index when
    the corresponding generated row-local predicates do. -/
theorem extractedMainTable_localAssertions (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (h : ∀ row : Fin source.height, GeneratedLocalConstraintsAt source row) :
    ∀ row : Fin source.height,
      ∀ e ∈ (componentWithRomMemAndOpBus length program).operations.constraints,
        (extractedMainTable source length program data).environmentAt ⟨row, by simp⟩ e = 0 := by
  intro row
  exact extractedMainTable_localAssertionsAt source length program data row (h row)

/-- Generated constraint 18 gives the predecessor/current PC assertion on the
    decoded effective table rows. The table and extraction interfaces both use
    saturated natural subtraction, so physical row zero reads itself as its
    predecessor and is gated by `SEGMENT_L1 = 1`. This is the PC conjunct of
    the component transition; its source-C-copy conjunct still requires the
    generated public-boundary constraints `3`, `4`, `9`, and `10`. -/
theorem extractedMainTable_pcHandshakeAt (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height)
    (h : Main.extraction.constraint_18_every_row source row) :
    pcHandshakeBetween
      ((componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).previousEnvironment ⟨row, by simp⟩))
      ((componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩)) := by
  have hpc := pcHandshakeBetween_materializeExtractedMainRow_of_constraint_18 source row h
  unfold Air.Flat.Table.previousEnvironment
  rw [extractedMainTable_rowInput source length program data
      ⟨row.val - 1, by omega⟩,
    extractedMainTable_rowInput source length program data row]
  simpa [mainRowOfCircuit] using hpc

/-- Generated b-source-C constraints 4 and 10 imply the intrinsic source-C
    copy on the physical single-segment schema. At row zero the intrinsic
    equation is disabled by `SEGMENT_L1 = 1`, while the generated equations
    select exposed indices 3 and 4 (`segment_previous_c[0]` and `[1]`). At
    every later in-domain row, including the terminal physical row,
    `SEGMENT_L1 = 0`, so the blend reduces to the predecessor's committed `c`
    value without constraining either exposed boundary value. The terminal
    exports at indices 6 and 7 belong to generated constraints 20 and 21 and
    are not part of this predecessor-copy transition. -/
theorem sourceCCopyBetween_mainRowOfCircuit (source : SingleSegmentSource FGL FGL)
    (row : Fin source.height)
    (h4 : Main.extraction.constraint_4_every_row source row)
    (h10 : Main.extraction.constraint_10_every_row source row) :
    sourceCCopyBetween (mainRowOfCircuit source (row - 1))
      (mainRowOfCircuit source row) := by
  by_cases hzero : row.val = 0
  · simp [hzero, sourceCCopyBetween, mainRowOfCircuit, materializeExtractedMainRow,
      singleSegmentPreprocessedValue, mainFixedColumns_segment_l1_first]
  · have hpositive : 0 < row.val := Nat.pos_of_ne_zero hzero
    have hcapacity : row.val < mainFixedCapacity :=
      lt_of_lt_of_le row.isLt source.height_le_capacity
    have hsegment := mainFixedColumns_segment_l1_nonfirst row hpositive hcapacity
    simp [Main.extraction.constraint_4_every_row,
      Main.extraction.constraint_10_every_row, singleSegmentMainValue,
      singleSegmentPreprocessedValue, hsegment] at h4 h10
    simpa [sourceCCopyBetween, mainRowOfCircuit, materializeExtractedMainRow,
      extractedMainCell, singleSegmentMainValue, singleSegmentPreprocessedValue,
      hsegment] using And.intro h4 h10

/-- The source-C copy equation holds on the decoded predecessor/current table
    rows, with arbitrary exposed boundary values preserved in the source. -/
theorem extractedMainTable_sourceCCopyAt (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height)
    (h4 : Main.extraction.constraint_4_every_row source row)
    (h10 : Main.extraction.constraint_10_every_row source row) :
    sourceCCopyBetween
      ((componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).previousEnvironment ⟨row, by simp⟩))
      ((componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩)) := by
  unfold Air.Flat.Table.previousEnvironment
  rw [extractedMainTable_rowInput source length program data
      ⟨row.val - 1, by omega⟩,
    extractedMainTable_rowInput source length program data row]
  exact sourceCCopyBetween_mainRowOfCircuit source row h4 h10

/-- Generated constraints 18, 4, and 10 supply the complete intrinsic Clean
    Main transition at one constructed physical table row. Constraints 3 and 9
    use the same exposed indices 3 and 4 for the corresponding a-source copy,
    but the current intrinsic `transitionBetween` contains only the b-source
    copy. They therefore have no transition conjunct to prove here; adding one
    would strengthen the maintained model. -/
theorem extractedMainTable_transitionBetweenAt (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height)
    (h18 : Main.extraction.constraint_18_every_row source row)
    (h4 : Main.extraction.constraint_4_every_row source row)
    (h10 : Main.extraction.constraint_10_every_row source row) :
    transitionBetween
      ((componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).previousEnvironment ⟨row, by simp⟩))
      ((componentWithRomMemAndOpBus length program).rowInput
        ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩)) := by
  exact ⟨extractedMainTable_pcHandshakeAt source length program data row h18,
    extractedMainTable_sourceCCopyAt source length program data row h4 h10⟩

/-- The live component carries the maintained Main transition function. -/
theorem componentWithRomMemAndOpBus_transition_eq
    (length : Nat) (program : Program length) :
    (componentWithRomMemAndOpBus length program).transition = pcHandshakeTransition := by
  rfl

/-- The physical generated predecessor equations imply the constructed
    table's complete `TransitionConstraints`; no modeled transition or public
    boundary equality is supplied by the caller. -/
theorem extractedMainTable_transitionConstraints (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (h : ∀ row : Fin source.height,
      Main.extraction.constraint_18_every_row source row ∧
      Main.extraction.constraint_4_every_row source row ∧
      Main.extraction.constraint_10_every_row source row) :
    (extractedMainTable source length program data).TransitionConstraints := by
  intro index
  rw [show (extractedMainTable source length program data).component =
      componentWithRomMemAndOpBus length program from rfl,
    componentWithRomMemAndOpBus_transition_eq]
  let row : Fin source.height := ⟨index.val, by simpa using index.isLt⟩
  have hrow := h row
  unfold pcHandshakeTransition Air.Flat.Table.previousEnvironment
  rw [extractedMainTable_evalRow source length program data
      ⟨index.val - 1, by simpa [row] using (show row.val - 1 < source.height by omega)⟩,
    extractedMainTable_evalRow source length program data row]
  exact ⟨by
      simpa [row, mainRowOfCircuit] using
        pcHandshakeBetween_materializeExtractedMainRow_of_constraint_18 source row hrow.1,
    sourceCCopyBetween_mainRowOfCircuit source row hrow.2.1 hrow.2.2⟩

/-- The remaining per-row `ConstraintsHold` gap is exactly concrete lookup
    containment; interaction balance is a separate ensemble-level obligation. -/
theorem extractedMainTable_constraintsHold_iff_assertions_and_lookups
    (source : SingleSegmentSource FGL FGL)
    (length : Nat) (program : Program length) (data : ProverData FGL)
    (row : Fin source.height) :
    (componentWithRomMemAndOpBus length program).operations.ConstraintsHold
        ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩) ↔
      (∀ e ∈ (componentWithRomMemAndOpBus length program).operations.constraints,
          (extractedMainTable source length program data).environmentAt ⟨row, by simp⟩ e = 0) ∧
      (∀ lookup ∈ (componentWithRomMemAndOpBus length program).operations.lookups,
          lookup.Contains
            ((extractedMainTable source length program data).environmentAt ⟨row, by simp⟩)) := by
  rfl

end ZiskFv.AirsClean.Main
