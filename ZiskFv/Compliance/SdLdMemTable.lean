import ZiskFv.Compliance.Instantiation.ConcreteRowReductions
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections

/-!
# Concrete SD/LD Mem provider table

The #221 constructibility phase fixes the first non-empty mutable-Mem table
used by an accepted trace: an SD of the non-zero doubleword `42`, followed by
an LD of the same word.  The table has the physical Mem fixed schema, so its
first row is the actual segment boundary rather than a synthetic prefix.

Regenerate the sidecar literals with the arithmetic recorded in
`docs/ai/plan/PLAN_MEM_PREFIX_221.md`; they solve `mem.pil`'s generated
segment and permutation equations for `std_alpha = 0`, `std_gamma = 1`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.Mem
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Compliance.Instantiation
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- Store `42` at Mem word address `0x14000001` at its c-slot timestamp 19. -/
def sdMemRow : MemRow FGL :=
  memRowOf true false true true 335544321 19 0 0 0 0 42 0

/-- Load the stored word from the same Mem address at its b-slot timestamp 22. -/
def ldMemRow : MemRow FGL :=
  memRowOf true false false false 335544321 22 0 19 3 0 42 0

/-- The first non-degenerate mutable-Mem timeline: a write followed by a
same-address read of its non-zero value. -/
def sdLdMemRows : List (MemRow FGL) := [sdMemRow, ldMemRow]

/-- A one-column prover-data entry with one scalar at each provided row. -/
private def memPrefixColumn (values : Array FGL) (width : Nat) : Array (Vector FGL width) :=
  values.map fun value => Vector.ofFn fun _ : Fin width => value

/-- Canonical generated Mem sidecars for the concrete two-row timeline.

`SEGMENT_L1` and `__L1__` are deliberately absent: they are component-owned
physical fixed columns (`[1, 0, ...]`), not prover-controlled data. -/
def sdLdMemData : ProverData FGL := fun key width =>
  memPrefixColumn
    (if key = MemRawSidecarDataKey.gsum then #[13400303369572487623, 8353862669730390925]
    else if key = MemRawSidecarDataKey.im0 then #[10110234730352224099, 10110234730352224099]
    else if key = MemRawSidecarDataKey.im1 then #[8384883667915720146, 8384883667915720146]
    else if key = MemRawSidecarDataKey.Segment.segmentId then #[0]
    else if key = MemRawSidecarDataKey.Segment.isFirstSegment then #[1]
    else if key = MemRawSidecarDataKey.Segment.isLastSegment then #[1]
    else if key = MemRawSidecarDataKey.Segment.previousSegmentValue0 then #[0]
    else if key = MemRawSidecarDataKey.Segment.previousSegmentValue1 then #[0]
    else if key = MemRawSidecarDataKey.Segment.previousSegmentStep then #[0]
    else if key = MemRawSidecarDataKey.Segment.previousSegmentAddr then #[335544320]
    else if key = MemRawSidecarDataKey.Segment.segmentLastValue0 then #[42]
    else if key = MemRawSidecarDataKey.Segment.segmentLastValue1 then #[0]
    else if key = MemRawSidecarDataKey.Segment.segmentLastStep then #[22]
    else if key = MemRawSidecarDataKey.Segment.segmentLastAddr then #[335544321]
    else if key = MemRawSidecarDataKey.Segment.distanceBase0 then #[0]
    else if key = MemRawSidecarDataKey.Segment.distanceBase1 then #[0]
    else if key = MemRawSidecarDataKey.Segment.distanceEnd0 then #[65534]
    else if key = MemRawSidecarDataKey.Segment.distanceEnd1 then #[1023]
    else if key = MemRawSidecarDataKey.Permutation.stdAlpha then #[0]
    else if key = MemRawSidecarDataKey.Permutation.stdGamma then #[1]
    else if key = MemRawSidecarDataKey.Permutation.imDirect0 then #[1537228672451215360]
    else if key = MemRawSidecarDataKey.Permutation.imDirect1 then #[0]
    else if key = MemRawSidecarDataKey.Permutation.imDirect2 then #[10110234730352224099]
    else if key = MemRawSidecarDataKey.Permutation.imDirect3 then #[10110234730352224099]
    else if key = MemRawSidecarDataKey.Permutation.imDirect4 then #[10110234730352224099]
    else if key = MemRawSidecarDataKey.Permutation.imDirect5 then #[10110234730352224099]
    else #[]) width

theorem sdLdMemRows_capacity : sdLdMemRows.length ≤ memFixedCapacity := by
  norm_num [sdLdMemRows, memFixedCapacity]

/-- The concrete two-row provider table, backed by the canonical generated
sidecar keys and the physical 2^22-row Mem fixed schema. -/
def sdLdMemTable : Table FGL :=
  memRowsTable sdLdMemData sdLdMemRows sdLdMemRows_capacity

theorem sdMemRow_rangeFacts : dualMemRowRangeFacts sdMemRow := by
  norm_num [dualMemRowRangeFacts, sdMemRow, memRowOf, memReadSameAddrOf, memValueOf]

theorem ldMemRow_rangeFacts : dualMemRowRangeFacts ldMemRow := by
  norm_num [dualMemRowRangeFacts, ldMemRow, memRowOf, memReadSameAddrOf, memValueOf]

theorem sdMemRow_proverAssumptions :
    componentWithDualMemBus.circuit.ProverAssumptions sdMemRow sdLdMemData
      (ProverHint.empty FGL) := by
  refine ⟨true, false, true, true, 335544321, 19, 0, 0, 0, 0, 42, 0,
    (by intro _; rfl), (by intro _; rfl), sdMemRow_rangeFacts, ?_⟩
  rfl

theorem ldMemRow_proverAssumptions :
    componentWithDualMemBus.circuit.ProverAssumptions ldMemRow sdLdMemData
      (ProverHint.empty FGL) := by
  refine ⟨true, false, false, false, 335544321, 22, 0, 19, 3, 0, 42, 0,
    (by intro _; rfl), (by intro _; rfl), ldMemRow_rangeFacts, ?_⟩
  rfl

theorem sdLdMemRows_proverAssumptions (index : Fin sdLdMemRows.length) :
    componentWithDualMemBus.circuit.ProverAssumptions (sdLdMemRows.get index)
      sdLdMemData (ProverHint.empty FGL) := by
  have h_index : index.val < 2 := by
    simp [sdLdMemRows]
  interval_cases h : index.val
  · have h_eq : index = ⟨0, by simp [sdLdMemRows]⟩ := Fin.ext (by omega)
    subst index
    simpa [sdLdMemRows] using sdMemRow_proverAssumptions
  · have h_eq : index = ⟨1, by simp [sdLdMemRows]⟩ := Fin.ext (by omega)
    subst index
    simpa [sdLdMemRows] using ldMemRow_proverAssumptions

theorem sdLdMemTable_constraints : sdLdMemTable.Constraints := by
  exact memRowsTable_constraints_of_proverAssumptions sdLdMemData sdLdMemRows
    sdLdMemRows_capacity sdLdMemRows_proverAssumptions

theorem sdLdMemTable_memBusInteractions :
    sdLdMemTable.interactionsWith MemBusChannel.toRaw =
      [memBusInteraction sdMemRow, memBusDualInteraction sdMemRow,
        memBusInteraction ldMemRow, memBusDualInteraction ldMemRow] := by
  rw [sdLdMemTable, memRowsTable_interactionsWith_memBus]
  rfl

@[simp] theorem sdLdMemTable_length : sdLdMemTable.length = 2 := by
  rfl

@[simp] theorem sdLdMemData_isFirstSegment :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.isFirstSegment = 1 := by
  have h_gsum : MemRawSidecarDataKey.Segment.isFirstSegment ≠ MemRawSidecarDataKey.gsum :=
    by decide
  have h_im0 : MemRawSidecarDataKey.Segment.isFirstSegment ≠ MemRawSidecarDataKey.im0 :=
    by decide
  have h_im1 : MemRawSidecarDataKey.Segment.isFirstSegment ≠ MemRawSidecarDataKey.im1 :=
    by decide
  have h_segmentId :
      MemRawSidecarDataKey.Segment.isFirstSegment ≠ MemRawSidecarDataKey.Segment.segmentId :=
    by decide
  simp [proverDataScalar, proverDataColumn, sdLdMemData, memPrefixColumn,
    h_gsum, h_im0, h_im1, h_segmentId]

@[simp] theorem sdLdMemData_gsum_zero :
    memSidecarGsumOfProverData sdLdMemData 0 = 13400303369572487623 := by
  norm_num [memSidecarGsumOfProverData, proverDataColumn, sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_gsum_one :
    memSidecarGsumOfProverData sdLdMemData 1 = 8353862669730390925 := by
  simp (config := { decide := true }) [memSidecarGsumOfProverData,
    proverDataColumn, sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_im0_zero :
    memSidecarIm0OfProverData sdLdMemData 0 = 10110234730352224099 := by
  simp (config := { decide := true }) [memSidecarIm0OfProverData,
    proverDataColumn, sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_im0_one :
    memSidecarIm0OfProverData sdLdMemData 1 = 10110234730352224099 := by
  simp (config := { decide := true }) [memSidecarIm0OfProverData,
    proverDataColumn, sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_im1_zero :
    memSidecarIm1OfProverData sdLdMemData 0 = 8384883667915720146 := by
  simp (config := { decide := true }) [memSidecarIm1OfProverData,
    proverDataColumn, sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_im1_one :
    memSidecarIm1OfProverData sdLdMemData 1 = 8384883667915720146 := by
  simp (config := { decide := true }) [memSidecarIm1OfProverData,
    proverDataColumn, sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_segmentId :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.segmentId = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_isLastSegment :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.isLastSegment = 1 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_previousSegmentValue0 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.previousSegmentValue0 = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_previousSegmentValue1 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.previousSegmentValue1 = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_previousSegmentStep :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.previousSegmentStep = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_previousSegmentAddr :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.previousSegmentAddr = 335544320 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_segmentLastValue0 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.segmentLastValue0 = 42 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_segmentLastValue1 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.segmentLastValue1 = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_segmentLastStep :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.segmentLastStep = 22 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_segmentLastAddr :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.segmentLastAddr = 335544321 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_distanceBase0 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.distanceBase0 = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_distanceBase1 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.distanceBase1 = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_distanceEnd0 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.distanceEnd0 = 65534 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_distanceEnd1 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Segment.distanceEnd1 = 1023 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_stdAlpha :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.stdAlpha = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_stdGamma :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.stdGamma = 1 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_imDirect0 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.imDirect0 = 1537228672451215360 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_imDirect1 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.imDirect1 = 0 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_imDirect2 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.imDirect2 = 10110234730352224099 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_imDirect3 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.imDirect3 = 10110234730352224099 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_imDirect4 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.imDirect4 = 10110234730352224099 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

@[simp] theorem sdLdMemData_imDirect5 :
    proverDataScalar sdLdMemData MemRawSidecarDataKey.Permutation.imDirect5 = 10110234730352224099 := by
  simp (config := { decide := true }) [proverDataScalar, proverDataColumn,
    sdLdMemData, memPrefixColumn]

private def sdLdMemSegmentColumns : ZiskFv.Airs.Mem.SegmentColumns FGL where
  segment_id := 0
  is_first_segment := 1
  is_last_segment := 1
  previous_segment_value_0 := 0
  previous_segment_value_1 := 0
  previous_segment_step := 0
  previous_segment_addr := 335544320
  segment_last_value_0 := 42
  segment_last_value_1 := 0
  segment_last_step := 22
  segment_last_addr := 335544321
  distance_base_0 := 0
  distance_base_1 := 0
  distance_end_0 := 65534
  distance_end_1 := 1023
  segment_l1 := fun row => memFixedColumns.fixedAt MemFixedColumn.segmentL1 row

private def sdLdMemPermutationColumns : ZiskFv.Airs.Mem.PermutationColumns FGL where
  std_alpha := 0
  std_gamma := 1
  l1 := fun row => memFixedColumns.fixedAt MemFixedColumn.l1 row
  im_direct_0 := 1537228672451215360
  im_direct_1 := 0
  im_direct_2 := 10110234730352224099
  im_direct_3 := 10110234730352224099
  im_direct_4 := 10110234730352224099
  im_direct_5 := 10110234730352224099

private theorem sdLdMemSegmentColumns_source :
    memSegmentColumnsOfProverDataAndFixed sdLdMemData
      (fun row => memFixedColumns.fixedAt MemFixedColumn.segmentL1 row) =
      sdLdMemSegmentColumns := by
  simp [sdLdMemSegmentColumns]

private theorem sdLdMemPermutationColumns_source :
    memPermutationColumnsOfProverDataAndFixed sdLdMemData
      (fun row => memFixedColumns.fixedAt MemFixedColumn.l1 row) =
      sdLdMemPermutationColumns := by
  simp [sdLdMemPermutationColumns]

@[simp] theorem sdLdMemTable_memRowAt_zero :
    memRowFromEnvironment (sdLdMemTable.environmentAt ⟨0, by simp⟩) = sdMemRow := by
  change Eval.eval
      (Environment.fromArray
        (memFixedColumns.materialize 0 (memRawRowWithProverData sdLdMemData sdMemRow))
        sdLdMemData)
      (varFromOffset (F := FGL) MemRow 0) = sdMemRow
  exact eval_memRawRowWithProverData_materialize 0 sdLdMemData sdMemRow

@[simp] theorem sdLdMemTable_memRowAt_one :
    memRowFromEnvironment (sdLdMemTable.environmentAt ⟨1, by simp⟩) = ldMemRow := by
  change Eval.eval
      (Environment.fromArray
        (memFixedColumns.materialize 1 (memRawRowWithProverData sdLdMemData ldMemRow))
        sdLdMemData)
      (varFromOffset (F := FGL) MemRow 0) = ldMemRow
  exact eval_memRawRowWithProverData_materialize 1 sdLdMemData ldMemRow

private theorem sdLdMemTable_rangeBridge_zero :
    memRangeSidecarBridge (sdLdMemTable.environmentAt ⟨0, by simp⟩) := by
  exact ⟨eval_memDistanceBase0Expr_materialize 0 sdLdMemData sdMemRow,
    eval_memDistanceBase1Expr_materialize 0 sdLdMemData sdMemRow,
    eval_memDistanceEnd0Expr_materialize 0 sdLdMemData sdMemRow,
    eval_memDistanceEnd1Expr_materialize 0 sdLdMemData sdMemRow⟩

private theorem sdLdMemTable_rangeBridge_one :
    memRangeSidecarBridge (sdLdMemTable.environmentAt ⟨1, by simp⟩) := by
  exact ⟨eval_memDistanceBase0Expr_materialize 1 sdLdMemData ldMemRow,
    eval_memDistanceBase1Expr_materialize 1 sdLdMemData ldMemRow,
    eval_memDistanceEnd0Expr_materialize 1 sdLdMemData ldMemRow,
    eval_memDistanceEnd1Expr_materialize 1 sdLdMemData ldMemRow⟩

@[simp] theorem sdLdMemFixed_segmentL1_zero :
    memFixedColumns.fixedAt MemFixedColumn.segmentL1 0 = 1 := by rfl

@[simp] theorem sdLdMemFixed_segmentL1_one :
    memFixedColumns.fixedAt MemFixedColumn.segmentL1 1 = 0 := by rfl

@[simp] theorem sdLdMemFixed_segmentL1_two :
    memFixedColumns.fixedAt MemFixedColumn.segmentL1 2 = 0 := by rfl

@[simp] theorem sdLdMemFixed_l1_zero :
    memFixedColumns.fixedAt MemFixedColumn.l1 0 = 1 := by rfl

@[simp] theorem sdLdMemFixed_l1_one :
    memFixedColumns.fixedAt MemFixedColumn.l1 1 = 0 := by rfl

@[simp] theorem sdLdMemFixed_l1_two :
    memFixedColumns.fixedAt MemFixedColumn.l1 2 = 0 := by rfl

/-- The two real Mem rows satisfy every generated continuity, range-source,
and permutation equation. Row zero uses the component's saturated
predecessor; row one uses the preceding store row. -/
theorem sdLdMemTable_transitions : sdLdMemTable.TransitionConstraints := by
  rw [Table.TransitionConstraints]
  intro index
  have h_index_lt : index.val < 2 := by
    simpa only [sdLdMemTable_length] using index.isLt
  interval_cases h : index.val
  · have h_eq : index = ⟨0, by simp⟩ := Fin.ext (by omega)
    subst index
    let previous := sdLdMemTable.previousEnvironment ⟨0, by simp⟩
    let current := sdLdMemTable.environmentAt ⟨0, by simp⟩
    have h_current : memRowFromEnvironment current = sdMemRow := by
      exact sdLdMemTable_memRowAt_zero
    have h_previous :
        memRowFromEnvironment previous = sdMemRow := by
      dsimp [previous]
      simpa only [Table.previousEnvironment, Nat.zero_sub] using h_current
    have h_data : current.data = sdLdMemData := by rfl
    have h_range : memRangeSidecarBridge current := by
      exact sdLdMemTable_rangeBridge_zero
    change generatedTransition memFixedColumns 0 previous current
    simp only [generatedTransition, h_data, sdLdMemSegmentColumns_source,
      sdLdMemPermutationColumns_source]
    refine ⟨?_, ?_, h_range⟩
    · norm_num [ZiskFv.Airs.Mem.segmentResidualEveryRow, memWindow, h_current,
        h_previous, sdLdMemSegmentColumns, ZiskFv.Airs.Mem.previous_row_step,
        ZiskFv.Airs.Mem.delta_addr, ZiskFv.Airs.Mem.segment_previous_addr,
        ZiskFv.Airs.Mem.delta_step, ZiskFv.Airs.Mem.segment_previous_value_0,
        ZiskFv.Airs.Mem.segment_previous_value_1, sdMemRow, memRowOf,
        memReadSameAddrOf, memValueOf]
    · norm_num [ZiskFv.Airs.Mem.permutation_every_row, memWindow, h_current,
        h_previous, h_data, sdLdMemPermutationColumns, ZiskFv.Airs.Mem.gsum_increment_1,
        ZiskFv.Airs.Mem.gsum_dual_step, ZiskFv.Airs.Mem.gsum_increment_0,
        ZiskFv.Airs.Mem.gsum_primary_mem, ZiskFv.Airs.Mem.gsum_dual_mem,
        sdLdMemSegmentColumns, ZiskFv.Airs.Mem.direct_gsum_0, ZiskFv.Airs.Mem.direct_gsum_1,
        ZiskFv.Airs.Mem.direct_gsum_distance_base_0,
        ZiskFv.Airs.Mem.direct_gsum_distance_base_1,
        ZiskFv.Airs.Mem.direct_gsum_distance_end_0,
        ZiskFv.Airs.Mem.direct_gsum_distance_end_1,
        ZiskFv.Airs.Mem.gsum_accumulator_delta, sdMemRow, memRowOf,
        memReadSameAddrOf, memValueOf] ; decide
  · have h_eq : index = ⟨1, by simp⟩ := Fin.ext (by omega)
    subst index
    let previous := sdLdMemTable.previousEnvironment ⟨1, by simp⟩
    let current := sdLdMemTable.environmentAt ⟨1, by simp⟩
    have h_current : memRowFromEnvironment current = ldMemRow := by
      exact sdLdMemTable_memRowAt_one
    have h_previous :
        memRowFromEnvironment previous = sdMemRow := by
      dsimp [previous]
      simpa only [Table.previousEnvironment] using sdLdMemTable_memRowAt_zero
    have h_data : current.data = sdLdMemData := by rfl
    have h_range : memRangeSidecarBridge current := by
      exact sdLdMemTable_rangeBridge_one
    change generatedTransition memFixedColumns 1 previous current
    simp only [generatedTransition, h_data, sdLdMemSegmentColumns_source,
      sdLdMemPermutationColumns_source]
    refine ⟨?_, ?_, h_range⟩
    · norm_num [ZiskFv.Airs.Mem.segmentResidualEveryRow, memWindow, h_current,
        h_previous, sdLdMemSegmentColumns, ZiskFv.Airs.Mem.previous_row_step,
        ZiskFv.Airs.Mem.delta_addr, ZiskFv.Airs.Mem.segment_previous_addr,
        ZiskFv.Airs.Mem.delta_step, ZiskFv.Airs.Mem.segment_previous_value_0,
        ZiskFv.Airs.Mem.segment_previous_value_1, sdMemRow, ldMemRow, memRowOf,
        memReadSameAddrOf, memValueOf]
    · norm_num [ZiskFv.Airs.Mem.permutation_every_row, memWindow, h_current,
        h_previous, h_data, sdLdMemPermutationColumns, ZiskFv.Airs.Mem.gsum_increment_1,
        ZiskFv.Airs.Mem.gsum_dual_step, ZiskFv.Airs.Mem.gsum_increment_0,
        ZiskFv.Airs.Mem.gsum_primary_mem, ZiskFv.Airs.Mem.gsum_dual_mem,
        sdLdMemSegmentColumns, ZiskFv.Airs.Mem.direct_gsum_0, ZiskFv.Airs.Mem.direct_gsum_1,
        ZiskFv.Airs.Mem.direct_gsum_distance_base_0,
        ZiskFv.Airs.Mem.direct_gsum_distance_base_1,
        ZiskFv.Airs.Mem.direct_gsum_distance_end_0,
        ZiskFv.Airs.Mem.direct_gsum_distance_end_1,
        ZiskFv.Airs.Mem.gsum_accumulator_delta, sdMemRow, ldMemRow, memRowOf,
        memReadSameAddrOf, memValueOf] ; decide

/-- The full `mem.pil` generated surface (segment 0--23 and permutation
24--33) is available from this table's ordinary constraints and indexed
transition certificate; it is not a separate accepted-trace premise. -/
theorem sdLdMemTable_generatedConstraintFacts :
    MemTableGeneratedConstraintFacts sdLdMemTable (memOfTableData sdLdMemTable)
      (memSegmentOfTableData sdLdMemTable) (memPermutationOfTableData sdLdMemTable) := by
  exact memTableGeneratedConstraintFacts_of_component_constraints_transitions
    sdLdMemTable rfl sdLdMemTable_constraints sdLdMemTable_transitions

end ZiskFv.Compliance
