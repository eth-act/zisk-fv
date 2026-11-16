import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage

/-! All chosen algebraic leaves recover the ACTUAL source-owned partial readers.
The theorem is about this computed source image, not an arbitrary field-function
or read-success/coherence certificate supplied by Root. Only the chosen fixture
is unpacked; this does not narrow any production/native acceptance contract. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Stage2

private theorem word_roundtrip (value : FGL) :
    NativeTraceWords.unpackedField (UInt64.ofNat value.val) = value := by
  rw [NativeTraceWords.unpackedField_eq_natCast]
  have fits : value.val < UInt64.size := by
    have bound := value.isLt
    change value.val < 18446744073709551616
    change value.val < 18446744069414584321 at bound
    omega
  rw [UInt64.toNat_ofNat_of_lt' fits]
  apply Fin.ext
  exact Nat.mod_eq_of_lt value.isLt

private theorem setup_of_view (view : CompleteView occurrence) :
    view.base.setup = Constructibility.setup :=
  Option.some.inj (view.base.setupSelected.symm.trans actual_setup)

theorem auxiliary_recovery (view : CompleteView occurrence) (row : Index)
    (column : Fin 3) (rotation : Int) :
    view.auxiliary row column rotation = extensionWitness (view.base.rotate row rotation) column := by
  apply Ext3.eq_of_coeff_eq
  intro coordinate
  rw [view.auxiliary_coeff]
  simp only [Fin.getElem_fin, CompleteView.auxiliaryAddress, actual_auxiliary]
  exact auxiliary_coordinate (view.base.rotate row rotation) column coordinate

theorem stage2_recovery (view : CompleteView occurrence) (row : Index)
    (column : Fin 3) (rotation : Int) :
    Stage2.witness? occurrence row.val 2 column.val rotation =
      some (extensionWitness (view.base.rotate row rotation) column) := by
  rw [view.auxiliary_source, auxiliary_recovery]

private theorem native_word (view : CompleteView occurrence) (row : Index) (column : Fin 13) :
    traceWord? (occurrence.params false)
      (row.val * view.base.nativeStride + column.val) =
      some (UInt64.ofNat ((primary row)[column]).val) := by
  have stride : view.base.nativeStride = 13 := rfl
  have bound : 13 * row.val + column.val < traceBuffer.size := by
    rw [traceBuffer_size]
    have within : row.val < N := row.isLt
    have col := column.isLt
    omega
  simp only [traceWord?, params_trace, stride, Nat.mul_comm]
  rw [getElem?_pos bound, trace_coordinate]

theorem primary_recovery (view : CompleteView occurrence) (row : Index) (column : Fin 13) :
    view.scalar row column = (primary row)[column] := by
  have selectedCell : ∃ cell, ZiskFv.AirsClean.NativeTraceCells.selectedCell? .mem column.val =
      some cell := by
    fin_cases column <;> exact ⟨_, rfl⟩
  obtain ⟨cell, selected⟩ := selectedCell
  have unpacked : occurrence.slotData.metadata.isPacked = false := rfl
  have actual : (NativeProjection.sharedRow view.base row).cell? column.val =
      some ((primary row)[column]) := by
    simp only [ZiskFv.AirsClean.NativeTraceCells.Row.cell?,
      ZiskFv.AirsClean.NativeTraceCells.Row.rawCell?, selected, bind, Option.bind_some,
      unpacked, Bool.false_eq_true, ↓reduceIte, NativeProjection.sharedRow]
    rw [native_word view row column, Option.map_some, word_roundtrip]
  exact Option.some.inj ((view.scalar_checked row column).symm.trans actual)

theorem canonical_primary_recovery (view : CompleteView occurrence) (row : Index)
    (column : Fin 13) :
    ZiskFv.AirsClean.NativeTraceCells.cell? .mem occurrence false row.val column.val =
      some ((primary row)[column]) := by
  rw [view.scalar_source, primary_recovery]

private theorem stage1_map (column : Fin 13) :
    Stage2.witnessMapId? Constructibility.setup 1 column.val = some column.val := by
  unfold Stage2.witnessMapId?
  rw [if_neg (by omega : ¬(1 = 2 ∧ column.val = 0))]
  rw [Array.findIdx?_eq_some_iff_getElem]
  have within := column.isLt
  refine ⟨?_, ?_, ?_⟩
  · simp only [Constructibility.setup, Constructibility.cmMap, Array.size_ofFn]
    omega
  · simp [Constructibility.setup, Constructibility.cmMap, Array.getElem_ofFn, within]
  · intro index before
    have smaller : index < 13 := by omega
    simp [Constructibility.setup, Constructibility.cmMap, Array.getElem_ofFn, smaller,
      Nat.ne_of_lt before]

private theorem stage1_entry (column : Fin 13) :
    (Constructibility.setup.cmPolsMap[column.val]'(by
      simp only [Constructibility.setup, Constructibility.cmMap, Array.size_ofFn]
      have within := column.isLt
      omega)).stage = 1 ∧
    (Constructibility.setup.cmPolsMap[column.val]'(by
      simp only [Constructibility.setup, Constructibility.cmMap, Array.size_ofFn]
      have within := column.isLt
      omega)).stagePos = column.val := by
  simp [Constructibility.setup, Constructibility.cmMap, Array.getElem_ofFn, column.isLt]

private theorem unpacked_single (view : CompleteView occurrence) (row : Index) (column : Fin 13) :
    NativeTraceWords.unpackedBlock? (occurrence.params false) (row.val * 13 + column.val) 1 =
      some #[((primary row)[column])] := by
  have bound : row.val * 13 + column.val + 1 ≤ (occurrence.params false).trace.size := by
    rw [params_trace, traceBuffer_size]
    have within : row.val < N := row.isLt
    have col := column.isLt
    omega
  rw [NativeTraceWords.unpackedBlock_constructible _ _ _ (by decide) bound]
  congr 1
  apply Array.ext
  · simp
  · intro index left right
    have zero : index = 0 := by simpa using left
    subst index
    simp only [Array.getElem_ofFn, Nat.add_zero, params_trace, Nat.mul_comm,
      trace_coordinate, word_roundtrip]
    rfl

theorem stage1_recovery (view : CompleteView occurrence) (row : Index)
    (column : Fin 13) (rotation : Int) :
    Stage2.witness? occurrence row.val 1 column.val rotation =
      some (Ext3.ofBase ((primary (view.base.rotate row rotation))[column])) := by
  have supported : (1 = 1 ∧ column.val < 13) ∨ (1 = 2 ∧ column.val < 3) :=
    Or.inl ⟨rfl, column.isLt⟩
  have entryBound : column.val < Constructibility.setup.cmPolsMap.size := by
    simp only [Constructibility.setup, Constructibility.cmMap, Array.size_ofFn]
    have within := column.isLt
    omega
  have entry := stage1_entry column
  have shifted : Constructibility.setup.baseRow? row.val rotation =
      some (view.base.rotate row rotation).val := by
    rw [← setup_of_view view]
    exact view.base.native_rotation row rotation
  unfold Stage2.witness?
  rw [if_pos supported]
  simp only [bind, actual_setup, Option.bind_some, stage1_map, ↓reduceIte]
  simp only [ResolvedOccurrence.cmWords?, bind, actual_setup, Option.bind_some,
    getElem?_pos entryBound, entry.1, ↓reduceIte]
  have unpacked : occurrence.slotData.metadata.isPacked = false := rfl
  simp only [unpacked, Bool.false_eq_true, ↓reduceIte, shifted, Option.bind_some, entry.2]
  rw [show "cm" ++ toString (1 : Nat) = "cm1" by decide]
  simp only [Constructibility.exact_cm1, Option.bind_some]
  rw [unpacked_single view (view.base.rotate row rotation) column]
  rfl

private theorem base_read_at (params : Params FGL) (kind : FieldBufferKind)
    (values : Array FGL) (offset : Nat) (selected : buffer? params kind = some values)
    (bound : offset < values.size) :
    Stage2.baseWords? (readBlock? params kind offset 1) = some (Ext3.ofBase values[offset]) := by
  have covered : offset + 1 ≤ values.size := by omega
  simp [Stage2.baseWords?, SourceFinalizer.scalarWord?, readBlock?, selected, covered,
    Array.size_extract, Array.getElem_extract]

private theorem extension_read_at (params : Params FGL) (kind : FieldBufferKind)
    (values : Array FGL) (offset : Nat) (selected : buffer? params kind = some values)
    (bound : offset + 3 ≤ values.size) :
    Stage2.extensionWords? (readBlock? params kind offset 3) =
      some (⟨values[offset]'(by omega), values[offset + 1]'(by omega),
        values[offset + 2]'(by omega)⟩ : Ext3 FGL) := by
  simp [Stage2.extensionWords?, readBlock?, selected, bound,
    Array.size_extract, Array.getElem_extract]

private theorem fixed_coordinate (row : Index) (column : Fin 2) :
    Constructibility.fixedBuffer[2 * row.val + column.val]'(by
      rw [Constructibility.fixedBuffer_size]
      have within : row.val < N := row.isLt
      have col := column.isLt
      omega) = firstFlag row := by
  have first : (2 * row.val + column.val < 2) ↔ row.val = 0 := by
    have col := column.isLt
    omega
  simp [Constructibility.fixedBuffer, Array.getElem_ofFn, firstFlag, first]

theorem fixed_recovery (view : CompleteView occurrence) (row : Index)
    (column : Fin 2) (rotation : Int) :
    Stage2.fixed? occurrence row.val column.val rotation =
      some (Ext3.ofBase (firstFlag (view.base.rotate row rotation))) := by
  have shifted : Constructibility.setup.baseRow? row.val rotation =
      some (view.base.rotate row rotation).val := by
    rw [← setup_of_view view]
    exact view.base.native_rotation row rotation
  have fixed : buffer? (occurrence.params false) .fixed = some Constructibility.fixedBuffer := by
    change some occurrence.slotData.fixed = some Constructibility.fixedBuffer
    rw [actual_slot, slot_fixed]
  have bound : (view.base.rotate row rotation).val * 2 + column.val <
      Constructibility.fixedBuffer.size := by
    rw [Constructibility.fixedBuffer_size]
    have within : (view.base.rotate row rotation).val < N := (view.base.rotate row rotation).isLt
    have col := column.isLt
    omega
  unfold Stage2.fixed?
  rw [if_pos column.isLt]
  simp only [ResolvedOccurrence.fixedWords?, actual_setup, bind, Option.bind_some, shifted]
  have constants : Constructibility.setup.nConstants = 2 := rfl
  rw [constants, if_pos column.isLt]
  rw [base_read_at _ _ _ _ fixed bound]
  congr 1
  simpa only [Nat.mul_comm] using fixed_coordinate (view.base.rotate row rotation) column

private theorem air_metadata (index : Fin 21) :
    (Constructibility.setup.airValuesMap[index.val]'(by
      simp only [Constructibility.setup, Constructibility.airMap, Array.size_ofFn]
      exact index.isLt)).stage = (if index.val < 15 then 1 else 2) ∧
    valueOffset Constructibility.setup.airValuesMap index.val =
      (if index.val < 15 then index.val else 15 + 3 * (index.val - 15)) := by
  fin_cases index <;> decide

theorem air_recovery (index : Fin 21) : Stage2.airValue? occurrence index.val = airCell index.val := by
  have bound : index.val < Constructibility.setup.airValuesMap.size := by
    simp only [Constructibility.setup, Constructibility.airMap, Array.size_ofFn]
    exact index.isLt
  have metadata := air_metadata index
  unfold Stage2.airValue?
  rw [if_pos index.isLt]
  simp only [actual_setup, bind, Option.bind_some, getElem?_pos bound, metadata.1]
  by_cases scalar : index.val < 15
  · simp only [if_pos scalar, ↓reduceIte]
    simp only [ResolvedOccurrence.airValueWords?, actual_setup, bind, Option.bind_some,
      getElem?_pos bound, metadata.2, if_pos scalar, valueWidth, metadata.1, if_pos scalar,
      ↓reduceIte]
    have capacity : index.val < airBuffer.size := by rw [airBuffer_size]; omega
    rw [base_read_at _ _ _ _ (by simp [buffer?, params_air]) capacity]
    simp [airCell, scalar, airBuffer, Array.getElem_ofFn]
  · simp only [if_neg scalar, ↓reduceIte]
    simp only [ResolvedOccurrence.airValueWords?, actual_setup, bind, Option.bind_some,
      getElem?_pos bound, metadata.2, if_neg scalar, valueWidth, metadata.1,
      if_neg scalar, ↓reduceIte]
    have capacity : 15 + 3 * (index.val - 15) + 3 ≤ airBuffer.size := by
      rw [airBuffer_size]
      have within := index.isLt
      omega
    rw [extension_read_at _ _ _ _ (by simp [buffer?, params_air]) capacity]
    fin_cases index <;> simp_all [airCell, airBuffer, Array.getElem_ofFn, Ext3.coeff]

theorem group_recovery : Stage2.groupValue? occurrence 0 = some groupResult := by
  simp [Stage2.groupValue?, actual_setup, ResolvedOccurrence.airGroupValueWords?, bind,
    valueOffset_zero, valueWidth, Constructibility.setup, readBlock?, buffer?, params_group,
    groupBuffer, Stage2.extensionWords?]

/-- Recovery of EVERY supported or unsupported leaf. Opaque AST remains None;
no selector-zero or missing-buffer shortcut makes a read disappear. -/
theorem witness_cell_recovery (view : CompleteView occurrence) (row : Index)
    (stage column : Nat) (rotation : Int) :
    Stage2.witness? occurrence row.val stage column rotation =
      witnessCell view.base row stage column rotation := by
  by_cases first : stage = 1
  · subst stage
    by_cases within : column < 13
    · exact stage1_recovery view row ⟨column, within⟩ rotation
    · simp [Stage2.witness?, witnessCell, within]
  · by_cases second : stage = 2
    · subst stage
      by_cases within : column < 3
      · exact stage2_recovery view row ⟨column, within⟩ rotation
      · simp [Stage2.witness?, witnessCell, within]
    · simp [Stage2.witness?, witnessCell, first, second]

theorem all_air_recovery (index : Nat) : Stage2.airValue? occurrence index = airCell index := by
  by_cases within : index < 21
  · exact air_recovery ⟨index, within⟩
  · simp [Stage2.airValue?, airCell, within, show ¬index < 15 by omega]

theorem challenge_recovery (stage index : Nat) :
    Stage2.challenge? occurrence stage index = challengeCell stage index := by
  by_cases supported : stage = 2 ∧ index < 2
  · obtain ⟨rfl, within⟩ := supported
    interval_cases index
    · exact actual_alpha
    · exact actual_gamma
  · simp [Stage2.challenge?, challengeCell, supported]

theorem all_group_recovery (index : Nat) : Stage2.groupValue? occurrence index = groupCell index := by
  by_cases zero : index = 0
  · subst index
    exact group_recovery
  · simp [Stage2.groupValue?, groupCell, zero]

theorem all_fixed_recovery (view : CompleteView occurrence) (row : Index)
    (column : Nat) (rotation : Int) :
    Stage2.fixed? occurrence row.val column rotation = fixedCell view.base row column rotation := by
  by_cases within : column < 2
  · exact fixed_recovery view row ⟨column, within⟩ rotation
  · simp [Stage2.fixed?, fixedCell, within]

theorem polynomial_recovery (view : CompleteView occurrence) (row : Index)
    (expr : Extraction.LookupWiring.Expr) :
    Stage2.polynomial? occurrence row.val expr = polynomial view.base row expr := by
  induction expr with
  | constant text => rfl
  | witness stage column rotation => exact witness_cell_recovery view row stage column rotation
  | fixed column rotation => exact all_fixed_recovery view row column rotation
  | challenge stage index => exact challenge_recovery stage index
  | airValue index => exact all_air_recovery index
  | airGroupValue index => exact all_group_recovery index
  | add lhs rhs left right => simp only [Stage2.polynomial?, polynomial, left, right]
  | sub lhs rhs left right => simp only [Stage2.polynomial?, polynomial, left, right]
  | mul lhs rhs left right => simp only [Stage2.polynomial?, polynomial, left, right]
  | neg value equal => simp only [Stage2.polynomial?, polynomial, equal]
  | opaque kind payload => rfl

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage
