import ZiskFv.AirsClean.NativeTraceCells
import ZiskFv.AirsClean.PublicIoMainGauge

/-! INTERNAL Main consumer of the ONE shared finite native-cell reader.
Both packed and unpacked modes use the identical SourceObject/resolved occurrence
and original UInt64 Params. The mode argument is the source proof/CPU selection;
packing comes ONLY from the selected slot metadata. Unpacked values are raw
canonical F storage cells, not Rust typed Bool/narrow getters.

A constructor owns one finite38-cell result, actual AIR8 and distinct GROUP3;
it never accepts a callback, a standalone buffer, a default field, or a height
certificate. The gauge is universally quantified, not a native zero/column.
Source registry/setup/PIL realization, ABI/materialization, actual physical-N
coverage, Clean prefix/continuation, completion and Root IO remain unproved. -/
namespace ZiskFv.AirsClean.PublicIoMainNativeTrace

open Goldilocks ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource.Native
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- All stored values are recovered from the same successful shared row and
same source Params. This is not an Accepted interface or a caller certificate. -/
structure View {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) (index : Nat) where
  native : NativeTraceCells.Row .main resolved mode index
  values : Vector FGL 38
  sameValues : native.values? = some values
  airWords : 8 ≤ (resolved.params mode).airvalues.size
  groupWords : 3 ≤ (resolved.params mode).airgroupValues.size

def construct? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) (index : Nat) : Option (View resolved mode index) :=
  match NativeTraceCells.row? .main resolved mode index with
  | none => none
  | some native =>
    match hv : native.values? with
    | none => none
    | some values =>
      if hair : 8 ≤ (resolved.params mode).airvalues.size then
        if hgroup : 3 ≤ (resolved.params mode).airgroupValues.size then
          some ⟨native, values, hv, hair, hgroup⟩
        else none
      else none

namespace View

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
  {mode : Bool} {index : Nat}

theorem constructor_recovers (view : View resolved mode index) :
    construct? resolved mode index = some view := by
  cases view with
  | mk native values hv hair hgroup =>
    have hn := native.constructor_recovers
    simp only [construct?, hn, dif_pos hair, dif_pos hgroup]
    split
    · rename_i hnone
      simp [hv] at hnone
    · rename_i selected hselected
      have heq : selected = values := Option.some.inj (hselected.symm.trans hv)
      subst selected
      rfl

/-- Native success really supplies all38 cells, in either packing mode. No
None→zero or source-index callback is introduced by the Main consumer. -/
theorem native_success_has_view (native : NativeTraceCells.Row .main resolved mode index)
    (hair : 8 ≤ (resolved.params mode).airvalues.size)
    (hgroup : 3 ≤ (resolved.params mode).airgroupValues.size) :
    ∃ view : View resolved mode index, construct? resolved mode index = some view := by
  obtain ⟨values, hv⟩ := native.values_defined
  let view : View resolved mode index := ⟨native, values, hv, hair, hgroup⟩
  exact ⟨view, view.constructor_recovers⟩

def cell (view : View resolved mode index) (column : Fin 38) : FGL :=
  view.values[column.val]

theorem all_native_cells (view : View resolved mode index) (column : Fin 38) :
    NativeTraceCells.cell? .main resolved mode index column.val = some (view.cell column) :=
  view.native.values_coordinates view.values view.sameValues column

/-- Source-profile/physical-index facts are DERIVED from the successful shared
constructor. No numRows→Clean-prefix implication is inserted. CPU/GPU/verify
support checks stay visible; these are not Root input restrictions. -/
theorem source_context (view : View resolved mode index) :
    ∃ setup : NativeSetup, resolved.setup? = some setup ∧
      NativeTraceRules.ready = true ∧ setup.profile.verify = false ∧ setup.profile.gpu = false ∧
      setup.mapSectionsN["cm1"]? = some 38 ∧ setup.rowCount = 4194304 ∧ index < setup.rowCount ∧
      resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 12 ∧
      resolved.slotData.metadata.nColsTrace =
        NativeTraceCells.nativeStride .main resolved.slotData.metadata.isPacked ∧
      setup.rowCount * resolved.slotData.metadata.nColsTrace ≤ (resolved.params mode).trace.size ∧
      view.native.base = index * resolved.slotData.metadata.nColsTrace := by
  have hbase := view.native.selected
  unfold NativeTraceCells.rowBase? at hbase
  cases hs : resolved.setup? with
  | none => simp [hs] at hbase
  | some setup =>
    cases hc : setup.mapSectionsN["cm1"]? with
    | none => simp [hs, hc] at hbase
    | some cm1 =>
      simp only [hs] at hbase
      dsimp only [Bind.bind, Option.bind] at hbase
      simp only [hc] at hbase
      split at hbase
      · rename_i hprofile
        rcases hprofile with ⟨hready, hgroup, hair, hverify, hgpu, hrows,
          hindex, hcm1, hstride, _, hcoverage⟩
        change cm1 = 38 at hcm1
        change setup.rowCount = 4194304 at hrows
        change resolved.registryEntry.airgroupId = 0 at hgroup
        change resolved.registryEntry.airId = 12 at hair
        have heq : index * resolved.slotData.metadata.nColsTrace = view.native.base := by
          simpa using hbase
        exact ⟨setup, rfl, hready, hverify, hgpu, hc.trans (congrArg some hcm1),
          hrows, hindex, hgroup, hair, hstride, hcoverage, heq.symm⟩
      · simp at hbase

def air (view : View resolved mode index) (column : Fin 8) : FGL :=
  (resolved.params mode).airvalues[column.val]'(by have hb := view.airWords; omega)

def airVector (view : View resolved mode index) : Vector FGL 8 := Vector.ofFn view.air

def group (view : View resolved mode index) (column : Fin 3) : FGL :=
  (resolved.params mode).airgroupValues[column.val]'(by have hb := view.groupWords; omega)

def groupVector (view : View resolved mode index) : Vector FGL 3 := Vector.ofFn view.group

/-- GROUP is its own source buffer, never an AIR-array slice or FromTrace claim. -/
theorem same_source_buffers (view : View resolved mode index) :
    view.native.values? = some view.values ∧
    (resolved.params mode).trace = resolved.slotData.trace ∧
    (resolved.params mode).airvalues = resolved.slotData.airvalues ∧
    (resolved.params mode).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params mode).publicInputs = source.globals.publicInputs :=
  ⟨view.sameValues, rfl, rfl, rfl, rfl⟩

theorem actual_air_projection (view : View resolved mode index) :
    NativeValuesLayout.mainWords? (resolved.params mode) = some view.airVector := by
  rw [NativeValuesLayout.main_reads_actual_buffer]
  have hb := view.airWords
  have h0 : 0 < (resolved.params mode).airvalues.size := by omega
  have h1 : 1 < (resolved.params mode).airvalues.size := by omega
  have h2 : 2 < (resolved.params mode).airvalues.size := by omega
  have h3 : 3 < (resolved.params mode).airvalues.size := by omega
  have h4 : 4 < (resolved.params mode).airvalues.size := by omega
  have h5 : 5 < (resolved.params mode).airvalues.size := by omega
  have h6 : 6 < (resolved.params mode).airvalues.size := by omega
  have h7 : 7 < (resolved.params mode).airvalues.size := by omega
  simp only [Array.getElem?_eq_getElem, h0, h1, h2, h3, h4, h5, h6, h7]
  change some #v[(resolved.params mode).airvalues[0], (resolved.params mode).airvalues[1],
    (resolved.params mode).airvalues[2], (resolved.params mode).airvalues[3],
    (resolved.params mode).airvalues[4], (resolved.params mode).airvalues[5],
    (resolved.params mode).airvalues[6], (resolved.params mode).airvalues[7]] = some view.airVector
  apply congrArg some
  apply Vector.ext
  intro column hcolumn
  interval_cases column <;> rfl

theorem actual_group_projection (view : View resolved mode index) :
    NativeValuesLayout.groupWords? .main (resolved.params mode) = some view.groupVector := by
  have sourceRead : NativeValuesLayout.groupWords? .main (resolved.params mode) = (do
      return #v[← (resolved.params mode).airgroupValues[0]?,
        ← (resolved.params mode).airgroupValues[1]?, ← (resolved.params mode).airgroupValues[2]?]) := by
    simp [NativeValuesLayout.groupWords?, NativeValuesLayout.actual_group_address,
      RawSource.readWord?, RawSource.buffer?]
  rw [sourceRead]
  have hb := view.groupWords
  have h0 : 0 < (resolved.params mode).airgroupValues.size := by omega
  have h1 : 1 < (resolved.params mode).airgroupValues.size := by omega
  have h2 : 2 < (resolved.params mode).airgroupValues.size := by omega
  simp only [Array.getElem?_eq_getElem, h0, h1, h2]
  change some #v[(resolved.params mode).airgroupValues[0],
    (resolved.params mode).airgroupValues[1], (resolved.params mode).airgroupValues[2]] = some view.groupVector
  apply congrArg some
  apply Vector.ext
  intro column hcolumn
  interval_cases column <;> rfl

/-- Pure assembly, NOT another reader or a freely supplied source callback. -/
private def assemble {K : Type} (values : Vector K 38) (gauge l1 step addr2 : K) : MainRowWithRom K :=
  { core :=
      { a_0 := values[0], a_1 := values[1], b_0 := values[2], b_1 := values[3],
        c_0 := values[4], c_1 := values[5], flag := values[6], pc := values[7],
        is_external_op := values[19], op := values[20], m32 := values[28], ind_width := values[18],
        set_pc := values[25], jmp_offset1 := values[26], jmp_offset2 := values[27], store_pc := values[21],
        im_high_degree_2 := gauge, segment_l1 := l1 }
    rom :=
      { a_offset_imm0 := values[10], a_imm1 := values[11], b_offset_imm0 := values[15], b_imm1 := values[16],
        store_offset := values[24], a_src_imm := values[8], a_src_mem := values[9], is_precompiled := values[12],
        b_src_imm := values[13], b_src_mem := values[14], store_mem := values[22], store_ind := values[23],
        b_src_ind := values[17], a_src_reg := values[35], b_src_reg := values[36], store_reg := values[37],
        addr0 := values[10], addr1 := values[29], addr2 := addr2, main_step := step,
        a_reg_prev_mem_step := values[30], b_reg_prev_mem_step := values[31], store_reg_prev_mem_step := values[32],
        store_reg_prev_value_0 := values[33], store_reg_prev_value_1 := values[34] } }

def rowFamily (view : View resolved mode index) (gauge : FGL) : MainRowWithRom FGL :=
  assemble view.values gauge (if index = 0 then 1 else 0)
    (view.air 1 * (4194304 : Nat) + (index : Nat))
    (view.cell 24 + view.cell 23 * view.cell 0)

/-- Circuit expressions retain the very same38 source cells and computed
addresses/step. Only the non-native gauge is allowed to be an arbitrary expression. -/
def expressionFamily (view : View resolved mode index) (gauge : Expression FGL) : Var MainRowWithRom FGL :=
  assemble (view.values.map Expression.const) gauge
    (Expression.const (if index = 0 then 1 else 0))
    (Expression.const (view.air 1 * (4194304 : Nat) + (index : Nat)))
    (Expression.const (view.cell 24) + Expression.const (view.cell 23) * Expression.const (view.cell 0))

theorem all_38_source_coordinates (view : View resolved mode index) (gauge : FGL) (column : Fin 38) :
    NativeTraceCells.cell? .main resolved mode index column.val =
      some (mainValue (extractedMainRow (view.rowFamily gauge)) 1 column.val index 0) := by
  fin_cases column <;> exact view.all_native_cells _

/-- Both derived addresses are tied to independently checked actual main.pil
expressions, not merely to an invented field-index ordering. -/
theorem source_derived_coordinates (view : View resolved mode index) (gauge : FGL) :
    PublicIoMainTraceLayout.sourceRulesAccepted = true ∧
    (view.rowFamily gauge).rom.addr0 = view.cell 10 ∧
    (view.rowFamily gauge).rom.addr2 = view.cell 24 + view.cell 23 * view.cell 0 ∧
    (view.rowFamily gauge).core.segment_l1 = (if index = 0 then 1 else 0) ∧
    (view.rowFamily gauge).rom.main_step = view.air 1 * (4194304 : Nat) + (index : Nat) :=
  ⟨PublicIoMainTraceLayout.actual_source_rules, rfl, rfl, rfl, rfl⟩

theorem gauge_family (view : View resolved mode index) (first second : FGL) :
    view.rowFamily second = PublicIoMainGauge.replace (view.rowFamily first) second := rfl

theorem all_model_specs (view : View resolved mode index) (first second : FGL) :
    (Spec (view.rowFamily first).core ↔ Spec (view.rowFamily second).core) ∧
    (Assumptions (view.rowFamily first).core ↔ Assumptions (view.rowFamily second).core) ∧
    (RomBoolSpec (view.rowFamily first) ↔ RomBoolSpec (view.rowFamily second)) ∧
    (AddressSpec (view.rowFamily first) ↔ AddressSpec (view.rowFamily second)) ∧
    (SourceSpec (view.rowFamily first) ↔ SourceSpec (view.rowFamily second)) :=
  ⟨PublicIoMainGauge.core_spec (view.rowFamily first) first second,
   PublicIoMainGauge.assumptions (view.rowFamily first) first second,
   PublicIoMainGauge.rom_boolean_spec (view.rowFamily first) first second,
   PublicIoMainGauge.address_spec (view.rowFamily first) first second,
   PublicIoMainGauge.source_spec (view.rowFamily first) first second⟩

theorem transition_gauge {previousIndex : Nat}
    (previous : View resolved mode previousIndex) (current : View resolved mode index)
    (previousFirst previousSecond currentFirst currentSecond : FGL) :
    transitionBetween (previous.rowFamily previousFirst) (current.rowFamily currentFirst) ↔
      transitionBetween (previous.rowFamily previousSecond) (current.rowFamily currentSecond) :=
  PublicIoMainGauge.transition (previous.rowFamily previousFirst) (current.rowFamily currentFirst)
    previousFirst previousSecond currentFirst currentSecond

theorem expression_gauge_family (view : View resolved mode index) (first second : Expression FGL) :
    view.expressionFamily second = PublicIoMainGauge.replace (view.expressionFamily first) second := rfl

theorem whole_circuit (view : View resolved mode index) (length : Nat) (program : Program length)
    (first second : Expression FGL) :
    mainWithRomMemAndOpBus length program (view.expressionFamily first) =
      mainWithRomMemAndOpBus length program (view.expressionFamily second) :=
  PublicIoMainGauge.whole_circuit length program (view.expressionFamily first) first second

theorem whole_operations (view : View resolved mode index) (length : Nat) (program : Program length)
    (first second : Expression FGL) (offset : Nat) :
    (mainWithRomMemAndOpBus length program (view.expressionFamily first)).operations offset =
      (mainWithRomMemAndOpBus length program (view.expressionFamily second)).operations offset :=
  PublicIoMainGauge.whole_operations length program (view.expressionFamily first) first second offset

theorem all_exposed_channels (view : View resolved mode index) (length : Nat) (program : Program length)
    (first second : Expression FGL) (offset : Nat) :
    (mainWithRomMemAndOpBusElaborated length program).exposedChannels (view.expressionFamily first) offset =
      (mainWithRomMemAndOpBusElaborated length program).exposedChannels (view.expressionFamily second) offset :=
  PublicIoMainGauge.all_exposed_channels length program (view.expressionFamily first) first second offset

theorem all_source_memory_messages (view : View resolved mode index) (first second : Expression FGL) :
    sourcePerRowMemoryMessages (view.expressionFamily first) =
      sourcePerRowMemoryMessages (view.expressionFamily second) :=
  PublicIoMainGauge.all_source_memory_messages (view.expressionFamily first) first second

theorem all_live_memory_messages (view : View resolved mode index) (first second : Expression FGL) :
    livePerRowMemoryMessages (view.expressionFamily first) =
      livePerRowMemoryMessages (view.expressionFamily second) :=
  PublicIoMainGauge.all_live_memory_messages (view.expressionFamily first) first second

theorem rom_message (view : View resolved mode index) (first second : FGL) :
    romMessage (view.rowFamily first) = romMessage (view.rowFamily second) :=
  PublicIoMainGauge.rom_message (view.rowFamily first) first second

theorem operation_messages (view : View resolved mode index) (first second : Expression FGL) :
    opBusMessageExpr (view.expressionFamily first).core =
      opBusMessageExpr (view.expressionFamily second).core ∧
    sourceOpBusMessageExpr (view.expressionFamily first) =
      sourceOpBusMessageExpr (view.expressionFamily second) :=
  ⟨PublicIoMainGauge.operation_message (view.expressionFamily first) first second,
   PublicIoMainGauge.source_operation_message (view.expressionFamily first) first second⟩

def rawCellFamily (view : View resolved mode index) (gauge : FGL) (column : Fin 41) : FGL :=
  match column.val with
  | 0 => view.cell 0 | 1 => view.cell 1 | 2 => view.cell 2
  | 3 => view.cell 3 | 4 => view.cell 4 | 5 => view.cell 5
  | 6 => view.cell 6 | 7 => view.cell 7 | 8 => view.cell 19
  | 9 => view.cell 20 | 10 => view.cell 28 | 11 => view.cell 18
  | 12 => view.cell 25 | 13 => view.cell 26 | 14 => view.cell 27
  | 15 => view.cell 21 | 16 => gauge | 17 => view.cell 10
  | 18 => view.cell 11 | 19 => view.cell 15 | 20 => view.cell 16
  | 21 => view.cell 24 | 22 => view.cell 8 | 23 => view.cell 9
  | 24 => view.cell 12 | 25 => view.cell 13 | 26 => view.cell 14
  | 27 => view.cell 22 | 28 => view.cell 23 | 29 => view.cell 17
  | 30 => view.cell 35 | 31 => view.cell 36 | 32 => view.cell 37
  | 33 => view.cell 10 | 34 => view.cell 29
  | 35 => view.cell 24 + view.cell 23 * view.cell 0
  | 36 => view.cell 30 | 37 => view.cell 31 | 38 => view.cell 32
  | 39 => view.cell 33 | _ => view.cell 34

theorem all_41_raw_coordinates (view : View resolved mode index) (gauge : FGL) (column : Fin 41) :
    view.rawCellFamily gauge column = (mainRawRow (view.rowFamily gauge))[column.val]'(by simp) := by
  fin_cases column <;> rfl

theorem all_other_raw_cells (view : View resolved mode index) (first second : FGL)
    (column : Fin 41) (notGauge : column.val ≠ 16) :
    view.rawCellFamily first column = view.rawCellFamily second column := by
  rw [view.all_41_raw_coordinates, view.all_41_raw_coordinates]
  exact PublicIoMainGauge.all_other_raw_cells (view.rowFamily first) first second column notGauge

end View
end ZiskFv.AirsClean.PublicIoMainNativeTrace
