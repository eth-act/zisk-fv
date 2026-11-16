import ZiskFv.AirsClean.Mem.PhysicalSource.Columns

/-! Internal, computed structural agreement between the ordered setup AIR/GROUP
maps and the independently pinned native Mem layout. This refines the SAME
CompleteView and Params; it does not compare two repacked readers. Only stages
and actual prefix offsets are checked. AIR/GROUP stageId, dim and stagePos are
not initialized by stark_info.cpp125–150 and are deliberately not constrained.
No compiled PILr.id/r.dim, producer, ABI, satisfaction or Root law follows. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- Independent generated PIL scalar roster: fifteen stage1 scalar cells. -/
theorem decoded_mem_base_pil_cells :
    NativeValuesLayout.logicalCells (SourceSchema.air_Mem.symbols.filter fun symbol =>
      decide (symbol.kind = .airValue ∧ symbol.stage = some 1)) = List.range 15 := by
  decide

/-- Explicit native scalar fields, independently flattened from the pinned
MemAirValues declaration; no setup-map name convention is invented. -/
private def baseFields : Vector (String × List Nat) 15 := #v[
  ("segment_id", []), ("is_first_segment", []), ("is_last_segment", []),
  ("previous_segment_value", [0]), ("previous_segment_value", [1]),
  ("previous_segment_step", []), ("previous_segment_addr", []),
  ("segment_last_value", [0]), ("segment_last_value", [1]),
  ("segment_last_step", []), ("segment_last_addr", []),
  ("distance_base", [0]), ("distance_base", [1]),
  ("distance_end", [0]), ("distance_end", [1])]

theorem decoded_mem_base_native_addresses (index : Fin 15) :
    NativeValuesLayout.scalarAddress? .mem (baseFields[index]).1 (baseFields[index]).2 =
      some index.val := by
  fin_cases index <;>
    rw [NativeValuesLayout.scalarAddress?, NativeValuesLayout.address_rules_checked] <;>
    decide

/-- Generated PIL names and logical scalar indices agree with the independently
enumerated native fields. Array element addressing is pinned above, not guessed
from AIR-map names (which are unused by the reader). -/
private theorem base_pil_fields :
    (SourceSchema.air_Mem.symbols.filter fun symbol =>
      decide (symbol.kind = .airValue ∧ symbol.stage = some 1)).flatMap
        (fun symbol => (List.range symbol.lengths.prod).map
          (fun offset => (symbol.name, symbol.index + offset))) =
      List.ofFn (fun index : Fin 15 => ("Mem." ++ (baseFields[index]).1, index.val)) := by
  decide

/-- Independent generated PIL and native-declaration pins establish the six
three-word AIR values and the separate three-word GROUP value. These are not
checks of uninitialized PolMap.dim fields or compiled PILr.r.dim identities. -/
theorem decoded_mem_extension_contract :
    (SourceSchema.air_Mem.symbols.filter fun symbol => symbol.name == "Mem.im_direct") =
      [⟨some 0, some 14, "Mem.im_direct", .airValue, some 2, 15, 1, [6]⟩] ∧
    (∀ index : Fin 6,
      NativeValuesLayout.address? "MemAirValues" "im_direct" [index.val] .extensionF =
        some (15 + 3 * index.val)) ∧
    NativeValuesLayout.declarationFields? "MemAirGroupValues" =
      some [("gsum_result", .extensionF)] ∧
    (SourceSchema.air_Mem.symbols.filter fun symbol => decide (symbol.kind = .airGroupValue)) =
      [⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩] ∧
    NativeValuesLayout.groupAddress? .mem = some 0 ∧
    NativeValuesLayout.slots? .extensionF = some 3 := by
  refine ⟨NativeValuesLayout.actual_mem_inverse_symbol,
    NativeValuesLayout.actual_mem_inverse_addresses,
    NativeValuesLayout.actual_group_native_fields .mem,
    NativeValuesLayout.actual_group_symbol .mem,
    NativeValuesLayout.actual_group_address .mem, ?_⟩
  decide

private def airStage (index : Nat) : Nat := if index < 15 then 1 else 2
private def airOffset (index : Nat) : Nat :=
  if index < 15 then index else 15 + 3 * (index - 15)

/-- The offsets are actual valueOffset prefixes in the authoritative setup.
Their expected values are the native scalar prefix and six extension addresses
pinned by actual_mem_native_fields/actual_mem_inverse_addresses, independently
of the generated actual_mem_inverse_symbol and actual_group_symbol. -/
private def decodingProfile (complete : CompleteView resolved) : Prop :=
  (∀ index : Fin 21,
    (complete.base.setup.airValuesMap[index.val]?).map (·.stage) = some (airStage index.val) ∧
    valueOffset complete.base.setup.airValuesMap index.val = airOffset index.val) ∧
  (complete.base.setup.airgroupValuesMap[0]?).map (·.stage) = some 2

private instance decodingProfileDecidable (complete : CompleteView resolved) :
    Decidable (decodingProfile complete) := by
  unfold decodingProfile
  infer_instance

structure DecodedView (resolved : ResolvedOccurrence source) where
  private mk ::
  complete : CompleteView resolved
  private checked : decodingProfile complete

/-- Shape-only refinement of one already computed view, not a caller's
read-success/coherence promise. Missing or incompatible ordered maps fail. -/
def decodedFromComplete? (complete : CompleteView resolved) : Option (DecodedView resolved) :=
  if checked : decodingProfile complete then some ⟨complete, checked⟩ else none

private theorem selected_stage (entries : Array PolMap) (index stage : Nat)
    (checked : (entries[index]?).map (·.stage) = some stage) :
    ∃ entry, entries[index]? = some entry ∧ entry.stage = stage := by
  cases selected : entries[index]? with
  | none => simp [selected] at checked
  | some entry =>
    exact ⟨entry, selected, Option.some.inj (by simpa [selected] using checked)⟩

private theorem direct_words_selected (complete : CompleteView resolved) (index : Fin 6) :
    NativeValuesLayout.memInverseWords? index (resolved.params false) =
      some complete.base.directWords[index] := by
  have selected := complete.base.directSelected
  unfold directBatch? at selected
  rcases Option.bind_eq_some_iff.mp selected with ⟨a, ha, selected⟩
  rcases Option.bind_eq_some_iff.mp selected with ⟨b, hb, selected⟩
  rcases Option.bind_eq_some_iff.mp selected with ⟨c, hc, selected⟩
  rcases Option.bind_eq_some_iff.mp selected with ⟨d, hd, selected⟩
  rcases Option.bind_eq_some_iff.mp selected with ⟨e, he, selected⟩
  rcases Option.bind_eq_some_iff.mp selected with ⟨f, hf, selected⟩
  have values : #v[a, b, c, d, e, f] = complete.base.directWords := Option.some.inj selected
  rw [← values]
  fin_cases index
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf

private theorem extension_read_at (params : Params FGL) (kind : FieldBufferKind)
    (values : Array FGL) (offset : Nat) (selected : buffer? params kind = some values)
    (bound : offset + 3 ≤ values.size) :
    Stage2.extensionWords? (readBlock? params kind offset 3) =
      some (⟨values[offset], values[offset + 1], values[offset + 2]⟩ : Stage2.Ext3 FGL) := by
  have b0 : offset < values.size := by omega
  have b1 : offset + 1 < values.size := by omega
  have b2 : offset + 2 < values.size := by omega
  simp [Stage2.extensionWords?, readBlock?, selected, bound,
    Array.size_extract, b0, b1, b2, Array.getElem_extract]

/-- A proof about the original block reader and the source-pinned native
three-word projection, not a second executable decoder. -/
private theorem extension_from_native_words (params : Params FGL) (kind : FieldBufferKind)
    (offset : Nat) (words : Vector FGL 3)
    (selected : (do
      return #v[← readWord? params kind offset, ← readWord? params kind (offset + 1),
        ← readWord? params kind (offset + 2)]) = some words) :
    Stage2.extensionWords? (readBlock? params kind offset 3) = some (extension words) := by
  cases buffer : buffer? params kind with
  | none => simp [readWord?, buffer, bind] at selected
  | some values =>
    have b2 : offset + 2 < values.size := by
      by_contra missing
      have absent : values[offset + 2]? = none :=
        getElem?_neg values (offset + 2) (by omega)
      cases h0 : values[offset]? <;> cases h1 : values[offset + 1]? <;>
        simp [readWord?, buffer, h0, h1, absent, bind] at selected
    have b0 : offset < values.size := by omega
    have b1 : offset + 1 < values.size := by omega
    have values_eq : #v[values[offset], values[offset + 1], values[offset + 2]] = words := by
      simpa [readWord?, buffer, b0, b1, b2, bind] using selected
    rw [extension_read_at params kind values offset buffer (by omega), ← values_eq]
    rfl

namespace DecodedView

private theorem base_air_capacity (view : DecodedView resolved) :
    15 < (resolved.params false).airvalues.size := by
  have selected := direct_words_selected view.complete 0
  by_contra missing
  have absent : (resolved.params false).airvalues[15]? = none :=
    getElem?_neg (resolved.params false).airvalues 15 (by omega)
  rw [NativeValuesLayout.mem_inverse_reads_actual_buffer] at selected
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, absent, bind,
    Option.bind_none] at selected

/-- The same original scalar target as CompleteView's polynomial model. -/
def baseAir (view : DecodedView resolved) (index : Fin 15) : FGL :=
  (resolved.params false).airvalues[index.val]'(by
    have capacity := view.base_air_capacity
    have within := index.isLt
    omega)

theorem airValue_base_source (view : DecodedView resolved) (index : Fin 15) :
    Stage2.airValue? resolved index.val = some (Stage2.Ext3.ofBase (view.baseAir index)) := by
  have within : index.val < 21 := by have := index.isLt; omega
  have profile := view.checked.1 ⟨index.val, within⟩
  obtain ⟨entry, selected, stage⟩ := selected_stage _ _ _ profile.1
  have entry_stage : entry.stage = 1 := by simpa [airStage, index.isLt] using stage
  have offset : valueOffset view.complete.base.setup.airValuesMap index.val = index.val := by
    simpa [airOffset, index.isLt] using profile.2
  have reader : Stage2.airValue? resolved index.val =
      Stage2.baseWords? (readBlock? (resolved.params false) .airValue index.val 1) := by
    simp [Stage2.airValue?, within, index.isLt, view.complete.base.setupSelected,
      selected, entry_stage, ResolvedOccurrence.airValueWords?, valueWidth, offset]
  have bound : index.val + 1 ≤ (resolved.params false).airvalues.size := by
    have capacity := view.base_air_capacity
    have col := index.isLt
    omega
  rw [reader]
  simp [Stage2.baseWords?, ZiskFv.AirsClean.Mem.SourceFinalizer.scalarWord?, readBlock?,
    buffer?, bound, Array.size_extract, Array.getElem_extract, baseAir, index.isLt]

theorem airValue_direct_source (view : DecodedView resolved) (index : Fin 6) :
    Stage2.airValue? resolved (15 + index.val) = some (view.complete.direct index) := by
  have within : 15 + index.val < 21 := by have := index.isLt; omega
  have not_base : ¬15 + index.val < 15 := by omega
  have profile := view.checked.1 ⟨15 + index.val, within⟩
  obtain ⟨entry, selected, stage⟩ := selected_stage _ _ _ profile.1
  have entry_stage : entry.stage = 2 := by simpa [airStage, not_base] using stage
  have offset : valueOffset view.complete.base.setup.airValuesMap (15 + index.val) =
      15 + 3 * index.val := by
    simpa [airOffset, not_base] using profile.2
  have reader : Stage2.airValue? resolved (15 + index.val) =
      Stage2.extensionWords? (readBlock? (resolved.params false) .airValue
        (15 + 3 * index.val) 3) := by
    simp [Stage2.airValue?, within, not_base, view.complete.base.setupSelected,
      selected, entry_stage, ResolvedOccurrence.airValueWords?, valueWidth, offset]
  rw [reader]
  apply extension_from_native_words
  have native := direct_words_selected view.complete index
  rw [NativeValuesLayout.mem_inverse_reads_actual_buffer] at native
  simpa [readWord?, buffer?] using native

/-- All twenty-one source AIR leaves, with no caller-supplied successful read. -/
theorem airValue_source (view : DecodedView resolved) (index : Fin 21) :
    Stage2.airValue? resolved index.val =
      if h : index.val < 15 then
        some (Stage2.Ext3.ofBase (view.baseAir ⟨index.val, h⟩))
      else some (view.complete.direct ⟨index.val - 15, by have := index.isLt; omega⟩) := by
  split
  · exact view.airValue_base_source _
  · rename_i not_base
    have back : 15 + (index.val - 15) = index.val := by omega
    simpa only [back] using view.airValue_direct_source
      ⟨index.val - 15, by have := index.isLt; omega⟩

theorem groupValue_source (view : DecodedView resolved) :
    Stage2.groupValue? resolved 0 = some view.complete.group := by
  obtain ⟨entry, selected, stage⟩ := selected_stage _ _ _ view.checked.2
  have reader : Stage2.groupValue? resolved 0 =
      Stage2.extensionWords? (readBlock? (resolved.params false) .airGroupValue 0 3) := by
    simp [Stage2.groupValue?, view.complete.base.setupSelected, selected, stage,
      ResolvedOccurrence.airGroupValueWords?, valueWidth, valueOffset_zero]
  rw [reader]
  apply extension_from_native_words
  have native := view.complete.base.groupSelected
  rw [NativeValuesLayout.group_reads_actual_buffer] at native
  simpa [readWord?, buffer?] using native

end DecodedView
end ZiskFv.AirsClean.Mem.PhysicalSource
