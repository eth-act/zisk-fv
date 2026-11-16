import ZiskFv.AirsClean.NativeValuesLayout
import ZiskFv.AirsClean.MemAlignWriteByte.SourceInstance
import ZiskFv.AirsClean.MemAlignWriteByte.NativeTupleSource

/-! WriteByte's actual distinct source AIR/GROUP value boundary.
The sole checked NativeValuesLayout supplies native values! addresses, never
PIL stage indices guessed as byte/word addresses. The same resolved occurrence's
Params owns padding AIR0, im_direct[3] (three Ext3 elements), and GROUP0 (Ext3).
No trace reader, profile callback, semantic segment ordinal or caller certificate
is introduced. Actual ABI/native-image authentication remains unproved. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeValues

open Goldilocks RawSource.Native
open ZiskFv.AirsClean

/-- Actual native values! declaration: one F word followed by three Ext3s. -/
theorem actual_native_AIR_fields :
    NativeValuesLayout.declarationFields? "MemAlignWriteByteAirValues" =
      some [("padding_size", .f), ("im_direct", .array .extensionF 3 "3")] := by
  simpa only [NativeValuesLayout.PaddingAir.air, NativeValuesLayout.Air.nativeName,
    NativeValuesLayout.PaddingAir.inverseCount, NativeValuesLayout.PaddingAir.inverseLiteral]
    using NativeValuesLayout.actual_padding_native_fields .writeByte

theorem actual_native_GROUP_fields :
    NativeValuesLayout.declarationFields? "MemAlignWriteByteAirGroupValues" =
      some [("gsum_result", .extensionF)] := by
  simpa only [NativeValuesLayout.Air.nativeName]
    using NativeValuesLayout.actual_group_native_fields .writeByte

/-- Source stage/kind/rank remains distinct from the native Ext3 word prefix. -/
theorem actual_padding_source_kind :
    RawByteSource.ByteAir.writeOnly.paddingSymbols =
      [⟨some 0, some 20, "MemAlignWriteByte.padding_size", .airValue,
        some 1, 0, 0, []⟩] := RawByteSource.padding_source_schema.2.2

theorem actual_inverse_source_kind :
    RawByteSource.ByteAir.writeOnly.schema.symbols.filter
      (fun symbol => decide (symbol.name = "MemAlignWriteByte.im_direct")) =
      [⟨some 0, some 20, "MemAlignWriteByte.im_direct", .airValue,
        some 2, 1, 1, [3]⟩] := RawByteSource.write_direct_array_source_schema

/-- The native source declaration is padding F followed by THREE Ext3 values.
Native address1+3*i is not logical AIR id1+i and not a GROUP offset. -/
theorem inverse_addresses (index : Fin 3) :
    NativeValuesLayout.address? "MemAlignWriteByteAirValues" "im_direct" [index.val] .extensionF =
      some (1 + 3 * index.val) := by
  fin_cases index <;> rw [NativeValuesLayout.address_rules_checked] <;> decide

def inverseWords? (index : Fin 3) (params : RawSource.Params FGL) :
    Option (Vector FGL 3) := do
  let address ← NativeValuesLayout.address? "MemAlignWriteByteAirValues" "im_direct"
    [index.val] .extensionF
  return #v[← RawSource.readWord? params .airValue address,
    ← RawSource.readWord? params .airValue (address + 1),
    ← RawSource.readWord? params .airValue (address + 2)]

theorem inverse_reads_actual_buffer (index : Fin 3) (params : RawSource.Params FGL) :
    inverseWords? index params = (do
      return #v[← params.airvalues[1 + 3 * index.val]?,
        ← params.airvalues[(1 + 3 * index.val) + 1]?,
        ← params.airvalues[(1 + 3 * index.val) + 2]?]) := by
  simp [inverseWords?, inverse_addresses, RawSource.readWord?, RawSource.buffer?]

/-- Computed output data, never an input source-validity/equality promise. -/
structure Values where
  padding : FGL
  groupWords : Vector FGL 3
  directInverses : Vector (Vector FGL 3) 3

def Values.directs (values : Values) : List (Interaction FGL) :=
  NativeTupleSource.directValues values.padding

/-- All projections below use the SAME Params object; no FromTrace GROUP alias. -/
def decodedValues? (params : RawSource.Params FGL) : Option Values := do
  let padding ← NativeValuesLayout.paddingValue? .writeByte params
  let groupWords ← NativeValuesLayout.groupWords? .writeByte params
  let first ← inverseWords? 0 params
  let second ← inverseWords? 1 params
  let third ← inverseWords? 2 params
  return ⟨padding, groupWords, #v[first, second, third]⟩

/-- Final registry labels select the actual WriteByte occurrence. Slot metadata
is not required equal or reinterpreted as an occurrence/segment certificate. -/
def sourceValues? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) : Option Values :=
  if resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 20 then
    decodedValues? (resolved.params mode)
  else none

theorem decoded_values_source (params : RawSource.Params FGL) (values : Values)
    (h : decodedValues? params = some values) :
    NativeValuesLayout.paddingValue? .writeByte params = some values.padding ∧
    NativeValuesLayout.groupWords? .writeByte params = some values.groupWords ∧
    inverseWords? 0 params = some values.directInverses[0] ∧
    inverseWords? 1 params = some values.directInverses[1] ∧
    inverseWords? 2 params = some values.directInverses[2] := by
  unfold decodedValues? at h
  cases hp : NativeValuesLayout.paddingValue? .writeByte params with
  | none => simp [hp, bind, pure] at h
  | some padding =>
    cases hg : NativeValuesLayout.groupWords? .writeByte params with
    | none => simp [hp, hg, bind, pure] at h
    | some groupWords =>
      cases h0 : inverseWords? 0 params with
      | none => simp [hp, hg, h0, bind, pure] at h
      | some first =>
        cases h1 : inverseWords? 1 params with
        | none => simp [hp, hg, h0, h1, bind, pure] at h
        | some second =>
          cases h2 : inverseWords? 2 params with
          | none => simp [hp, hg, h0, h1, h2, bind, pure] at h
          | some third =>
            have heq : (⟨padding, groupWords, #v[first, second, third]⟩ : Values) = values := by
              simpa [hp, hg, h0, h1, h2, bind, pure] using h
            subst values
            exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem source_values_same_params {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (values : Values)
    (h : sourceValues? resolved mode = some values) :
    resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 20 ∧
      decodedValues? (resolved.params mode) = some values := by
  unfold sourceValues? at h
  split at h
  · rename_i hkey
    exact ⟨hkey.1, hkey.2, h⟩
  · simp at h

/-- Padding is the actual raw field word: zero/negative values remain valid
source data, with no count/range/rows-used conversion. -/
theorem decoded_padding_actual (params : RawSource.Params FGL) (values : Values)
    (h : decodedValues? params = some values) : params.airvalues[0]? = some values.padding := by
  have hp := (decoded_values_source params values h).1
  simpa only [NativeValuesLayout.padding_reads_actual_buffer] using hp

/-- GROUP0 is its OWN actual three-word buffer, not padding/AIR0 or FromTrace. -/
theorem decoded_group_actual (params : RawSource.Params FGL) (values : Values)
    (h : decodedValues? params = some values) :
    (do return #v[← params.airgroupValues[0]?, ← params.airgroupValues[1]?,
      ← params.airgroupValues[2]?]) = some values.groupWords := by
  have hg := (decoded_values_source params values h).2.1
  simpa only [NativeValuesLayout.group_reads_actual_buffer] using hg

/-- Same source occurrence/slot buffers, with no mutable-slot label equality
or population/positivity premise. The registry remains the setup authority. -/
theorem source_padding_same_slot {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (values : Values)
    (h : sourceValues? resolved mode = some values) :
    resolved.slotData.airvalues[0]? = some values.padding := by
  have hd := (source_values_same_params resolved mode values h).2.2
  simpa only [ResolvedOccurrence.params, RawSource.paramsOf]
    using decoded_padding_actual (resolved.params mode) values hd

theorem decoded_directs_actual (params : RawSource.Params FGL) (values : Values)
    (h : decodedValues? params = some values) :
    NativeTupleSource.directValues? params = some values.directs := by
  rw [NativeTupleSource.direct_reads_actual_padding, decoded_padding_actual params values h]
  rfl

/-- Real source construction is total on the actual bounded word reads, not an
always-None placeholder or an externally asserted row/source equality. -/
theorem decoded_values_constructible (params : RawSource.Params FGL)
    (padding : FGL) (groupWords first second third : Vector FGL 3)
    (hp : NativeValuesLayout.paddingValue? .writeByte params = some padding)
    (hg : NativeValuesLayout.groupWords? .writeByte params = some groupWords)
    (h0 : inverseWords? 0 params = some first)
    (h1 : inverseWords? 1 params = some second)
    (h2 : inverseWords? 2 params = some third) :
    decodedValues? params = some ⟨padding, groupWords, #v[first, second, third]⟩ := by
  simp [decodedValues?, hp, hg, h0, h1, h2]

end ZiskFv.AirsClean.MemAlignWriteByte.NativeValues
