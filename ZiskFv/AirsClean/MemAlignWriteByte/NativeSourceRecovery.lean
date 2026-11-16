import ZiskFv.AirsClean.MemAlignWriteByte.NativeSource

/-! INTERNAL original-buffer constructibility/recovery for the source-owned
WriteByte projection. This adds no SourceObject fields, replacement word store,
SourceValid/row-equality/native-authentication input or Accepted interface.

The finite native AIR/GROUP prefix is read from the original resolved slot;
the entire UInt64 trace, including a possibly larger suffix, remains identical.
Length hypotheses below are local bounded-read constructibility hypotheses, not
new validity predicates or restrictions imposed on production/Root witnesses.
No physical-domain trace array is constructed or copied. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeSourceRecovery

open Goldilocks RawSource.Native
open ZiskFv.AirsClean

/-- Exactly thirteen requested native value words, obtained from the original
buffers. The nine inverse words retain their three separate Ext3 coordinates. -/
def originalValues {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (airBound : 10 ≤ resolved.slotData.airvalues.size)
    (groupBound : 3 ≤ resolved.slotData.airgroupValues.size) : NativeValues.Values :=
  { padding := resolved.slotData.airvalues[0]'(by omega)
    groupWords := #v[resolved.slotData.airgroupValues[0]'(by omega),
      resolved.slotData.airgroupValues[1]'(by omega),
      resolved.slotData.airgroupValues[2]'(by omega)]
    directInverses := #v[
      #v[resolved.slotData.airvalues[1]'(by omega),
        resolved.slotData.airvalues[2]'(by omega),
        resolved.slotData.airvalues[3]'(by omega)],
      #v[resolved.slotData.airvalues[4]'(by omega),
        resolved.slotData.airvalues[5]'(by omega),
        resolved.slotData.airvalues[6]'(by omega)],
      #v[resolved.slotData.airvalues[7]'(by omega),
        resolved.slotData.airvalues[8]'(by omega),
        resolved.slotData.airvalues[9]'(by omega)]] }

/-- Construct the sole getter's real finite row from EXACTLY its existing
native metadata checks and ORIGINAL trace-prefix coverage. The inequality
allows arbitrary additional raw suffix words; no source row array is built.
These are local construction hypotheses, not a new Valid/Accepted predicate. -/
theorem row_defined_from_original_prefix {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (setup : NativeSetup) (hsetup : resolved.setup? = some setup)
    (hcm : setup.mapSectionsN["cm1"]? =
      some (NativeTraceCells.profile .writeByte).unpackedWords)
    (hkey : resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 20)
    (hverify : setup.profile.verify = false) (hgpu : setup.profile.gpu = false)
    (hcount : setup.rowCount = (NativeTraceCells.profile .writeByte).nativeRows)
    (hrow : row < setup.rowCount)
    (hstride : resolved.slotData.metadata.nColsTrace =
      NativeTraceCells.nativeStride .writeByte resolved.slotData.metadata.isPacked)
    (hprefix : setup.rowCount * resolved.slotData.metadata.nColsTrace ≤
      resolved.slotData.trace.size) :
    ∃ view : NativeTraceCells.Row .writeByte resolved mode row,
      NativeTraceCells.row? .writeByte resolved mode row = some view := by
  have hpositive : 0 < resolved.slotData.metadata.nColsTrace := by
    rw [hstride]
    cases resolved.slotData.metadata.isPacked <;> decide +kernel
  have hcheck : NativeTraceRules.ready = true ∧
      resolved.registryEntry.airgroupId = (NativeTraceCells.profile .writeByte).nativeGroup ∧
      resolved.registryEntry.airId = (NativeTraceCells.profile .writeByte).nativeAir ∧
      setup.profile.verify = false ∧ setup.profile.gpu = false ∧
      setup.rowCount = (NativeTraceCells.profile .writeByte).nativeRows ∧
      row < setup.rowCount ∧
      (NativeTraceCells.profile .writeByte).unpackedWords =
        (NativeTraceCells.profile .writeByte).unpackedWords ∧
      resolved.slotData.metadata.nColsTrace =
        NativeTraceCells.nativeStride .writeByte resolved.slotData.metadata.isPacked ∧
      0 < resolved.slotData.metadata.nColsTrace ∧
      setup.rowCount * resolved.slotData.metadata.nColsTrace ≤ (resolved.params mode).trace.size :=
    ⟨NativeTraceRules.actual_source_ready, hkey.1, hkey.2, hverify, hgpu,
      hcount, hrow, rfl, hstride, hpositive, hprefix⟩
  have hbase : NativeTraceCells.rowBase? .writeByte resolved mode row =
      some (row * resolved.slotData.metadata.nColsTrace) := by
    unfold NativeTraceCells.rowBase?
    rw [hsetup]
    dsimp only [Bind.bind, Option.bind]
    rw [hcm]
    dsimp only [Bind.bind, Option.bind]
    rw [if_pos hcheck]
  let view : NativeTraceCells.Row .writeByte resolved mode row :=
    ⟨row * resolved.slotData.metadata.nColsTrace, hbase⟩
  exact ⟨view, view.constructor_recovers⟩

/-- The actual successful source row already establishes the registry identity;
no independent slot-label equality, semantic segment ordinal or width oracle. -/
theorem row_registry_identity {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (view : NativeTraceCells.Row .writeByte resolved mode row) :
    resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 20 := by
  have hbase := view.selected
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
        rcases hprofile with ⟨_, hgroup, hair, _, _, _, _, _, _, _, _⟩
        exact ⟨hgroup, hair⟩
      · simp at hbase

/-- The native bounded buffer reads really recover every requested value, not
an always-None decoder or a free value/source correspondence assertion. -/
theorem values_defined_from_original_buffers {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool)
    (airBound : 10 ≤ resolved.slotData.airvalues.size)
    (groupBound : 3 ≤ resolved.slotData.airgroupValues.size)
    (hkey : resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 20) :
    NativeValues.sourceValues? resolved mode =
      some (originalValues resolved airBound groupBound) := by
  simp (disch := omega) [NativeValues.sourceValues?, hkey,
    NativeValues.decodedValues?, NativeValuesLayout.padding_reads_actual_buffer,
    NativeValuesLayout.group_reads_actual_buffer, NativeValues.inverse_reads_actual_buffer,
    ResolvedOccurrence.params, RawSource.paramsOf, originalValues,
    Array.getElem?_eq_getElem]

/-- A real finite physical row and the actual source value buffers construct a
joint projection. All values are computed, not independent input scalar words. -/
theorem projection_defined_from_original_buffers {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (view : NativeTraceCells.Row .writeByte resolved mode row)
    (airBound : 10 ≤ resolved.slotData.airvalues.size)
    (groupBound : 3 ≤ resolved.slotData.airgroupValues.size) :
    ∃ projection,
      NativeSource.project? resolved mode row = some projection ∧
      projection.values = originalValues resolved airBound groupBound := by
  obtain ⟨cells, hc⟩ := NativeSource.cells_constructible resolved mode row view
  have hv := values_defined_from_original_buffers resolved mode airBound groupBound
    (row_registry_identity resolved mode row view)
  refine ⟨⟨cells, originalValues resolved airBound groupBound⟩, ?_, rfl⟩
  simp [NativeSource.project?, hc, hv]

/-- Exact full original UInt64 storage identity, not merely equality of a
cropped rowCount*stride prefix or of a modulo-p decoded field image. -/
theorem entire_original_trace {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) :
    (resolved.params mode).trace = resolved.slotData.trace := rfl

/-- Every original suffix position is still addressable by the same Params
reader, including positions beyond the physical row prefix. No suffix copy. -/
theorem original_suffix_read {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool)
    (physicalPrefix suffixIndex : Nat) :
    RawSource.traceWord? (resolved.params mode) (physicalPrefix + suffixIndex) =
      resolved.slotData.trace[physicalPrefix + suffixIndex]? := rfl

/-- A genuinely present original suffix word is returned as SOME that exact
UInt64, not merely matched by a vacuous None=None or by field reduction. -/
theorem original_suffix_defined {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool)
    (physicalPrefix suffixIndex : Nat)
    (bound : physicalPrefix + suffixIndex < resolved.slotData.trace.size) :
    RawSource.traceWord? (resolved.params mode) (physicalPrefix + suffixIndex) =
      some (resolved.slotData.trace[physicalPrefix + suffixIndex]'bound) := by
  rw [original_suffix_read]
  simp [bound]

/-- Source padding can be ANY raw field scalar. This transports a genuine
original-slot read, not an honest-builder count or a default-zero convention. -/
theorem directs_recover_raw_scalar {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : NativeSource.Projection)
    (hproject : NativeSource.project? resolved mode row = some projection)
    (padding : FGL) (hraw : resolved.slotData.airvalues[0]? = some padding) :
    projection.onceDirects = NativeTupleSource.directValues padding := by
  have hp : projection.values.padding = padding :=
    Option.some.inj ((NativeSource.project_padding_same_slot resolved mode row
      projection hproject).symm.trans hraw)
  change NativeTupleSource.directValues projection.values.padding = _
  rw [hp]

/-- Zero preserves all three source messages; it does not erase the roster. -/
theorem zero_source_directs {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : NativeSource.Projection)
    (hproject : NativeSource.project? resolved mode row = some projection)
    (hraw : resolved.slotData.airvalues[0]? = some 0) :
    projection.onceDirects.length = 3 ∧
      projection.onceDirects.map Interaction.mult = [0, 0, 0] := by
  rw [directs_recover_raw_scalar resolved mode row projection hproject 0 hraw]
  constructor
  · rfl
  · simp only [NativeTupleSource.direct_multiplicities, neg_zero]

/-- A nontrivial negative raw scalar remains negative; no Nat/count/range
interpretation is silently substituted for the actual AIR0 field value. -/
theorem negative_one_source_directs {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : NativeSource.Projection)
    (hproject : NativeSource.project? resolved mode row = some projection)
    (hraw : resolved.slotData.airvalues[0]? = some (-1 : FGL)) :
    (-1 : FGL) ≠ 0 ∧
      projection.onceDirects.map Interaction.mult = [-1, 1, -1] := by
  constructor
  · exact neg_ne_zero.mpr (one_ne_zero : (1 : FGL) ≠ 0)
  · rw [directs_recover_raw_scalar resolved mode row projection hproject (-1) hraw]
    simp only [NativeTupleSource.direct_multiplicities, neg_neg]

end ZiskFv.AirsClean.MemAlignWriteByte.NativeSourceRecovery
