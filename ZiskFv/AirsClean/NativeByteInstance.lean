import ZiskFv.AirsClean.ByteMemorySourceProjection
import ZiskFv.AirsClean.MemAlignByte.Bridge
import ZiskFv.AirsClean.MemAlignReadByte.Bridge

/-!
INTERNAL corrected source-native read-capable Byte instance model. This is NOT
an existing Component/Table/Accepted/Root cutover or an old/new domain iff.

The factory computes the actual resolved occurrence, checked physical domain,
and ONE sole-decoder row-zero layout check. All FinN native/logical row reads
and their complete compiled row operations are then DERIVED total, not supplied
as an all-row success premise. The disjoint instance site owns the actual
ByteMemoryCompiledPadding pair from the SAME raw AIR0, once per source occurrence.

PIL b632 state-machines/mem/pil/mem_align_byte.pil106-118 defines the positive
LOAD8 and negative LOAD1 pair for these two families. All p, ordered zero
messages and every existing row lookup/assertion/channel remain present. Other
AIR families, including WriteOnly, are NOT removed from any global model.

Native production/image/ABI/PIL acceptance and actual constructor totality on
production inputs remain separate unproved boundaries. Recovery below is on
this computed checked representation, never a caller/Root SourceValid promise.
-/
namespace ZiskFv.AirsClean

open Goldilocks
open ZiskFv.AirsClean
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource.Native

/-- The kind is derived from the existing source descriptor, not slot labels. -/
def nativeByteKind : ByteMemoryPhysicalRows.Air → NativeTraceCells.Kind
  | .byte => .byte
  | .readByte => .readByte

/-- Only the computed factory below can construct the owning representation.
No free row reader, scalar, packet, roster, group value or all-row certificate. -/
structure NativeByteInstance (source : SourceObject FGL) where
  private mk ::
  resolved : ResolvedOccurrence source
  physical : ByteMemoryPhysicalRows.Rows resolved
  nativeFirst : NativeTraceCells.Row (nativeByteKind physical.air) resolved false 0

namespace NativeByteInstance

variable {source : SourceObject FGL}

/-- Source-specific construction, with no None-to-zero or guessed native stride. -/
def fromResolved? (resolved : ResolvedOccurrence source) : Option (NativeByteInstance source) :=
  match ByteMemoryPhysicalRows.fromResolved? resolved with
  | none => none
  | some physical =>
    match NativeTraceCells.row? (nativeByteKind physical.air) resolved false 0 with
    | none => none
    | some native => some ⟨resolved, physical, native⟩

/-- This is the actual registry occurrence index, never a caller segment tag. -/
def at? (source : SourceObject FGL) (index : source.Occurrence) :
    Option (NativeByteInstance source) := do
  let resolved ← source.resolve? index.val
  fromResolved? resolved

def key (view : NativeByteInstance source) : RawSource.OccurrenceKey :=
  view.resolved.key

/-- Internal representation recovery, not production/Accepted existence. -/
theorem constructor_recovers (view : NativeByteInstance source) :
    fromResolved? view.resolved = some view := by
  rcases view with ⟨resolved, physical, native⟩
  simp [fromResolved?, ByteMemoryPhysicalRows.constructor_recovers physical,
    native.constructor_recovers]

private theorem resolve_recovers (resolved : ResolvedOccurrence source) :
    source.resolve? resolved.globalSlot = some resolved := by
  cases resolved with
  | mk occurrence bound =>
    simp [SourceObject.resolve?, ResolvedOccurrence.globalSlot, occurrence.isLt, bound]

theorem at_recovers (view : NativeByteInstance source) :
    at? source view.resolved.occurrence = some view := by
  unfold at?
  change (source.resolve? view.resolved.globalSlot).bind fromResolved? = some view
  rw [resolve_recovers]
  exact view.constructor_recovers

/-- The row-zero check already established every profile/stride/buffer fact.
Only the row bound changes; FinN supplies it from the SAME selected setup. -/
private theorem native_base_at (view : NativeByteInstance source)
    (index : view.physical.Index) :
    NativeTraceCells.rowBase? (nativeByteKind view.physical.air)
      view.resolved false index.val =
        some (index.val * view.resolved.slotData.metadata.nColsTrace) := by
  have initial := view.nativeFirst.selected
  unfold NativeTraceCells.rowBase? at initial ⊢
  simp only [view.physical.setupSelected] at initial ⊢
  dsimp only [Bind.bind, Option.bind] at initial ⊢
  simp only [view.physical.cm1Selected] at initial ⊢
  split at initial
  · rename_i checked
    rcases checked with ⟨hready, hgroup, hair, hverify, hgpu, hcount, _, hcm1,
      hstride, hpositive, hcoverage⟩
    rw [if_pos ⟨hready, hgroup, hair, hverify, hgpu, hcount, index.isLt,
      hcm1, hstride, hpositive, hcoverage⟩]
  · simp at initial

/-- Every physical row has a constructed sole-getter descriptor. No callback or
universal row-success input is stored or requested. No trace is copied. -/
def nativeAt (view : NativeByteInstance source) (index : view.physical.Index) :
    NativeTraceCells.Row (nativeByteKind view.physical.air) view.resolved false index.val :=
  ⟨index.val * view.resolved.slotData.metadata.nColsTrace,
    native_base_at view index⟩

theorem native_getter_total (view : NativeByteInstance source)
    (index : view.physical.Index) :
    NativeTraceCells.row? (nativeByteKind view.physical.air)
      view.resolved false index.val = some (view.nativeAt index) :=
  (view.nativeAt index).constructor_recovers

/-- At most16/10 logical fields are read per requested row, by the existing
source projection. Unpacked raw F storage is NOT a typed Rust Bool coercion. -/
def logicalRow? (view : NativeByteInstance source) (index : view.physical.Index) :
    Option (MemAlignByte.MemAlignByteRow FGL ⊕ MemAlignReadByte.MemAlignReadByteRow FGL) :=
  match view.physical.air with
  | .byte => (ByteMemorySourceProjection.byte? view.physical index).map Sum.inl
  | .readByte => (ByteMemorySourceProjection.read? view.physical index).map Sum.inr

/-- Pointwise totality is derived for ALL FinN rows from row zero and the
physical descriptor, rather than added as a SourceValid/caller field. -/
theorem logical_rows_total (view : NativeByteInstance source)
    (index : view.physical.Index) :
    ∃ row, view.logicalRow? index = some row := by
  cases hair : view.physical.air with
  | byte =>
    have native : NativeTraceCells.Row .byte view.resolved false index.val := by
      simpa [nativeByteKind, hair] using view.nativeAt index
    obtain ⟨row, hr⟩ := ByteMemorySourceProjection.byte_projection_defined
      view.physical index hair native
    exact ⟨Sum.inl row, by simp [logicalRow?, hair, hr]⟩
  | readByte =>
    have native : NativeTraceCells.Row .readByte view.resolved false index.val := by
      simpa [nativeByteKind, hair] using view.nativeAt index
    obtain ⟨row, hr⟩ := ByteMemorySourceProjection.read_projection_defined
      view.physical index hair native
    exact ⟨Sum.inr row, by simp [logicalRow?, hair, hr]⟩

/-- These are the COMPLETE existing compiled row circuits, not a channel filter
or a handcrafted message list. All lookups/assertions/internal channels stay. -/
def compiledRowOperations :
    (MemAlignByte.MemAlignByteRow FGL ⊕ MemAlignReadByte.MemAlignReadByteRow FGL) → Operations FGL
  | .inl row => (MemAlignByte.main (MemAlignByte.constVar row)).operations 0
  | .inr row => (MemAlignReadByte.main (MemAlignReadByte.constVar row)).operations 0

def rowOperations? (view : NativeByteInstance source) (index : view.physical.Index) :
    Option (Operations FGL) :=
  (view.logicalRow? index).map compiledRowOperations

theorem row_operations_total (view : NativeByteInstance source)
    (index : view.physical.Index) :
    ∃ operations, view.rowOperations? index = some operations := by
  obtain ⟨row, hr⟩ := view.logical_rows_total index
  exact ⟨compiledRowOperations row, by simp [rowOperations?, hr]⟩

/-- The ACTUAL previously compiled Direct circuit captures SAME-source AIR0.
No scalar is accepted from a caller and no zero-multiplicity tuple is removed. -/
def instanceOperations (view : NativeByteInstance source) : Operations FGL :=
  (ByteMemoryCompiledPadding.byteCircuit (.const view.physical.padding)).operations 0

/-- The emission index is a disjoint row domain plus ONE instance site. There
is no N-row list, row map/slice, copied matrix or extra per-row Direct emission. -/
def operationsAt? (view : NativeByteInstance source)
    (site : view.physical.Index ⊕ Unit) : Option (Operations FGL) :=
  match site with
  | .inl index => view.rowOperations? index
  | .inr () => some view.instanceOperations

theorem emissions_total (view : NativeByteInstance source)
    (site : view.physical.Index ⊕ Unit) :
    ∃ operations, view.operationsAt? site = some operations := by
  cases site with
  | inl index => exact view.row_operations_total index
  | inr unit => cases unit; exact ⟨view.instanceOperations, rfl⟩

/-- Disjoint source-indexed ownership makes the instance site unique even if a
row's evaluated values happen to coincide with the Direct batch. -/
theorem unique_instance_site (view : NativeByteInstance source) :
    ∃! site : view.physical.Index ⊕ Unit, site.isRight = true := by
  refine ⟨Sum.inr (), rfl, ?_⟩
  intro site h
  cases site with
  | inl index => simp at h
  | inr unit => cases unit; rfl

/-- The actual native source hint lowering owns this compiled instance batch.
Environment is a universally quantified observer, not stored caller data. -/
theorem instance_operations_eq_native (view : NativeByteInstance source)
    (env : Environment FGL) :
    view.physical.sourceOperations? env =
      some (view.instanceOperations.interactionValues env) := by
  rw [view.physical.source_operations_present]
  cases hair : view.physical.air with
  | byte => rfl
  | readByte => rfl

theorem instance_operations_eq_source (view : NativeByteInstance source)
    (env : Environment FGL) :
    some (view.instanceOperations.interactionValues env) = (do
      let air ← RawByteSource.airForEntry? view.resolved.registryEntry
      if ByteMemoryPadding.readCapable air then
        air.hints.mapM (RawByteSource.lowerDirect? air (view.resolved.params false))
      else none) := by
  rw [← view.instance_operations_eq_native env]
  simpa only [ByteMemoryPhysicalRows.Rows.sourceOperations?] using
    ByteMemorySourceOperations.byte_operations_eq_source view.resolved env

/-- All SIX fields and both ordered signed multiplicities are retained for any
actual raw p, including0/negative. No nativeP=count or numeric-logUp step. -/
theorem instance_values (view : NativeByteInstance source) (env : Environment FGL) :
    view.instanceOperations.interactionValues env =
      [Channels.MemoryBus.MemBusChannel.pushedIfValue view.physical.padding
          (ByteMemoryCompiledPadding.zeroLoadValue 8),
       Channels.MemoryBus.MemBusChannel.pushedIfValue (-view.physical.padding)
          (ByteMemoryCompiledPadding.zeroLoadValue 1)] :=
  ByteMemoryCompiledPadding.byte_compiled view.physical.padding env

/-- Registry-sized only; all actual read-capable occurrences are selected.
WriteOnly/other AIRs are not removed from any global source contribution list. -/
def selectedOccurrences (source : SourceObject FGL) : List source.Occurrence :=
  source.occurrences.filter fun index =>
    (ByteMemoryPhysicalRows.airForEntry? (source.registryEntry index)).isSome

def roster? (source : SourceObject FGL) : Option (List (NativeByteInstance source)) :=
  (selectedOccurrences source).mapM (at? source)

private theorem fromResolved_preserves (resolved : ResolvedOccurrence source)
    (view : NativeByteInstance source) (h : fromResolved? resolved = some view) :
    view.resolved = resolved := by
  unfold fromResolved? at h
  split at h
  · simp at h
  · rename_i physical hp
    split at h
    · simp at h
    · cases Option.some.inj h
      rfl

private theorem at_occurrence (source : SourceObject FGL) (index : source.Occurrence)
    (view : NativeByteInstance source) (h : at? source index = some view) :
    view.resolved.occurrence = index := by
  unfold at? at h
  cases hr : source.resolve? index.val with
  | none => simp [hr] at h
  | some resolved =>
    have hf : fromResolved? resolved = some view := by simpa [hr] using h
    have hs := fromResolved_preserves resolved view hf
    apply Fin.ext
    change view.resolved.globalSlot = index.val
    rw [hs]
    exact source.resolve_globalSlot index.val resolved hr

private theorem map_occurrences (source : SourceObject FGL)
    (indices : List source.Occurrence) (instances : List (NativeByteInstance source))
    (h : indices.mapM (at? source) = some instances) :
    instances.map (fun view => view.resolved.occurrence) = indices := by
  induction indices generalizing instances with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    cases h
    rfl
  | cons index rest ih =>
    rw [List.mapM_cons] at h
    cases hp : at? source index with
    | none => simp [hp] at h
    | some view =>
      cases ht : rest.mapM (at? source) with
      | none => simp [hp, ht] at h
      | some tail =>
        have heq : view :: tail = instances := by simpa [hp, ht] using h
        subst instances
        simp only [List.map_cons]
        exact congrArg₂ List.cons (at_occurrence source index view hp) (ih tail ht)

/-- Unique source identity is DERIVED for the computed roster; no roster or
roster-equality certificate is a model input. Each member owns one instance site. -/
theorem roster_keys_nodup (source : SourceObject FGL)
    (instances : List (NativeByteInstance source)) (h : roster? source = some instances) :
    (instances.map key).Nodup := by
  have hi := map_occurrences source (selectedOccurrences source) instances h
  have hk : ((selectedOccurrences source).map source.key).Nodup := by
    apply List.Nodup.map (source.key_injective)
    exact (List.nodup_ofFn_ofInjective (fun _ _ eq => eq)).filter _
  rw [← hi] at hk
  simpa only [List.map_map, key, ResolvedOccurrence.key, Function.comp_def] using hk

end NativeByteInstance
end ZiskFv.AirsClean
