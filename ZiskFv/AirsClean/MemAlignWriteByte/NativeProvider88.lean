import ZiskFv.AirsClean.MemAlignWriteByte.SourceInstance
import ZiskFv.AirsClean.DualBytePackedSource

/-! INTERNAL original-buffer projection of the actual bus88 packed provider.

The primary factory below requires ONLY the same source's resolved final
registry0/AIR33 occurrence. It computes the supported unpacked CM1 view and
reads the actual source88 location for each requested tuple. All 65536 weights,
including zeros, are present; no histogram/count validator or free reader is
an input, and no physical-N decoded trace/list/map is materialized.

Source pins: b632 pil/src/pil_helpers/traces.rs504-513 declares eight field
multiplicity lanes, 2097152 rows, group0/AIR33. ff0e std_virtual_table.rs66-125
loads actual virtual_table_data offsets/widths and global-info rows;193-211
selects lane/row;341-390 writes row-major F::from_u64 weights and installs that
actual global slot with unpacked TraceInfo. Native materialization and equality
of those runtime hints/global-info/setup objects with the observed PIL layout
are NOT inferred from this partial internal decoder. Actual shared/remote/skip
handling, instance pairing, native global balance and Accepted embedding remain
unproved. In particular an absent local table is never interpreted as zero. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeProvider88

open Goldilocks RawSource.Native
open ZiskFv.AirsClean
open Extraction.PackedVirtualTables
open Extraction.LookupWiring

/-- The two existing physical source schemas, without adding a shared kind or
inventing a schema/name fallback for a missing registry-selected setup. -/
def schema (air : Fin 2) : SourceSchema.Air :=
  if air.val = 0 then SourceSchema.air_VirtualTable0 else SourceSchema.air_VirtualTable1

theorem multiplicity_declaration (air : Fin 2) :
    (schema air).symbols[1]? = some
      ⟨some 0, some (schema air).airIndex, "multiplicity", .witness, some 1, 0, 1, [8]⟩ := by
  fin_cases air <;> rfl

/-- Derived internal pointer/layout evidence. Only view? constructs this data;
no shape/success certificate is supplied by a caller. Slot task AIR labels are
retained separately and are NOT required equal to registry authority. -/
structure View {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (air : Fin 2) where
  private mk ::
  setup : NativeSetup
  setupSource : resolved.setup? = some setup
  registryGroup : resolved.registryEntry.airgroupId = 0
  registryAir : resolved.registryEntry.airId = (schema air).airIndex
  cpuVerify : setup.profile.verify = false
  cpuGpu : setup.profile.gpu = false
  rows : setup.rowCount = physicalRows
  cm1Source : setup.mapSectionsN["cm1"]? = some 8
  unpacked : resolved.slotData.metadata.isPacked = false
  stride : resolved.slotData.metadata.nColsTrace = 8
  coverage : physicalRows * 8 ≤ resolved.slotData.trace.size

/-- Partial supported CPU/unpacked CM1 decoder, not a new source validator or
Root scope exclusion. Only real selected setup/slot metadata and buffer bounds
are used. AIR/GROUP values, padding/counts and unrelated source buffers are not
required or rewritten. -/
def view? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (air : Fin 2) : Option (View resolved air) :=
  match hs : resolved.setup? with
  | none => none
  | some setup =>
    match hc : setup.mapSectionsN["cm1"]? with
    | none => none
    | some width =>
      if h : resolved.registryEntry.airgroupId = 0 ∧
          resolved.registryEntry.airId = (schema air).airIndex ∧
          setup.profile.verify = false ∧ setup.profile.gpu = false ∧
          setup.rowCount = physicalRows ∧ width = 8 ∧
          resolved.slotData.metadata.isPacked = false ∧
          resolved.slotData.metadata.nColsTrace = 8 ∧
          physicalRows * 8 ≤ resolved.slotData.trace.size then
        some (by
          rcases h with ⟨hg, ha, hv, hgpu, hr, hw, hp, hc8, hb⟩
          exact ⟨setup, hs, hg, ha, hv, hgpu, hr,
            hc.trans (congrArg some hw), hp, hc8, hb⟩)
      else none

/-- Native bus88 alone never requires an AIR34 view. -/
abbrev Factory {source : SourceObject FGL} (resolved : ResolvedOccurrence source) :=
  View resolved (0 : Fin 2)

def factory? {source : SourceObject FGL} (resolved : ResolvedOccurrence source) :
    Option (Factory resolved) := view? resolved 0

/-- The actual unpacked row-major word address, not lane-major pack_tables
numbering. The production location map supplies the lane and physical row. -/
def wordIndex (row : Fin physicalRows) (lane : Fin 8) : Nat := row.val * 8 + lane.val

theorem View.word_bound {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {air : Fin 2} (view : View resolved air) (row : Fin physicalRows) (lane : Fin 8) :
    wordIndex row lane < resolved.slotData.trace.size := by
  have hr := row.isLt
  have hl := lane.isLt
  have hb := view.coverage
  unfold wordIndex
  omega

/-- Primary original UInt64 word: no canonicalization/copy before selection. -/
def View.word {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {air : Fin 2} (view : View resolved air) (row : Fin physicalRows) (lane : Fin 8) : UInt64 :=
  resolved.slotData.trace[wordIndex row lane]'(view.word_bound row lane)

/-- The existing genuine native Goldilocks conversion, not a callback. -/
def View.field {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {air : Fin 2} (view : View resolved air) (row : Fin physicalRows) (lane : Fin 8) : FGL :=
  RawSource.NativeTraceWords.unpackedField (view.word row lane)

theorem View.word_source {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {air : Fin 2} (view : View resolved air) (row : Fin physicalRows) (lane : Fin 8)
    (mode : Bool) :
    RawSource.traceWord? (resolved.params mode) (wordIndex row lane) =
      some (view.word row lane) := by
  change resolved.slotData.trace[wordIndex row lane]? = some (view.word row lane)
  simp [View.word, view.word_bound row lane]

theorem View.field_source {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {air : Fin 2} (view : View resolved air) (row : Fin physicalRows) (lane : Fin 8)
    (mode : Bool) :
    RawSource.NativeTraceWords.unpackedWord? (resolved.params mode) (wordIndex row lane) =
      some (view.field row lane) := by
  simp [RawSource.NativeTraceWords.unpackedWord?, view.word_source row lane mode, View.field]

/-- Every requested native scalar block is total from the computed full-buffer
bound. This allocates one requested scalar, never an N-row field image. -/
theorem View.block_source {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {air : Fin 2} (view : View resolved air) (row : Fin physicalRows) (lane : Fin 8)
    (mode : Bool) :
    RawSource.NativeTraceWords.unpackedBlock? (resolved.params mode) (wordIndex row lane) 1 =
      some (Array.ofFn (fun _ : Fin 1 => view.field row lane)) := by
  have hb : wordIndex row lane + 1 ≤ (resolved.params mode).trace.size := by
    change wordIndex row lane + 1 ≤ resolved.slotData.trace.size
    have := view.word_bound row lane
    omega
  rw [RawSource.NativeTraceWords.unpackedBlock_constructible _ _ _ (by decide) hb]
  apply congrArg some
  apply congrArg Array.ofFn
  funext index
  have hz : index.val = 0 := by have := index.isLt; omega
  simp only [hz, Nat.add_zero]
  rfl

/-- Real existing C-reader correspondence for an ACTUAL selected native map
entry. No global polynomial id/stagePos is guessed from a PIL hint or supplied
as a factory field. Runtime PIL/native-map correlation remains a separate seam. -/
theorem View.cmWords_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {air : Fin 2}
    (view : View resolved air) (mode : Bool) (row : Fin physicalRows) (lane : Fin 8)
    (mapId : Nat) (entry : PolMap)
    (hentry : view.setup.cmPolsMap[mapId]? = some entry)
    (hstage : entry.stage = 1) (hposition : entry.stagePos = lane.val) :
    resolved.cmWords? mode mapId row.val 0 =
      some (Array.ofFn (fun _ : Fin 1 => view.field row lane)) := by
  have hr : row.val < view.setup.rowCount := by rw [view.rows]; exact row.isLt
  have hnonneg : (0 : Int) ≤ (row.val : Int) := Int.natCast_nonneg _
  have hsmall : (row.val : Int) < (view.setup.rowCount : Int) := by exact_mod_cast hr
  have hshift : view.setup.baseRow? row.val 0 = some row.val := by
    simp [NativeSetup.baseRow?, view.cpuVerify, view.cpuGpu, hr,
      Int.emod_eq_of_lt hnonneg hsmall]
  have hkey : "cm" ++ toString (1 : Nat) = "cm1" := rfl
  rw [resolved.cmWords_unpacked_source mode mapId row.val 0 view.setup entry
    view.setupSource hentry hstage view.unpacked]
  simpa [hshift, hstage, hkey, view.cm1Source, hposition, wordIndex, bind, pure] using
    view.block_source row lane mode

/-- The generated source88 map is load-bearing; these arithmetic equations
identify its actual VirtualTable0 lane2 and rows262144+i. -/
theorem source88_coordinates (index : Fin 65536) :
    let location := source88.location (DualBytePackedSource.sourceIndex index)
    location.air.val = 0 ∧ location.lane.val = 2 ∧ location.row.val = 262144 + index.val := by
  have hi := index.isLt
  simp only [Source.location, source88, DualBytePackedSource.sourceIndex, physicalRows]
  omega

def Factory.weight {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    (factory : Factory resolved) (index : Fin 65536) : FGL :=
  let location := source88.location (DualBytePackedSource.sourceIndex index)
  factory.field location.row location.lane

theorem source88_wordIndex (index : Fin 65536) :
    let location := source88.location (DualBytePackedSource.sourceIndex index)
    wordIndex location.row location.lane = (262144 + index.val) * 8 + 2 := by
  have h := source88_coordinates index
  simp only [wordIndex, h.2.1, h.2.2]

theorem Factory.weight_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} (factory : Factory resolved)
    (index : Fin 65536) (mode : Bool) :
    RawSource.NativeTraceWords.unpackedWord? (resolved.params mode)
      ((262144 + index.val) * 8 + 2) = some (factory.weight index) := by
  rw [← source88_wordIndex index]
  exact factory.field_source _ _ mode

/-- Lazy actual tuple provider. The sole weight is computed from the original
source33 buffer; fixed tuple coordinates retain exact A=i/256,B=i%256 order. -/
def Factory.providerRow {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    (factory : Factory resolved) (index : Fin 65536) : DualByteSlice.ProviderRow FGL :=
  DualByteSlice.sourceRows factory.weight index

theorem Factory.provider_coordinates {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} (factory : Factory resolved) (index : Fin 65536) :
    (factory.providerRow index).byte_a = ((index.val / 256 : Nat) : FGL) ∧
      (factory.providerRow index).byte_b = ((index.val % 256 : Nat) : FGL) ∧
      (factory.providerRow index).multiplicity = factory.weight index := ⟨rfl, rfl, rfl⟩

theorem Factory.provider_constructible {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} (factory : Factory resolved) (index : Fin 65536)
    (data : ProverData FGL) (hint : ProverHint FGL) :
    DualByteSlice.circuit.ProverAssumptions (factory.providerRow index) data hint :=
  DualByteSlice.sourceRows_membership factory.weight index

/-- No filtering of zero multiplicities and no conversion to positive counts. -/
def Factory.interactionAt {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    (factory : Factory resolved) (index : Fin 65536) : Interaction FGL :=
  ZiskFv.Channels.DualByte.DualByteChannel.pushedIfValue (factory.weight index)
    ⟨(factory.providerRow index).byte_a, (factory.providerRow index).byte_b⟩

theorem Factory.interaction_weight {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} (factory : Factory resolved) (index : Fin 65536) :
    (factory.interactionAt index).mult = factory.weight index := rfl

/-- Non-vacuous constructor recovery for every supported source view. All
shape evidence is computed inside view?, never supplied to factory? by callers. -/
theorem View.constructor_recovers {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {air : Fin 2}
    (view : View resolved air) : view? resolved air = some view := by
  unfold view?
  split
  · rename_i hs
    rw [view.setupSource] at hs
    cases hs
  · rename_i setup hs
    have heq : setup = view.setup := Option.some.inj (hs.symm.trans view.setupSource)
    subst setup
    split
    · rename_i hc
      rw [view.cm1Source] at hc
      cases hc
    · rename_i width hc
      have heq : width = 8 := Option.some.inj (hc.symm.trans view.cm1Source)
      subst width
      split
      · rename_i hshape
        rcases hshape with ⟨hg, ha, hv, hgpu, hr, hw, hp, hc8, hb⟩
        congr 1
      · rename_i hbad
        exact False.elim (hbad ⟨view.registryGroup, view.registryAir,
          view.cpuVerify, view.cpuGpu, view.rows, rfl, view.unpacked, view.stride, view.coverage⟩)

/-- AUXILIARY pair-indexed image only. Both real final-slot identities and
their SAME SourceObject are retained. No chronological/semantic pairing,
first-matching-AIR choice, unique-table premise or native roster is asserted. -/
structure PackedPair (source : SourceObject FGL) (left right : source.Occurrence) where
  private mk ::
  leftResolved : ResolvedOccurrence source
  leftSource : source.resolve? left.val = some leftResolved
  leftView : Factory leftResolved
  rightResolved : ResolvedOccurrence source
  rightSource : source.resolve? right.val = some rightResolved
  rightView : View rightResolved 1

/-- A caller supplies only source and actual registry positions, not decoded
weights, equalities or a pairing certificate. A missing/unsupported AIR34
affects ONLY this auxiliary whole-witness export, never factory? for AIR33. -/
def pair? (source : SourceObject FGL) (left right : source.Occurrence) :
    Option (PackedPair source left right) :=
  match hl : source.resolve? left.val with
  | none => none
  | some leftResolved =>
    match hr : source.resolve? right.val with
    | none => none
    | some rightResolved => do
      let leftView ← view? leftResolved 0
      let rightView ← view? rightResolved 1
      return ⟨leftResolved, hl, leftView, rightResolved, hr, rightView⟩

theorem PackedPair.left_slot {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right) :
    pair.leftResolved.globalSlot = left.val :=
  source.resolve_globalSlot left.val pair.leftResolved pair.leftSource

theorem PackedPair.right_slot {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right) :
    pair.rightResolved.globalSlot = right.val :=
  source.resolve_globalSlot right.val pair.rightResolved pair.rightSource

theorem PackedPair.registry_authority {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right) :
    pair.leftResolved.registryEntry.airgroupId = 0 ∧
      pair.leftResolved.registryEntry.airId = 33 ∧
      pair.rightResolved.registryEntry.airgroupId = 0 ∧
      pair.rightResolved.registryEntry.airId = 34 :=
  ⟨pair.leftView.registryGroup, pair.leftView.registryAir,
    pair.rightView.registryGroup, pair.rightView.registryAir⟩

/-- Distinct actual positions follow from their different decoded registry
entries; uniqueness/pairing is not supplied as an additional assumption. -/
theorem PackedPair.distinct_positions {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right) : left ≠ right := by
  intro heq
  have hl : pair.leftResolved.occurrence = left := Fin.ext pair.left_slot
  have hr : pair.rightResolved.occurrence = right := Fin.ext pair.right_slot
  have ha := pair.registry_authority.2.1
  have hb := pair.registry_authority.2.2.2
  change (source.registryEntry pair.leftResolved.occurrence).airId = 33 at ha
  change (source.registryEntry pair.rightResolved.occurrence).airId = 34 at hb
  rw [hl, heq] at ha
  rw [hr] at hb
  omega

/-- Total ONLY because BOTH actual full-buffer views exist. Each physical AIR
uses its own original store; there is no value for an absent table, cross-AIR
alias, fallback weight or independently supplied base witness. -/
def PackedPair.rawWitness {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right) :
    PackedVirtualTableSources.Witness FGL :=
  fun location =>
    if location.air.val = 0 then pair.leftView.field location.row location.lane
    else pair.rightView.field location.row location.lane

theorem PackedPair.rawWitness_left_source {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (row : Fin physicalRows) (lane : Fin 8) (mode : Bool) :
    RawSource.NativeTraceWords.unpackedWord? (pair.leftResolved.params mode)
      (wordIndex row lane) = some (pair.rawWitness ⟨0, lane, row⟩) := by
  simpa only [PackedPair.rawWitness, if_pos rfl] using pair.leftView.field_source row lane mode

theorem PackedPair.rawWitness_right_source {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (row : Fin physicalRows) (lane : Fin 8) (mode : Bool) :
    RawSource.NativeTraceWords.unpackedWord? (pair.rightResolved.params mode)
      (wordIndex row lane) = some (pair.rawWitness ⟨1, lane, row⟩) := by
  simpa only [PackedPair.rawWitness, if_neg (by decide : (1 : Nat) ≠ 0)] using
    pair.rightView.field_source row lane mode

/-- All source88 weights are the selected AIR33 words, not a caller equality
between a native image and a separately chosen PackedWitness. -/
theorem PackedPair.project88 {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (index : Fin 65536) :
    PackedVirtualTableSources.project pair.rawWitness source88
      (DualBytePackedSource.sourceIndex index) = pair.leftView.weight index := by
  simp [PackedVirtualTableSources.project, PackedPair.rawWitness, Factory.weight,
    (source88_coordinates index).1]

/-- The existing genuine provider row, with the computed SAME-source witness,
equals the lazy native provider; no new validator/table fallback is introduced. -/
theorem PackedPair.providerRow_eq {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (index : Fin 65536) :
    DualBytePackedSource.providerRow pair.rawWitness index = pair.leftView.providerRow index := by
  simp only [DualBytePackedSource.providerRow, Factory.providerRow,
    DualByteSlice.sourceRows, pair.project88]

/-- Representation equality to existing providerTable, not another eager
table constructor. The native implementation itself remains a lazy family. -/
theorem PackedPair.providerTable_rawRows {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (data : ProverData FGL) :
    (DualBytePackedSource.providerTable pair.rawWitness data).rawRows =
      List.ofFn (fun index : Fin 65536 => #[pair.leftView.weight index]) := by
  dsimp only [DualBytePackedSource.providerTable]
  apply congrArg List.ofFn
  funext index
  rw [pair.providerRow_eq index]
  rfl

theorem PackedPair.providerTable_materialized {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (data : ProverData FGL) :
    (DualBytePackedSource.providerTable pair.rawWitness data).table =
      List.ofFn (fun index : Fin 65536 =>
        (toElements (pair.leftView.providerRow index)).toArray) := by
  rw [DualBytePackedSource.providerTable_materialized]
  apply congrArg List.ofFn
  funext index
  rw [pair.providerRow_eq index]

theorem PackedPair.providerTable_constraints {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (data : ProverData FGL) :
    (DualBytePackedSource.providerTable pair.rawWitness data).Constraints :=
  DualBytePackedSource.providerTable_constraints pair.rawWitness data

/-- Actual existing provider operations evaluated on materialized source rows,
not merely a detached list of desired positive messages. Every zero retained. -/
theorem PackedPair.providerTable_interactions {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right)
    (data : ProverData FGL) :
    (DualBytePackedSource.providerTable pair.rawWitness data).interactionsWith
        ZiskFv.Channels.DualByte.DualByteChannel.toRaw =
      List.ofFn pair.leftView.interactionAt := by
  rw [DualBytePackedSource.providerTable_interactionsWith]
  unfold DualBytePackedSource.providerInteractions
  apply congrArg List.ofFn
  funext index
  rw [pair.providerRow_eq index]
  rfl

/-- Both computed views really export a pair when their actual source slots
are addressable. This is representational constructibility, NOT a theorem that
the runtime selected these two occurrences as corresponding native tables. -/
theorem PackedPair.constructor_recovers {source : SourceObject FGL}
    {left right : source.Occurrence} (pair : PackedPair source left right) :
    pair? source left right = some pair := by
  unfold pair?
  split
  · rename_i hl
    rw [pair.leftSource] at hl
    cases hl
  · rename_i leftResolved hl
    have heq : leftResolved = pair.leftResolved :=
      Option.some.inj (hl.symm.trans pair.leftSource)
    subst leftResolved
    split
    · rename_i hr
      rw [pair.rightSource] at hr
      cases hr
    · rename_i rightResolved hr
      have heq : rightResolved = pair.rightResolved :=
        Option.some.inj (hr.symm.trans pair.rightSource)
      subst rightResolved
      simp only [pair.leftView.constructor_recovers, pair.rightView.constructor_recovers,
        bind, Option.bind, pure, Pure.pure]

end ZiskFv.AirsClean.MemAlignWriteByte.NativeProvider88
