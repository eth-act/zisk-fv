import ZiskFv.AirsClean.MemAlignWriteByte.RawSource
import ZiskFv.AirsClean.MemAlignWriteByte.NativeTraceWords

/-! Source-owned images of the ff0e33a9 ProofCtx/Dctx/SetupCtx boundary.

Registry labels select setup and verifier (proofman/src/verify_constraints.rs
21–24,58–65; verify.rs143–168). Slot metadata is retained, not required equal:
common/src/proof_ctx.rs484–485 overwrites the chosen global slot unconditionally.
initialize_air_instance checks num_rows against the registry-selected setup's
nBits, not equality of those labels (proofman.rs3873–3885).

NativeSetup is the POST-setup C++ image, not Rust's serde/default map_offsets:
stark_info.cpp263–336 changes offsets with verify/verify_constraints/gpu.
The ordered AIR and GROUP maps and buffers remain separate. No group value is
constructed via TraceInfo.with_airgroup_values/new_from_trace.

SourceObject.context? computes the old typed image; it never accepts a separate
Context, eight decoded values, snapshot-validity predicate or roster certificate.
This is NOT a proof that live Rust/C++ memory has been materialized as SourceObject.
That remaining binding must identify each final global slot, registry-selected
post-setup object, every source buffer and shared global vector. No Accepted,
Component, Table, Circuit, Valid or Root interface is changed here. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

open Goldilocks

open Extraction.LookupWiring

/-- Native C++ PolMap fields, widened from uint64_t. Rank/lengths and dim are
separate; polsMapId is retained but is not used as an AIR/group prefix oracle. -/
structure PolMap where
  name : String
  stage : Nat
  dim : Nat
  imPol : Bool
  stagePos : Nat
  stageId : Nat
  lengths : Array Nat
  commitId : Nat
  expId : Nat
  polsMapId : Nat

structure CustomCommit where
  name : String
  stageWidths : Array Nat
  publicValues : Array Nat

/-- Actual constructor/setup mode, not inferred from the requested Params mode. -/
structure SetupProfile where
  verify : Bool
  verifyConstraints : Bool
  gpu : Bool

/-- Relevant fields of the actual post-setup native StarkInfo object.
The map key in SetupCtx, not these retained metadata labels, is authoritative. -/
structure NativeSetup where
  profile : SetupProfile
  airgroupId : Nat
  airId : Nat
  nBits : Nat
  nBitsExt : Nat
  nStages : Nat
  nConstants : Nat
  nPublics : Nat
  cmPolsMap : Array PolMap
  constPolsMap : Array PolMap
  airValuesMap : Array PolMap
  airgroupValuesMap : Array PolMap
  proofValuesMap : Array PolMap
  publicsMap : Array PolMap
  challengesMap : Array PolMap
  customCommitsMap : Array (Array PolMap)
  customCommits : Array CustomCommit
  openingPoints : Array Int
  mapSectionsN : Std.HashMap String Nat
  mapOffsets : Std.HashMap (String × Bool) Nat

/-- The complete existing generated catalog, without new symbols or guessed AIR
fallbacks. Missing/unsupported setup keys fail context construction explicitly. -/
def sourceSchemas : Array SourceSchema.Air := #[
  SourceSchema.air_Dma, SourceSchema.air_DmaMemCpy, SourceSchema.air_DmaInputCpy,
  SourceSchema.air_Dma64Aligned, SourceSchema.air_Dma64AlignedInputCpy,
  SourceSchema.air_Dma64AlignedMemSet, SourceSchema.air_Dma64AlignedMem,
  SourceSchema.air_Dma64AlignedMemCpy, SourceSchema.air_DmaUnaligned,
  SourceSchema.air_DmaPrePost, SourceSchema.air_DmaPrePostMemCpy,
  SourceSchema.air_DmaPrePostInputCpy, SourceSchema.air_Main, SourceSchema.air_Rom,
  SourceSchema.air_Mem, SourceSchema.air_RomData, SourceSchema.air_InputData,
  SourceSchema.air_MemAlign, SourceSchema.air_MemAlignByte,
  SourceSchema.air_MemAlignReadByte, SourceSchema.air_MemAlignWriteByte,
  SourceSchema.air_Arith, SourceSchema.air_Binary, SourceSchema.air_BinaryAdd,
  SourceSchema.air_BinaryExtension, SourceSchema.air_Add256, SourceSchema.air_ArithEq,
  SourceSchema.air_ArithEq384, SourceSchema.air_Keccakf, SourceSchema.air_Sha256f,
  SourceSchema.air_Poseidon2, SourceSchema.air_Blake2br, SourceSchema.air_SpecifiedRanges,
  SourceSchema.air_VirtualTable0, SourceSchema.air_VirtualTable1]

def sourceSchema? (key : Nat × Nat) : Option SourceSchema.Air :=
  sourceSchemas.find? (fun schema => schema.groupIndex == key.1 && schema.airIndex == key.2)

/-- Source native extension word width, distinct from a symbol's array rank.
The reader uses stage==1 ? 1 : 3 (expressions_info.cpp525–532,553–565). -/
def valueWidth (entry : PolMap) : Nat := if entry.stage = 1 then 1 else 3

/-- Source-expression id -> native word offset, using the actual ordered map.
This is NOT id itself, dim, rank, or a freely supplied decoded offset. -/
def valueOffset (entries : Array PolMap) (id : Nat) : Nat :=
  (entries.toList.take id).foldl (fun offset entry => offset + valueWidth entry) 0

theorem valueOffset_zero (entries : Array PolMap) : valueOffset entries 0 = 0 := rfl

/-- Descriptive physical domain from setup metadata, not an assertion that any
Clean table or populated prefix has this length. -/
def NativeSetup.rowCount (setup : NativeSetup) : Nat := 2 ^ setup.nBits

def NativeSetup.compiledLayout? (setup : NativeSetup) (key : Nat × Nat) :
    Option CompiledLayout := do
  let schema ← sourceSchema? key
  let widths ← (Array.range setup.nStages).mapM fun index =>
    setup.mapSectionsN["cm" ++ toString (index + 1)]?
  return {
    schema
    physicalRows := setup.rowCount
    witnessStageWidths := widths
    fixedColumns := setup.nConstants
    customStageWidths := setup.customCommits.map (·.stageWidths)
    extensionWordWidth := 3 }

/-- A source-owning image: arrays and setup maps are shared by all projections.
This type has no independently chosen RawSource.Context or decoded scalar fields.
Actual live-memory/ABI/producer materialization into this image remains unproved. -/
structure SourceObject (F : Type) where
  globals : Globals F
  registry : Registry
  slots : Array (Instance F)
  setupRepository : Std.HashMap (Nat × Nat) NativeSetup

def SourceObject.compiledLayouts? (source : SourceObject F) : Option (Array CompiledLayout) :=
  source.setupRepository.toArray.mapM fun entry => entry.2.compiledLayout? entry.1

def SourceObject.context? (source : SourceObject F) : Option (Context F) :=
  source.compiledLayouts?.map fun layouts => {
    globals := source.globals
    registry := source.registry
    slots := source.slots
    compiledLayouts := layouts }

/-- Constructor correctness only, not a native snapshot authentication premise. -/
theorem SourceObject.context_same_source (source : SourceObject F) (context : Context F)
    (h : source.context? = some context) :
    context.globals = source.globals ∧ context.registry = source.registry ∧
      context.slots = source.slots := by
  cases hl : source.compiledLayouts? with
  | none => simp [SourceObject.context?, hl] at h
  | some layouts =>
    simp only [SourceObject.context?, hl, Option.map_some, Option.some.injEq] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩

abbrev SourceObject.Occurrence (source : SourceObject F) := Fin source.registry.instances.size

def SourceObject.registryEntry (source : SourceObject F) (index : source.Occurrence) :
    RegistryEntry := source.registry.instances[index.val]

def SourceObject.key (source : SourceObject F) (index : source.Occurrence) : OccurrenceKey :=
  let entry := source.registryEntry index
  ⟨entry.airgroupId, entry.airId, index.val⟩

theorem SourceObject.key_injective (source : SourceObject F) :
    Function.Injective source.key := by
  intro left right h
  exact Fin.ext (congrArg OccurrenceKey.globalSlot h)

def SourceObject.occurrences (source : SourceObject F) : List source.Occurrence := List.ofFn id

theorem SourceObject.occurrence_keys_nodup (source : SourceObject F) :
    (List.ofFn source.key).Nodup :=
  List.nodup_ofFn_ofInjective source.key_injective

/-- Actual get_setup authority: registry pair, never mutable slot metadata. -/
def SourceObject.setupAt? (source : SourceObject F) (index : source.Occurrence) :
    Option NativeSetup :=
  let entry := source.registryEntry index
  source.setupRepository[(entry.airgroupId, entry.airId)]?

/-- No stored decoded values or coherence certificate: only an actual registry
occurrence and proof that its SAME global slot is locally addressable. -/
structure ResolvedOccurrence (source : SourceObject F) where
  occurrence : source.Occurrence
  slotBound : occurrence.val < source.slots.size

def SourceObject.resolve? (source : SourceObject F) (globalSlot : Nat) :
    Option (ResolvedOccurrence source) :=
  if hreg : globalSlot < source.registry.instances.size then
    if hslot : globalSlot < source.slots.size then
      some ⟨⟨globalSlot, hreg⟩, hslot⟩
    else none
  else none

def ResolvedOccurrence.globalSlot {source : SourceObject F}
    (resolved : ResolvedOccurrence source) : Nat := resolved.occurrence.val

def ResolvedOccurrence.registryEntry {source : SourceObject F}
    (resolved : ResolvedOccurrence source) : RegistryEntry := source.registryEntry resolved.occurrence

def ResolvedOccurrence.key {source : SourceObject F}
    (resolved : ResolvedOccurrence source) : OccurrenceKey := source.key resolved.occurrence

def ResolvedOccurrence.slotData {source : SourceObject F}
    (resolved : ResolvedOccurrence source) : Instance F :=
  source.slots[resolved.globalSlot]'resolved.slotBound

def ResolvedOccurrence.isStored {source : SourceObject F}
    (resolved : ResolvedOccurrence source) : Bool := !resolved.slotData.trace.isEmpty

def ResolvedOccurrence.params {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (genProof : Bool) : Params F :=
  paramsOf source.globals resolved.slotData genProof

def ResolvedOccurrence.setup? {source : SourceObject F}
    (resolved : ResolvedOccurrence source) : Option NativeSetup :=
  source.setupAt? resolved.occurrence

theorem SourceObject.resolve_globalSlot (source : SourceObject F) (index : Nat)
    (resolved : ResolvedOccurrence source) (h : source.resolve? index = some resolved) :
    resolved.globalSlot = index := by
  unfold SourceObject.resolve? at h
  split at h
  · split at h
    · cases Option.some.inj h
      rfl
    · simp at h
  · simp at h

theorem ResolvedOccurrence.params_same_buffers {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) :
    (resolved.params mode).trace = resolved.slotData.trace ∧
    (resolved.params mode).airvalues = resolved.slotData.airvalues ∧
    (resolved.params mode).airgroupValues = resolved.slotData.airgroupValues ∧
    (resolved.params mode).customCommitsFixed = resolved.slotData.customCommitsFixed ∧
    (resolved.params mode).publicInputs = source.globals.publicInputs ∧
    (resolved.params mode).proofValues = source.globals.proofValues :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ResolvedOccurrence.setup_registry_authority {source : SourceObject F}
    (resolved : ResolvedOccurrence source) :
    resolved.setup? = source.setupRepository[
      (resolved.registryEntry.airgroupId, resolved.registryEntry.airId)]? := rfl

/-- Source add_air_instance's final-slot replacement, not insertion history. -/
def SourceObject.overwriteSlot (source : SourceObject F) (index : Fin source.slots.size)
    (slotData : Instance F) : SourceObject F :=
  { source with slots := source.slots.set index.val slotData }

theorem SourceObject.overwrite_registry (source : SourceObject F) (slot : Fin source.slots.size)
    (slotData : Instance F) : (source.overwriteSlot slot slotData).registry = source.registry := rfl

theorem SourceObject.overwrite_setupAt (source : SourceObject F) (slot : Fin source.slots.size)
    (slotData : Instance F) (index : source.Occurrence) :
    (source.overwriteSlot slot slotData).setupAt? index = source.setupAt? index := rfl

theorem SourceObject.overwrite_key (source : SourceObject F) (slot : Fin source.slots.size)
    (slotData : Instance F) (index : source.Occurrence) :
    (source.overwriteSlot slot slotData).key index = source.key index := rfl

/-- expressions_info.cpp525–532 and553–565 compute DIFFERENT prefixes in
DIFFERENT maps; expressions_pack.hpp357–360 binds DIFFERENT Params buffers. -/
def ResolvedOccurrence.airValueWords? {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (id : Nat) : Option (Array F) := do
  let setup ← resolved.setup?
  let entry ← setup.airValuesMap[id]?
  readBlock? (resolved.params mode) .airValue
    (valueOffset setup.airValuesMap id) (valueWidth entry)

def ResolvedOccurrence.airGroupValueWords? {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (id : Nat) : Option (Array F) := do
  let setup ← resolved.setup?
  let entry ← setup.airgroupValuesMap[id]?
  readBlock? (resolved.params mode) .airGroupValue
    (valueOffset setup.airgroupValuesMap id) (valueWidth entry)

/-- Scalar projection requires the actual selected map entry to be stage1.
It does not mistake array rank or logical id for native extension/word offset. -/
def ResolvedOccurrence.airValueScalar? {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (id : Nat) : Option F := do
  let setup ← resolved.setup?
  let entry ← setup.airValuesMap[id]?
  if entry.stage = 1 then
    readWord? (resolved.params mode) .airValue (valueOffset setup.airValuesMap id)
  else none

/-- CPU, nonextended native row address. Unsupported verifier/GPU layouts or
out-of-domain rows are absent, not silently reinterpreted as a Clean row.
Signed rotation uses mathematical modulo; a consumer must bind actual opening
strides, fixed native widths, defined machine arithmetic and its PIL reference. -/
def NativeSetup.baseRow? (setup : NativeSetup) (row : Nat) (rotation : Int) : Option Nat :=
  if setup.profile.verify || setup.profile.gpu then none
  else if row < setup.rowCount then
    some (((row : Int) + rotation) % (setup.rowCount : Int)).toNat
  else none

/-- Shared actual auxiliary branch, using metadata already selected from the
same source occurrence. Field trace decoding is not smuggled into generic F. -/
def cmAuxAt? {source : SourceObject F} (resolved : ResolvedOccurrence source)
    (mode : Bool) (setup : NativeSetup) (entry : PolMap) (row : Nat) (rotation : Int) :
    Option (Array F) := do
  let shifted ← setup.baseRow? row rotation
  let width ← setup.mapSectionsN["cm" ++ toString entry.stage]?
  let offset ← setup.mapOffsets[("cm" ++ toString entry.stage, false)]?
  readBlock? (resolved.params mode) .auxTrace
    (offset + shifted * width + entry.stagePos) entry.dim

/-- Generic stage>1 reader for native finalizer consumers. The actual selected
map, row, section width and post-setup offset are unchanged. Stage1 is handled
by the separate concrete FGL/raw-word route, not a generic conversion oracle. -/
def ResolvedOccurrence.cmAuxWords? {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (mapId row : Nat)
    (rotation : Int) : Option (Array F) := do
  let setup ← resolved.setup?
  let entry ← setup.cmPolsMap[mapId]?
  if 1 < entry.stage then cmAuxAt? resolved mode setup entry row rotation else none

/-- Actual cmPolsMap selection with a concrete UNPACKED FGL stage1 view of the
same primary UInt64 store. Only the requested word is reduced, not a whole
trace copy. Packed bit decoding remains unsupported here, never field-reduced
as a fake lossless representation or excluded from Root's supported scope. -/
def ResolvedOccurrence.cmWords? {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (mapId row : Nat)
    (rotation : Int) : Option (Array FGL) := do
  let setup ← resolved.setup?
  let entry ← setup.cmPolsMap[mapId]?
  if entry.stage = 1 then
    if resolved.slotData.metadata.isPacked then none
    else do
      let shifted ← setup.baseRow? row rotation
      let width ← setup.mapSectionsN["cm" ++ toString entry.stage]?
      NativeTraceWords.unpackedBlock? (resolved.params mode)
        (shifted * width + entry.stagePos) 1
  else if 1 < entry.stage then cmAuxAt? resolved mode setup entry row rotation else none

/-- Generic finalizer and concrete FGL readers share the exact same auxiliary
branch for every actual selected stage>1 entry. No trace cast is involved. -/
theorem ResolvedOccurrence.cmWords_aux {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (mapId row : Nat)
    (rotation : Int) (setup : NativeSetup) (entry : PolMap)
    (hs : resolved.setup? = some setup) (he : setup.cmPolsMap[mapId]? = some entry)
    (hstage : 1 < entry.stage) :
    resolved.cmWords? mode mapId row rotation = resolved.cmAuxWords? mode mapId row rotation := by
  have hnot : entry.stage ≠ 1 := by omega
  simp [ResolvedOccurrence.cmWords?, ResolvedOccurrence.cmAuxWords?, hs, he, hnot, hstage]

/-- The unpacked branch projects only actual requested trace words from this
same occurrence's Params; there is no independently supplied decoded image. -/
theorem ResolvedOccurrence.cmWords_unpacked_source {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (mapId row : Nat)
    (rotation : Int) (setup : NativeSetup) (entry : PolMap)
    (hs : resolved.setup? = some setup) (he : setup.cmPolsMap[mapId]? = some entry)
    (hstage : entry.stage = 1) (hpacked : resolved.slotData.metadata.isPacked = false) :
    resolved.cmWords? mode mapId row rotation = (do
      let shifted ← setup.baseRow? row rotation
      let width ← setup.mapSectionsN["cm" ++ toString entry.stage]?
      NativeTraceWords.unpackedBlock? (resolved.params mode)
        (shifted * width + entry.stagePos) 1) := by
  simp [ResolvedOccurrence.cmWords?, hs, he, hstage, hpacked]

/-- Raw primary trace access preserves every native bit, even where field
canonicalization is noninjective. Original buffer length is not cropped. -/
theorem ResolvedOccurrence.traceWord_source {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (index : Nat) :
    traceWord? (resolved.params mode) index = resolved.slotData.trace[index]? := rfl

/-- Native fixed operands push r.id directly, not constPolsMap.stagePos
(expressions_info.cpp466–474); the load is one scalar word. -/
def ResolvedOccurrence.fixedWords? {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (column row : Nat)
    (rotation : Int) : Option (Array F) := do
  let setup ← resolved.setup?
  let shifted ← setup.baseRow? row rotation
  if column < setup.nConstants then
    readBlock? (resolved.params mode) .fixed (shifted * setup.nConstants + column) 1
  else none

/-- Same live occurrence list after computed projection; this is not a supplied
roster-equality certificate or an assertion about semantic segments. -/
theorem SourceObject.context_occurrence_keys (source : SourceObject F) (context : Context F)
    (h : source.context? = some context) :
    List.ofFn (occurrenceKey context) = List.ofFn source.key := by
  cases hl : source.compiledLayouts? with
  | none => simp [SourceObject.context?, hl] at h
  | some layouts =>
    simp only [SourceObject.context?, hl, Option.map_some, Option.some.injEq] at h
    cases h
    rfl

def SourceObject.paramsAt? (source : SourceObject F) (globalSlot : Nat) (mode : Bool) :
    Option (Params F) :=
  (source.resolve? globalSlot).map (fun resolved => resolved.params mode)

/-- Computed native-slot Params and the computed existing Context select exactly
the same source arrays. The hypothesis is the result of the constructor, not a
new input certificate asserting native authenticity or row semantics. -/
theorem SourceObject.context_params (source : SourceObject F) (context : Context F)
    (h : source.context? = some context) (globalSlot : Nat) (mode : Bool) :
    source.paramsAt? globalSlot mode =
      (if hreg : globalSlot < context.registry.instances.size then
        RawSource.paramsAt? context ⟨globalSlot, hreg⟩ mode else none) := by
  cases hl : source.compiledLayouts? with
  | none => simp [SourceObject.context?, hl] at h
  | some layouts =>
    simp only [SourceObject.context?, hl, Option.map_some, Option.some.injEq] at h
    cases h
    by_cases hreg : globalSlot < source.registry.instances.size
    · by_cases hslot : globalSlot < source.slots.size
      · simp [SourceObject.paramsAt?, SourceObject.resolve?, hreg, hslot,
          ResolvedOccurrence.params, ResolvedOccurrence.slotData,
          ResolvedOccurrence.globalSlot, RawSource.paramsAt?, instanceAt?]
      · simp [SourceObject.paramsAt?, SourceObject.resolve?, hreg, hslot,
          RawSource.paramsAt?, instanceAt?]
    · simp [SourceObject.paramsAt?, SourceObject.resolve?, hreg]

/-- Ordered native AIR map id0 is word0 only because the prefix is empty.
Its stage1 width is established separately by the actual map entry. -/
theorem ResolvedOccurrence.airValueScalar_zero {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (setup : NativeSetup)
    (entry : PolMap) (hsetup : resolved.setup? = some setup)
    (hentry : setup.airValuesMap[0]? = some entry) (hstage : entry.stage = 1) :
    resolved.airValueScalar? mode 0 = resolved.slotData.airvalues[0]? := by
  simp [ResolvedOccurrence.airValueScalar?, hsetup, hentry, hstage, valueOffset_zero,
    readWord?, buffer?, ResolvedOccurrence.params, paramsOf]

/-- Group id0 uses its OWN ordered map and OWN selected slot buffer, even when
AIR id0 exists. No group FromTrace transfer or stage2 producer is invented. -/
theorem ResolvedOccurrence.airGroupValue_zero {source : SourceObject F}
    (resolved : ResolvedOccurrence source) (mode : Bool) (setup : NativeSetup)
    (entry : PolMap) (hsetup : resolved.setup? = some setup)
    (hentry : setup.airgroupValuesMap[0]? = some entry) :
    resolved.airGroupValueWords? mode 0 =
      readBlock? (resolved.params mode) .airGroupValue 0 (valueWidth entry) := by
  simp [ResolvedOccurrence.airGroupValueWords?, hsetup, hentry, valueOffset_zero]

/-- Successful bounded reads contain exactly the requested number of native
words. This is not a semantic extension-field or source-expression theorem. -/
theorem readBlock_size {F : Type} (params : Params F) (kind : FieldBufferKind)
    (offset width : Nat) (words : Array F)
    (h : readBlock? params kind offset width = some words) :
    words.size = width := by
  by_cases hz : width = 0
  · simp [readBlock?, hz] at h
  · cases hb : buffer? params kind with
    | none => simp [readBlock?, hz, hb] at h
    | some values =>
      by_cases hbound : offset + width ≤ values.size
      · simp [readBlock?, hz, hb, hbound] at h
        cases h
        simp only [Array.size_extract]
        omega
      · simp [readBlock?, hz, hb, hbound] at h

end ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
