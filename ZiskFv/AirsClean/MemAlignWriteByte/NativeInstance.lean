import ZiskFv.AirsClean.MemAlignWriteByte.NativeSourceRecovery

/-! INTERNAL full physical-domain recovery from the SAME actual native source
row0 decoder. No physical-row list/map/slice, free field reader, universal
success premise, count interpretation, or public witness interface is added.
The supported profile/stride/full-buffer facts are derived from the existing
sole getter's actual row0 evidence, not supplied as a new source validator. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeInstance

open Goldilocks RawSource.Native
open ZiskFv.AirsClean

/-- Physical domain comes from the actual generated native WriteByte profile. -/
def rowCount : Nat := (NativeTraceCells.profile .writeByte).nativeRows

/-- The source getter's actual row0 base cannot be an arbitrary row/offset. -/
theorem zero_base {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (anchor : NativeTraceCells.Row .writeByte resolved mode 0) :
    anchor.base = 0 := by
  have hbase := anchor.selected
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
      · have hzero : 0 = anchor.base := by simpa using Option.some.inj hbase
        exact hzero.symm
      · simp at hbase

/-- ONE actual source row0 establishes all source profile/stride/full-prefix
facts needed by EVERY physical index. No `∀ index, decoder succeeds` input. -/
theorem row_base_of_zero {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (anchor : NativeTraceCells.Row .writeByte resolved mode 0)
    (index : Fin rowCount) :
    NativeTraceCells.rowBase? .writeByte resolved mode index.val =
      some (index.val * resolved.slotData.metadata.nColsTrace) := by
  have hbase := anchor.selected
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
        rcases hprofile with ⟨hready, hgroup, hair, hverify, hgpu, hcount,
          _, hwidth, hstride, hpositive, hcoverage⟩
        have hindex : index.val < setup.rowCount := by
          rw [hcount]
          exact index.isLt
        unfold NativeTraceCells.rowBase?
        rw [hs]
        dsimp only [Bind.bind, Option.bind]
        rw [hc]
        dsimp only [Bind.bind, Option.bind]
        rw [if_pos ⟨hready, hgroup, hair, hverify, hgpu, hcount,
          hindex, hwidth, hstride, hpositive, hcoverage⟩]
      · simp at hbase

/-- Lazy, source-derived finite-row view; only the requested row is decoded. -/
def rowAt {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (anchor : NativeTraceCells.Row .writeByte resolved mode 0)
    (index : Fin rowCount) : NativeTraceCells.Row .writeByte resolved mode index.val :=
  ⟨index.val * resolved.slotData.metadata.nColsTrace, row_base_of_zero anchor index⟩

theorem rowAt_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (anchor : NativeTraceCells.Row .writeByte resolved mode 0) (index : Fin rowCount) :
    NativeTraceCells.row? .writeByte resolved mode index.val = some (rowAt anchor index) :=
  (rowAt anchor index).constructor_recovers

/-- The existing sole getter proves all fourteen finite coordinates defined.
Option.get uses that derived fact; there is no None→0 or arbitrary reader. -/
def cellsFromRow {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} {index : Nat}
    (view : NativeTraceCells.Row .writeByte resolved mode index) : NativeRow.Cells :=
  view.values?.get (by obtain ⟨values, h⟩ := view.values_defined; simp [h])

theorem cellsFromRow_recovers {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool} {index : Nat}
    (view : NativeTraceCells.Row .writeByte resolved mode index) :
    view.values? = some (cellsFromRow view) := by
  exact (Option.some_get _).symm

def cellsAt {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (anchor : NativeTraceCells.Row .writeByte resolved mode 0)
    (index : Fin rowCount) : NativeRow.Cells := cellsFromRow (rowAt anchor index)

theorem cellsAt_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (anchor : NativeTraceCells.Row .writeByte resolved mode 0) (index : Fin rowCount) :
    NativeSource.cells? resolved mode index.val = some (cellsAt anchor index) := by
  simp [NativeSource.cells?, rowAt_source anchor index, cellsAt,
    cellsFromRow_recovers, bind, pure]

theorem cellsAt_coordinates {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (anchor : NativeTraceCells.Row .writeByte resolved mode 0)
    (index : Fin rowCount) (column : Fin 14) :
    NativeTraceCells.cell? .writeByte resolved mode index.val column.val =
      some (cellsAt anchor index)[column.val] :=
  NativeSource.cells_coordinates resolved mode index.val (cellsAt anchor index)
    (cellsAt_source anchor index) column

/-- Recover the source's real row0 view from its actual project? result; no
second runtime decoder call is required to construct the zero-base view. -/
theorem zero_base_of_project {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool)
    (projection : NativeSource.Projection)
    (hproject : NativeSource.project? resolved mode 0 = some projection) :
    NativeTraceCells.rowBase? .writeByte resolved mode 0 = some 0 := by
  have hc := (NativeSource.project_same_source resolved mode 0 projection hproject).1
  unfold NativeSource.cells? at hc
  cases hv : NativeTraceCells.row? .writeByte resolved mode 0 with
  | none => simp [hv, bind, pure] at hc
  | some view =>
    exact view.selected.trans (congrArg some (zero_base view))

/-- Only the computed factory below constructs this internal cache. The proofs
are erased recovery evidence for the SAME decoded data, not caller inputs. -/
structure Factory {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) where
  private mk ::
  zero : NativeSource.Projection
  zeroSource : NativeSource.project? resolved mode 0 = some zero
  directs : List (Interaction FGL)
  directsSource : NativeTupleSource.directValues? (resolved.params mode) = some directs

/-- Decode row0 once and the actual three Direct hints once. Unsupported source
layouts remain None. No count/positivity/semantic-segment test is introduced. -/
def factory? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) : Option (Factory resolved mode) :=
  match hz : NativeSource.project? resolved mode 0 with
  | none => none
  | some zero =>
    let hd := NativeSource.project_directs_same_params resolved mode 0 zero hz
    let defined : (NativeTupleSource.directValues? (resolved.params mode)).isSome := by
      rw [hd]
      rfl
    some ⟨zero, hz, (NativeTupleSource.directValues? (resolved.params mode)).get defined,
      (Option.some_get defined).symm⟩

/-- The cached row0 determines its actual zero-base view; no second decode. -/
def Factory.anchor {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) :
    NativeTraceCells.Row .writeByte resolved mode 0 :=
  ⟨0, zero_base_of_project resolved mode factory.zero factory.zeroSource⟩

/-- Lazy complete physical family. AIR/GROUP values are occurrence-constant and
shared with cached row0, not reread/reconstructed for every requested row. -/
def Factory.projectAt {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) (index : Fin rowCount) :
    NativeSource.Projection :=
  if index.val = 0 then factory.zero
  else ⟨cellsAt factory.anchor index, factory.zero.values⟩

theorem Factory.projectAt_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) :
    NativeSource.project? resolved mode index.val = some (factory.projectAt index) := by
  unfold Factory.projectAt
  split
  · rename_i hzero
    simpa only [hzero] using factory.zeroSource
  · have hv := (NativeSource.project_same_source resolved mode 0 factory.zero
      factory.zeroSource).2
    simp [NativeSource.project?, cellsAt_source factory.anchor index, hv, bind, pure]

/-- Actual c7/c8/c9/c10 source operands remain load-bearing: extract the
source-decoded operation list, not a separately supplied row operation oracle. -/
def Factory.rowOperations {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) : Operations FGL :=
  ((factory.projectAt index).operations? 0).get (by
    rw [NativeSource.operations_existing_main]
    rfl)

theorem Factory.rowOperations_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) :
    (factory.projectAt index).operations? 0 = some (factory.rowOperations index) :=
  (Option.some_get _).symm

theorem Factory.rowOperations_existing_main {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) :
    factory.rowOperations index =
      NativeRow.operations (factory.projectAt index).cells 0 := by
  exact Option.some.inj ((factory.rowOperations_source index).symm.trans
    (NativeSource.operations_existing_main (factory.projectAt index) 0))

theorem Factory.row_spec {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) (env : Environment FGL)
    (hholds : ConstraintsHold.Soundness env (factory.rowOperations index)) :
    Spec (factory.projectAt index).localRow :=
  NativeSource.local_spec (factory.projectAt index) 0 (factory.rowOperations index)
    env (factory.rowOperations_source index) hholds

/-- Literal embedding, not another source interpreter: all channels, message
coordinates, unrestricted field weights and guarantee flags come from the
actual successfully decoded Direct interactions. -/
def literalInteraction (interaction : Interaction FGL) : AbstractInteraction FGL where
  channel := interaction.channel
  mult := .const interaction.mult
  msg := interaction.msgVector.map Expression.const
  assumeGuarantees := interaction.assumeGuarantees

theorem literalInteraction_eval (interaction : Interaction FGL) (env : Environment FGL) :
    (literalInteraction interaction).eval env = interaction := by
  cases interaction
  simp [literalInteraction, AbstractInteraction.eval, Interaction.msgVector,
    Vector.map_map, Function.comp_def, circuit_norm]

/-- A finite list of exactly three source Direct operations, emitted ONCE by
the separate branch below, never once per physical row. Zero weights retained. -/
def Factory.onceOperations {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) : Operations FGL :=
  factory.directs.map (fun interaction => Operation.interact (literalInteraction interaction))

theorem Factory.directs_eq {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) :
    factory.directs = NativeTupleSource.directValues factory.zero.values.padding :=
  Option.some.inj (factory.directsSource.symm.trans
    (NativeSource.project_directs_same_params resolved mode 0 factory.zero factory.zeroSource))

theorem Factory.onceOperations_values {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (env : Environment FGL) :
    (factory.onceOperations.interactions.map (fun interaction => interaction.eval env)) =
      factory.directs := by
  simp [Factory.onceOperations, factory.directs_eq, NativeTupleSource.directValues,
    Operations.interactions, literalInteraction_eval]

theorem Factory.onceOperations_count {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) : factory.onceOperations.length = 3 := by
  rw [Factory.onceOperations, List.length_map, factory.directs_eq]
  rfl

theorem Factory.once_multiplicities {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) :
    factory.directs.map Interaction.mult =
      [factory.zero.values.padding, -factory.zero.values.padding, factory.zero.values.padding] := by
  rw [factory.directs_eq]
  rfl

theorem factory_constructible {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool)
    (zero : NativeSource.Projection)
    (hzero : NativeSource.project? resolved mode 0 = some zero) :
    ∃ factory, factory? resolved mode = some factory := by
  unfold factory?
  split
  · rename_i hnone
    simp only [hnone] at hzero
    cases hzero
  · exact ⟨_, rfl⟩

theorem Factory.coordinates {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) (column : Fin 14) :
    NativeTraceCells.cell? .writeByte resolved mode index.val column.val =
      some (factory.projectAt index).cells[column.val] :=
  NativeSource.project_coordinates resolved mode index.val (factory.projectAt index)
    (factory.projectAt_source index) column

theorem Factory.padding_source {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) :
    resolved.slotData.airvalues[0]? = some factory.zero.values.padding :=
  NativeSource.project_padding_same_slot resolved mode 0 factory.zero factory.zeroSource

/-- Neither source zero nor a negative field scalar changes the three-message
roster; these are scalar cases, not "honest count" restrictions. -/
theorem Factory.zero_directs {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (hz : factory.zero.values.padding = 0) :
    factory.directs.map Interaction.mult = [0, 0, 0] ∧
      factory.onceOperations.length = 3 := by
  constructor
  · simpa [hz] using factory.once_multiplicities
  · exact factory.onceOperations_count

theorem Factory.negative_one_directs {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (hn : factory.zero.values.padding = -1) :
    factory.directs.map Interaction.mult = [-1, 1, -1] ∧
      factory.onceOperations.length = 3 := by
  constructor
  · simpa [hn] using factory.once_multiplicities
  · exact factory.onceOperations_count

/-- The disjoint domain is ALL physical rows plus ONE Direct occurrence. There
is no full-N list/map/slice and no scalar-to-row-count interpretation. -/
abbrev Emission := Sum (Fin rowCount) Unit

def Factory.operationsAt {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) : Emission → Operations FGL
  | .inl index => factory.rowOperations index
  | .inr () => factory.onceOperations

theorem row_ne_once (index : Fin rowCount) : (Sum.inl index : Emission) ≠ .inr () := by
  intro h
  cases h

/-- Computed lazy final-registry roster. Missing local slots/unsupported
layouts remain None; no caller supplies a roster, field reader or success
certificate. Registry position is occurrence identity, NOT semantic segment. -/
def sourceInstances? (source : SourceObject FGL) (mode : Bool)
    (index : source.Occurrence) :
    Option (Σ resolved : ResolvedOccurrence source, Factory resolved mode) := do
  let resolved ← source.resolve? index.val
  let factory ← factory? resolved mode
  return ⟨resolved, factory⟩

theorem sourceInstances_globalSlot (source : SourceObject FGL) (mode : Bool)
    (index : source.Occurrence)
    (entry : Σ resolved : ResolvedOccurrence source, Factory resolved mode)
    (h : sourceInstances? source mode index = some entry) :
    entry.1.globalSlot = index.val := by
  unfold sourceInstances? at h
  cases hr : source.resolve? index.val with
  | none => simp [hr, bind, pure] at h
  | some resolved =>
    cases hf : factory? resolved mode with
    | none => simp [hr, hf, bind, pure] at h
    | some factory =>
      have heq : (⟨resolved, factory⟩ :
          Σ resolved : ResolvedOccurrence source, Factory resolved mode) = entry := by
        simpa [hr, hf, bind, pure] using h
      cases heq
      exact source.resolve_globalSlot index.val resolved hr

/-- Distinct final-registry occurrences cannot acquire the same occurrence key.
This is not a claimed native-to-Accepted occurrence/balance binding. -/
theorem sourceInstances_identity (source : SourceObject FGL) (mode : Bool)
    (left right : source.Occurrence)
    (first second : Σ resolved : ResolvedOccurrence source, Factory resolved mode)
    (hf : sourceInstances? source mode left = some first)
    (hs : sourceInstances? source mode right = some second)
    (hkey : first.1.key = second.1.key) : left = right := by
  apply Fin.ext
  calc
    left.val = first.1.globalSlot := (sourceInstances_globalSlot source mode left first hf).symm
    _ = second.1.globalSlot := congrArg RawSource.OccurrenceKey.globalSlot hkey
    _ = right.val := sourceInstances_globalSlot source mode right second hs

end ZiskFv.AirsClean.MemAlignWriteByte.NativeInstance
