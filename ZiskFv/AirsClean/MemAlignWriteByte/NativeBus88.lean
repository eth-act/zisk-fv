import ZiskFv.AirsClean.MemAlignWriteByte.NativeInstance

/-! INTERNAL joint source-family bus88 projection. Every physical row retains
its actual ordered negative-unit pull. The separate once-only source Direct
branch has no bus88 contribution because all three real channels are MemoryBus,
not because of a padding/count interpretation or cancellation convention.

This does NOT manufacture provider balance. The existing DualBytePackedSource
provider has the real fixed 65536 tuples and unrestricted source-location
weights. Its location-function witness is not yet derived from THIS native
SourceObject: source88 is VirtualTable0 (registry group0/AIR33), physical lane2,
rows262144+i, not a fresh fallback table. Binding its actual multiplicity cells
and registry-selected native setup/raw store, then the native global sum/once
roster to the existing balance model, remains necessary. Native ABI/PIL-to-setup
materialization, stage2 finalizer enforcement and Accepted embedding are not
proved or taken as new caller certificates here. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeBus88

open Goldilocks RawSource.Native
open ZiskFv.AirsClean
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.DualByte (DualByteChannel)
open NativeInstance

/-- Actual distinct channel identity, independent of any scalar's value. -/
theorem memory_ne_dual : (MemBusChannel.toRaw : RawChannel FGL) ≠ DualByteChannel.toRaw := by
  intro h
  have hn := congrArg (fun channel : RawChannel FGL => channel.name) h
  exact (by decide : ("MemoryBus" : String) ≠ "DualByte88") hn

/-- All four source row operations, including both aligned pulls and the
selected STORE push, remain present before selecting channel88. -/
theorem row_values {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) (index : Fin rowCount)
    (env : Environment FGL) :
    (factory.rowOperations index).interactionValues env =
      NativeRow.interactionValues (factory.projectAt index).cells :=
  NativeSource.operations_row_interactions (factory.projectAt index) 0
    (factory.rowOperations index) env (factory.rowOperations_source index)

/-- Actual compiled-operation projection, not a detached requested message. -/
theorem row88 {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) (index : Fin rowCount)
    (env : Environment FGL) :
    (factory.rowOperations index).interactionValuesWith DualByteChannel.toRaw env =
      [DualByteChannel.pulledValue (NativeRow.dualRead (factory.projectAt index).cells)] := by
  classical
  rw [Operations.interactionValuesWith_eq_filter, row_values factory index env]
  simp [NativeRow.interactionValues, Channel.pulledValue, Channel.pushedValue,
    memory_ne_dual]

/-- The source's c8 operand order is byte_value (cell9), value_8b (cell8).
Multiplicity stays exactly -1, including source zeros in either byte cell. -/
theorem row88_schema {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) (index : Fin rowCount) :
    let pull := DualByteChannel.pulledValue (NativeRow.dualRead (factory.projectAt index).cells)
    pull.mult = -1 ∧
      pull.msg = #[(factory.projectAt index).cells[9], (factory.projectAt index).cells[8]] ∧
      pull.assumeGuarantees = true := by
  exact ⟨rfl, rfl, rfl⟩

/-- Both ordered operands come from the SAME original physical row/store. -/
theorem row88_source_coordinates {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (index : Fin rowCount) :
    NativeTraceCells.cell? .writeByte resolved mode index.val 9 =
        some (factory.projectAt index).cells[9] ∧
      NativeTraceCells.cell? .writeByte resolved mode index.val 8 =
        some (factory.projectAt index).cells[8] :=
  ⟨factory.coordinates index ⟨9, by decide⟩, factory.coordinates index ⟨8, by decide⟩⟩

/-- All real Direct messages are retained as three MemoryBus contributions.
In particular source zero is not an empty roster and raw -1 is not a count. -/
theorem once_channels {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) :
    factory.directs.map Interaction.channel =
      [MemBusChannel.toRaw, MemBusChannel.toRaw, MemBusChannel.toRaw] := by
  rw [factory.directs_eq]
  rfl

/-- Channel disjointness, NOT a blanket ignored/canceled Direct contribution. -/
theorem once88 {source : SourceObject FGL} {resolved : ResolvedOccurrence source}
    {mode : Bool} (factory : Factory resolved mode) (env : Environment FGL) :
    factory.onceOperations.interactionValuesWith DualByteChannel.toRaw env = [] := by
  classical
  rw [Operations.interactionValuesWith_eq_filter]
  change (factory.onceOperations.interactions.map (fun interaction => interaction.eval env)).filter
    (fun interaction => interaction.channel = DualByteChannel.toRaw) = []
  rw [factory.onceOperations_values, factory.directs_eq]
  simp [NativeTupleSource.directValues, Channel.pushedIfValue, memory_ne_dual]

/-- Computed lazy projection of the WHOLE disjoint full-N-plus-once family.
The existing framework's channel filter is noncomputable, not a free reader. -/
noncomputable def channel88Family {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (env : Environment FGL) :
    Emission → List (Interaction FGL) :=
  fun emission => (factory.operationsAt emission).interactionValuesWith DualByteChannel.toRaw env

theorem channel88Family_exact {source : SourceObject FGL}
    {resolved : ResolvedOccurrence source} {mode : Bool}
    (factory : Factory resolved mode) (env : Environment FGL) :
    channel88Family factory env = (fun
      | .inl index =>
        [DualByteChannel.pulledValue (NativeRow.dualRead (factory.projectAt index).cells)]
      | .inr () => []) := by
  funext emission
  cases emission with
  | inl index => exact row88 factory index env
  | inr once => cases once; exact once88 factory env

/-- Actual final-registry-indexed partial source image, computed from source
and mode alone. No arbitrary all-row field function/roster is supplied. None
continues to mean unsupported/missing source data, NOT a Root scope exclusion. -/
noncomputable def sourceChannel88 (source : SourceObject FGL) (mode : Bool)
    (env : Environment FGL) (occurrence : source.Occurrence) :
    Option (Emission → List (Interaction FGL)) :=
  (sourceInstances? source mode occurrence).map (fun entry => channel88Family entry.2 env)

theorem sourceChannel88_exact (source : SourceObject FGL) (mode : Bool)
    (env : Environment FGL) (occurrence : source.Occurrence)
    (entry : Σ resolved : ResolvedOccurrence source, Factory resolved mode)
    (h : sourceInstances? source mode occurrence = some entry) :
    sourceChannel88 source mode env occurrence = some (fun
      | .inl index =>
        [DualByteChannel.pulledValue (NativeRow.dualRead (entry.2.projectAt index).cells)]
      | .inr () => []) := by
  simp only [sourceChannel88, h, Option.map_some, channel88Family_exact]

end ZiskFv.AirsClean.MemAlignWriteByte.NativeBus88
