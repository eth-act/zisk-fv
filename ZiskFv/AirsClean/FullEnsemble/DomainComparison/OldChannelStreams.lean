import ZiskFv.AirsClean.FullEnsemble.DomainComparison.RowCompatibility
import ZiskFv.AirsClean.FullEnsemble.Balance.BinaryTableWitnessConstruction

/-! Exact ordered streams for the actual witness splice. The reference is
`oldexactsourcecompare`: Old16 freezes 45e618f2cf08bf3fcd47cbc8c74c870cd88bede7,
whereas the current physical roster is the source415 roster. No interaction is
filtered by multiplicity: in particular zero-valued raw multiplicities survive.
-/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.OperationBus
open ZiskFv.Channels.MemoryBus
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable
open ZiskFv.Channels.SpecifiedRanges
open PackedVirtualTableSources
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)

variable {p : Nat} {program : Program p}

/-- Source order, not a set of channels. -/
def oldFinishedChannels : List (RawChannel FGL) :=
  [RegisterStepRangeChannel.toRaw, MemAlignRangeChannel.toRaw,
   MemBusChannel.toRaw, OpBusChannel.toRaw, MemAlignRomChannel.toRaw,
   SpecifiedRangesSliceChannel.toRaw]

theorem old_finished_channels :
    (Legacy45.fullRv64imEnsemble p program).ensemble.channels = oldFinishedChannels := by
  simp [Legacy45.fullRv64imEnsemble, Legacy45.fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels, oldFinishedChannels]

theorem current_finished_channels :
    (fullRv64imEnsemble p program).ensemble.channels =
      [BinaryExtensionTableChannel.toRaw, BinaryTableChannel.toRaw] ++
        (Legacy45.fullRv64imEnsemble p program).ensemble.channels := by
  rw [old_finished_channels]
  simp [fullRv64imEnsemble, fullRv64imSoundEnsemble,
    SoundEnsemble.toFormal, SoundEnsemble.addFinishedChannel_channels,
    SoundEnsemble.addTable_channels, SoundEnsemble.empty_channels, oldFinishedChannels]

private theorem silent_of_names (table : Table FGL) (channel : RawChannel FGL)
    (h : channel.name ∉ table.component.circuit.channels.map (·.name)) :
    table.interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro hm
  exact h (List.mem_map_of_mem (f := fun c : RawChannel FGL => c.name) hm)

/-- The real fixed providers expose only their new lookup channel. -/
theorem extension_provider_old_stream (old : OldWitness p program)
    (raw : Witness FGL) (channel : RawChannel FGL)
    (hc : channel ∈ oldFinishedChannels) :
    (extensionProviderTable raw old.data).interactionsWith channel = [] := by
  apply silent_of_names
  simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [extensionProviderTable, BinaryExtensionTableSlice.sourceComponent,
      BinaryExtensionTableSlice.sourceCircuit, circuit_norm,
      RegisterStepRangeChannel, MemAlignRangeChannel, MemBusChannel, OpBusChannel,
      MemAlignRomChannel, SpecifiedRangesSliceChannel, BinaryExtensionTableChannel]

theorem binary_provider_old_stream (old : OldWitness p program)
    (raw : Witness FGL) (channel : RawChannel FGL)
    (hc : channel ∈ oldFinishedChannels) :
    (binaryProviderTable raw old.data).interactionsWith channel = [] := by
  apply silent_of_names
  simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [binaryProviderTable, BinaryTableSlice.sourceComponent,
      BinaryTableSlice.sourceCircuit, circuit_norm,
      RegisterStepRangeChannel, MemAlignRangeChannel, MemBusChannel, OpBusChannel,
      MemAlignRomChannel, SpecifiedRangesSliceChannel, BinaryTableChannel]

theorem binary_consumer_old_stream (old : OldWitness p program)
    (channel : RawChannel FGL) (hc : channel ∈ oldFinishedChannels) :
    (binaryConsumerTable old).interactionsWith channel =
      (oldTable old 12).interactionsWith channel := by
  by_cases hop : channel = OpBusChannel.toRaw
  · subst channel
    simp only [Table.interactionsWith, binaryConsumerTable_table,
      Operations.interactionValuesWith_eq_map]
    have hcomp := old_binary_component old
    simp only [binaryConsumerTable, hcomp,
      FullEnsemble.binary_consumer_interactionsWith_opBus,
      Binary.staticLookupComponent_interactionsWith_opBus]
    rfl
  · have hn : channel.name ≠ OpBusChannel.toRaw.name := by
      simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact False.elim (hop rfl) | decide
    have hnew := silent_of_names (binaryConsumerTable old) channel (by
      simp [binaryConsumerTable, Binary.tableConsumerComponent,
        Binary.tableConsumerCircuit, circuit_norm, hn]
      all_goals
        simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hold := silent_of_names (oldTable old 12) channel (by
      rw [old_binary_component]
      simpa [Binary.staticLookupComponent, Binary.staticLookupCircuit, circuit_norm] using hn)
    rw [hnew, hold]

theorem extension_consumer_old_stream (old : OldWitness p program)
    (channel : RawChannel FGL) (hc : channel ∈ oldFinishedChannels) :
    (extensionConsumerTable old).interactionsWith channel =
      (oldTable old 11).interactionsWith channel := by
  by_cases hop : channel = OpBusChannel.toRaw
  · subst channel
    simp only [Table.interactionsWith, extensionConsumerTable_table,
      Operations.interactionValuesWith_eq_map]
    have hcomp := old_extension_component old
    simp only [extensionConsumerTable, hcomp,
      FullEnsemble.extension_consumer_interactionsWith_opBus,
      BinaryExtension.shiftStaticLookupComponent_interactionsWith_opBus]
    rfl
  · have hn : channel.name ≠ OpBusChannel.toRaw.name := by
      simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact False.elim (hop rfl) | decide
    have hnew := silent_of_names (extensionConsumerTable old) channel (by
      simp [extensionConsumerTable, BinaryExtension.shiftTableConsumerComponent,
        BinaryExtension.shiftTableConsumerCircuit, circuit_norm, hn]
      all_goals
        simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have hold := silent_of_names (oldTable old 11) channel (by
      rw [old_extension_component]
      simpa [BinaryExtension.shiftStaticLookupComponent,
        BinaryExtension.shiftStaticLookupCircuit, circuit_norm] using hn)
    rw [hnew, hold]

/-- Exact list equality on the actual allTables stream: row order, table order,
messages, raw multiplicities, and zero interactions are all retained. -/
theorem completed_old_channel_stream (old : OldWitness p program)
    (raw : Witness FGL) (channel : RawChannel FGL)
    (hc : channel ∈ (Legacy45.fullRv64imEnsemble p program).ensemble.channels) :
    (completedWitness old raw).interactionsWith channel = old.interactionsWith channel := by
  rw [old_finished_channels] at hc
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables,
    completedWitness_tables, completedWitness_verifierTable, old_tables_eq,
    completedTables, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
    binary_consumer_old_stream old channel hc,
    extension_consumer_old_stream old channel hc,
    binary_provider_old_stream old raw channel hc,
    extension_provider_old_stream old raw channel hc,
    List.nil_append, List.append_nil]

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
