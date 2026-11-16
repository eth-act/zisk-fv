import Source415DomainComparison.ReverseProjection

/-!
# Six ordered streams of the arbitrary reverse projection

These are equalities of unfiltered raw interaction lists. In particular both
zero interactions and the exact interaction-count/no-overflow guard transfer.
Source-provider silence depends only on its component, never its prefix height.
-/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Channels.OperationBus
open ZiskFv.Channels.MemoryBus
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable
open ZiskFv.Channels.SpecifiedRanges
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)

variable {p : Nat} {program : Program p}

private theorem arbitrary_extension_source_old_stream (new : NewWitness p program)
    (channel : RawChannel FGL) (hc : channel ∈ oldFinishedChannels) :
    (newTable new 14).interactionsWith channel = [] := by
  apply BinaryTableBalance.interactionsWith_nil_of_channel_names
  rw [newTable_component]
  change channel.name ∉ BinaryExtensionTableSlice.sourceComponent.circuit.channels.map (·.name)
  simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem arbitrary_binary_source_old_stream (new : NewWitness p program)
    (channel : RawChannel FGL) (hc : channel ∈ oldFinishedChannels) :
    (newTable new 15).interactionsWith channel = [] := by
  apply BinaryTableBalance.interactionsWith_nil_of_channel_names
  rw [newTable_component]
  change channel.name ∉ BinaryTableSlice.sourceComponent.circuit.channels.map (·.name)
  simp only [oldFinishedChannels, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Exact source order, messages and raw multiplicities on each old channel. -/
theorem projected_old_channel_stream (new : NewWitness p program)
    (channel : RawChannel FGL)
    (hc : channel ∈ (Legacy45.fullRv64imEnsemble p program).ensemble.channels) :
    (projectedWitness new).interactionsWith channel = new.interactionsWith channel := by
  rw [old_finished_channels] at hc
  have hb := binary_consumer_old_stream (projectedWitness new) channel hc
  rw [projected_binary_consumer] at hb
  have binary : (binaryStaticTable new).interactionsWith channel =
      (newTable new 12).interactionsWith channel := hb.symm
  have he := extension_consumer_old_stream (projectedWitness new) channel hc
  rw [projected_extension_consumer] at he
  have extension : (extensionStaticTable new).interactionsWith channel =
      (newTable new 11).interactionsWith channel := he.symm
  change ((projectedWitness new).verifierTable :: projectedTables new).flatMap
      (fun table => table.interactionsWith channel) =
    (new.verifierTable :: new.tables).flatMap (fun table => table.interactionsWith channel)
  rw [projected_verifierTable, new_tables_eq]
  simp only [projectedTables, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
    binary, extension, arbitrary_extension_source_old_stream new channel hc,
    arbitrary_binary_source_old_stream new channel hc,
    List.nil_append, List.append_nil, List.append_assoc]

/-- Full old balance, including the original raw-list length bound. -/
theorem projected_balanced (new : NewWitness p program) (hb : new.BalancedChannels) :
    (projectedWitness new).BalancedChannels := by
  intro channel hc
  have hn : channel ∈ (fullRv64imEnsemble p program).ensemble.channels := by
    rw [current_finished_channels]
    exact List.mem_append_right _ hc
  have h := hb channel hn
  change BalancedInteractions (new.interactionsWith channel) at h
  change BalancedInteractions ((projectedWitness new).interactionsWith channel)
  rw [projected_old_channel_stream new channel hc]
  exact h

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
