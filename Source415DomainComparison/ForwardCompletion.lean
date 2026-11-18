import Source415DomainComparison.ForwardRequests
import Source415DomainComparison.OldOperationCounts
import Source415DomainComparison.TransitionCompatibility
import Source415DomainComparison.ReplayFieldPreservation

/-! Existence of an accepted source18 completion of each accepted old16 trace.
The shared packed witness is freshly completed by request histograms; there is
no equality claim about an arbitrary previously committed provider witness.
The original physical execution tables, prover data, public input, verifier,
selected replay table, guard, coverage, and universal Main height are retained. -/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open PackedVirtualTableSources
open Extraction.PackedVirtualTables
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable

variable {p : Nat} {program : Program p}

noncomputable def forwardRaw (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) (base : Witness FGL) : Witness FGL :=
  physicalOfRequests base (oldBinaryRequests old hc hb) (oldExtensionRequests old hc hb)

/-- Exact source projection qualification: only the two requested source
regions change. Every other selected source view and every unowned cell is
preserved. Counts are raw field values, including zero at unused indices. -/
theorem forwardRaw_projections (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) (base : Witness FGL) :
    project (forwardRaw old hc hb base) source88 = project base source88 ∧
    project (forwardRaw old hc hb base) source330 = project base source330 ∧
    project (forwardRaw old hc hb base) source331 = project base source331 ∧
    project (forwardRaw old hc hb base) source124 =
      (fun i => (((oldExtensionRequests old hc hb).map extensionIndex).count i : FGL)) ∧
    project (forwardRaw old hc hb base) source125 =
      (fun i => (((oldBinaryRequests old hc hb).map binaryIndex).count i : FGL)) ∧
    (∀ location, sourceAt location = none →
      forwardRaw old hc hb base location = base location) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact project88_physicalOfLogical _ _
  · exact project330_physicalOfLogical _ _
  · exact project331_physicalOfLogical _ _
  · exact project124_physicalOfLogical _ _
  · exact project125_physicalOfLogical _ _
  · exact fun location h => requests_preserve_unrelated base _ _ location h

private theorem oldTable_lookup_silent (old : OldWitness p program) (i : Fin 15)
    (channel : RawChannel FGL)
    (hchannel : channel = BinaryTableChannel.toRaw ∨
      channel = BinaryExtensionTableChannel.toRaw) :
    (oldTable old i).interactionsWith channel = [] := by
  apply BinaryTableBalance.interactionsWith_nil_of_channel_names
  rw [oldTable_component]
  rcases hchannel with rfl | rfl <;> fin_cases i <;>
    exact of_decide_eq_true (by with_unfolding_all rfl)

private theorem oldVerifier_lookup_silent (old : OldWitness p program)
    (channel : RawChannel FGL) : old.verifierTable.interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change channel ∉ ([] : List (RawChannel FGL))
  simp

/-- Actual ordered allTables streams: consumer rows precede the full canonical
producer. Neither stream is filtered at zero multiplicity. -/
theorem completed_binary_request_stream (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) (base : Witness FGL) :
    (completedWitness old (forwardRaw old hc hb base)).interactionsWith
        BinaryTableChannel.toRaw =
      consumedSourceRequests BinaryTableChannel
        (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val)
        (oldBinaryRequests old hc hb) ++
      countedSourceInteractions BinaryTableChannel
        (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val)
        (oldBinaryRequests old hc hb) := by
  have he : (extensionConsumerTable old).interactionsWith BinaryTableChannel.toRaw = [] := by
    apply BinaryTableBalance.interactionsWith_nil_of_channel_names
    exact of_decide_eq_true (by with_unfolding_all rfl)
  have hp := extensionProviderTable_other_channel
    (forwardRaw old hc hb base) old.data BinaryTableChannel.toRaw (by decide)
  have hprovider :
      (binaryProviderTable (forwardRaw old hc hb base) old.data).interactionsWith
        BinaryTableChannel.toRaw =
      countedSourceInteractions BinaryTableChannel
        (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val)
        (oldBinaryRequests old hc hb) := by
    rw [binaryProviderTable_interactionsWith]
    exact binaryInteractions_physicalOfRequests base
      (oldBinaryRequests old hc hb) (oldExtensionRequests old hc hb)
  change ((completedWitness old _).verifierTable :: completedTables old _).flatMap
    (fun table => table.interactionsWith BinaryTableChannel.toRaw) = _
  rw [completedWitness_verifierTable, List.flatMap_cons, oldVerifier_lookup_silent, List.nil_append]
  have spine := flatMap_seventeen_consumer12_source15
    (fun table => table.interactionsWith BinaryTableChannel.toRaw)
    (oldTable old 0) (oldTable old 1) (oldTable old 2) (oldTable old 3)
    (oldTable old 4) (oldTable old 5) (oldTable old 6) (oldTable old 7)
    (oldTable old 8) (oldTable old 9) (oldTable old 10)
    (extensionConsumerTable old) (binaryConsumerTable old) (oldTable old 13)
    (extensionProviderTable (forwardRaw old hc hb base) old.data)
    (binaryProviderTable (forwardRaw old hc hb base) old.data) (oldTable old 14)
    (consumedSourceRequests BinaryTableChannel
      (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val)
      (oldBinaryRequests old hc hb))
    (oldTable_lookup_silent old 0 _ (Or.inl rfl))
    (oldTable_lookup_silent old 1 _ (Or.inl rfl))
    (oldTable_lookup_silent old 2 _ (Or.inl rfl))
    (oldTable_lookup_silent old 3 _ (Or.inl rfl))
    (oldTable_lookup_silent old 4 _ (Or.inl rfl))
    (oldTable_lookup_silent old 5 _ (Or.inl rfl))
    (oldTable_lookup_silent old 6 _ (Or.inl rfl))
    (oldTable_lookup_silent old 7 _ (Or.inl rfl))
    (oldTable_lookup_silent old 8 _ (Or.inl rfl))
    (oldTable_lookup_silent old 9 _ (Or.inl rfl))
    (oldTable_lookup_silent old 10 _ (Or.inl rfl))
    he (binary_consumer_requests old hc hb)
    (oldTable_lookup_silent old 13 _ (Or.inl rfl)) hp
    (oldTable_lookup_silent old 14 _ (Or.inl rfl))
  exact spine.trans (congrArg (fun provider =>
    consumedSourceRequests BinaryTableChannel
      (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val)
      (oldBinaryRequests old hc hb) ++ provider) hprovider)

theorem completed_extension_request_stream (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) (base : Witness FGL) :
    (completedWitness old (forwardRaw old hc hb base)).interactionsWith
        BinaryExtensionTableChannel.toRaw =
      consumedSourceRequests BinaryExtensionTableChannel
        (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val)
        (oldExtensionRequests old hc hb) ++
      countedSourceInteractions BinaryExtensionTableChannel
        (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val)
        (oldExtensionRequests old hc hb) := by
  have he : (binaryConsumerTable old).interactionsWith BinaryExtensionTableChannel.toRaw = [] := by
    apply BinaryTableBalance.interactionsWith_nil_of_channel_names
    exact of_decide_eq_true (by with_unfolding_all rfl)
  have hp := binaryProviderTable_other_channel
    (forwardRaw old hc hb base) old.data BinaryExtensionTableChannel.toRaw (by decide)
  have hprovider :
      (extensionProviderTable (forwardRaw old hc hb base) old.data).interactionsWith
        BinaryExtensionTableChannel.toRaw =
      countedSourceInteractions BinaryExtensionTableChannel
        (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val)
        (oldExtensionRequests old hc hb) := by
    rw [extensionProviderTable_interactionsWith]
    exact extensionInteractions_physicalOfRequests base
      (oldBinaryRequests old hc hb) (oldExtensionRequests old hc hb)
  change ((completedWitness old _).verifierTable :: completedTables old _).flatMap
    (fun table => table.interactionsWith BinaryExtensionTableChannel.toRaw) = _
  rw [completedWitness_verifierTable, List.flatMap_cons, oldVerifier_lookup_silent, List.nil_append]
  have spine := flatMap_seventeen_consumer11_source14
    (fun table => table.interactionsWith BinaryExtensionTableChannel.toRaw)
    (oldTable old 0) (oldTable old 1) (oldTable old 2) (oldTable old 3)
    (oldTable old 4) (oldTable old 5) (oldTable old 6) (oldTable old 7)
    (oldTable old 8) (oldTable old 9) (oldTable old 10)
    (extensionConsumerTable old) (binaryConsumerTable old) (oldTable old 13)
    (extensionProviderTable (forwardRaw old hc hb base) old.data)
    (binaryProviderTable (forwardRaw old hc hb base) old.data) (oldTable old 14)
    (consumedSourceRequests BinaryExtensionTableChannel
      (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val)
      (oldExtensionRequests old hc hb))
    (oldTable_lookup_silent old 0 _ (Or.inr rfl))
    (oldTable_lookup_silent old 1 _ (Or.inr rfl))
    (oldTable_lookup_silent old 2 _ (Or.inr rfl))
    (oldTable_lookup_silent old 3 _ (Or.inr rfl))
    (oldTable_lookup_silent old 4 _ (Or.inr rfl))
    (oldTable_lookup_silent old 5 _ (Or.inr rfl))
    (oldTable_lookup_silent old 6 _ (Or.inr rfl))
    (oldTable_lookup_silent old 7 _ (Or.inr rfl))
    (oldTable_lookup_silent old 8 _ (Or.inr rfl))
    (oldTable_lookup_silent old 9 _ (Or.inr rfl))
    (oldTable_lookup_silent old 10 _ (Or.inr rfl))
    (extension_consumer_requests old hc hb) he
    (oldTable_lookup_silent old 13 _ (Or.inr rfl)) hp
    (oldTable_lookup_silent old 14 _ (Or.inr rfl))
  exact spine.trans (congrArg (fun provider =>
    consumedSourceRequests BinaryExtensionTableChannel
      (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val)
      (oldExtensionRequests old hc hb) ++ provider) hprovider)

private theorem consumed_counted_balanced {Message : TypeMap} [ProvableType Message]
    {n : Nat} (channel : Channel FGL Message) (row : Fin n → Message FGL)
    (requests : List (Fin n)) (bound : n + requests.length < ringChar FGL) :
    BalancedInteractions (consumedSourceRequests channel row requests ++
      countedSourceInteractions channel row requests) := by
  refine ⟨Or.inl ?_, ?_⟩
  · simpa [consumedSourceRequests, countedSourceInteractions, Nat.add_comm] using bound
  · intro message
    rw [balanceOf_append, consumedSourceRequests_balanceOf,
      countedSourceInteractions_balanceOf, neg_add_cancel]

theorem completed_balanced_channels (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) (base : Witness FGL) :
    (completedWitness old (forwardRaw old hc hb base)).BalancedChannels := by
  intro channel hchannel
  rw [current_finished_channels] at hchannel
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hchannel
  change BalancedInteractions ((completedWitness old (forwardRaw old hc hb base)).interactionsWith channel)
  rcases hchannel with (rfl | rfl) | hold
  · rw [completed_extension_request_stream]
    apply consumed_counted_balanced
    rw [oldExtensionRequests_length]
    exact old_extension_request_count_bound old hc hb
  · rw [completed_binary_request_stream]
    apply consumed_counted_balanced
    rw [oldBinaryRequests_length]
    exact old_binary_request_count_bound old hc hb
  · rw [completed_old_channel_stream old _ channel hold]
    exact hb channel hold

end ZiskFv.AirsClean.FullEnsemble.DomainComparison

namespace ZiskFv.Compliance.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.FullEnsemble.DomainComparison
open PackedVirtualTableSources

/-- A forward existence construction, not equality with an arbitrary source18
provider commitment. Both full source tables read the same completed raw. -/
noncomputable def forwardAccepted {n : Nat} (trace : Legacy45.AcceptedZiskTrace n)
    (base : Witness FGL) : Legacy457.AcceptedZiskTrace n :=
  let raw := forwardRaw trace.witness trace.constraints_hold trace.channels_balanced base
  { programLength := trace.programLength
    program := trace.program
    witness := completedWitness trace.witness raw
    constraints_hold := completed_constraints trace.witness raw trace.constraints_hold
    channels_balanced := completed_balanced_channels trace.witness
      trace.constraints_hold trace.channels_balanced base
    mem_replay_table := fun guard =>
      ⟨(trace.mem_replay_table
        ((completed_mutableMemPresent trace.witness raw).mpr guard)).1,
        completed_selected_replay_table trace raw guard⟩
    mem_replay_source_covers := completed_replay_source_covers trace raw
    transitions_hold := completed_transitions trace.witness raw trace.transitions_hold
    cyclic_successor_transitions_hold := completed_cyclic_transitions
      trace.witness raw trace.cyclic_successor_transitions_hold
    main_height := completed_universal_main_height trace raw }

theorem forwardAccepted_witness {n : Nat} (trace : Legacy45.AcceptedZiskTrace n)
    (base : Witness FGL) :
    (forwardAccepted trace base).witness = completedWitness trace.witness
      (forwardRaw trace.witness trace.constraints_hold trace.channels_balanced base) := rfl

theorem forwardAccepted_selected_replay {n : Nat} (trace : Legacy45.AcceptedZiskTrace n)
    (base : Witness FGL) (guard : Legacy457.MutableMemPresent (forwardAccepted trace base).witness) :
    ((forwardAccepted trace base).mem_replay_table guard).1 =
      (trace.mem_replay_table ((completed_mutableMemPresent trace.witness
        (forwardRaw trace.witness trace.constraints_hold trace.channels_balanced base)).mpr guard)).1 := rfl

end ZiskFv.Compliance.DomainComparison
