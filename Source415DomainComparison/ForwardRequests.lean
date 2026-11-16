import Source415DomainComparison.OldChannelStreams

/-! Forward requests are extracted from the frozen witness's actual static
lookup specifications. Every physical row contributes all eight routes, in
order, including repeated messages. No source certificate is an input. -/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open BinaryTableBalance
open PackedVirtualTableSources
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable

variable {p : Nat} {program : Program p}

def oldBinaryMessages (old : OldWitness p program) : List (BinaryTableMessage FGL) :=
  (oldTable old 12).table.flatMap fun row => List.ofFn fun i : Fin 8 =>
    binaryMessageRow (Binary.staticLookupComponent.rowInput
      ((oldTable old 12).environment row)) i

def oldExtensionMessages (old : OldWitness p program) :
    List (BinaryExtensionTableMessage FGL) :=
  (oldTable old 11).table.flatMap fun row => List.ofFn fun i : Fin 8 =>
    extensionMessageRow (BinaryExtension.shiftStaticLookupComponent.rowInput
      ((oldTable old 11).environment row)) i

private theorem binary_static_eight (row : Binary.BinaryRow FGL)
    (facts : Binary.StaticBinaryTableSpecFacts row) (index : Fin 8) :
    BinaryTable.binaryTable.Spec (binaryMessageRow row index) := by
  fin_cases index <;> simp only [binaryMessageRow]
  · exact facts.1
  · exact facts.2.1
  · exact facts.2.2.1
  · exact facts.2.2.2.1
  · exact facts.2.2.2.2.1
  · exact facts.2.2.2.2.2.1
  · exact facts.2.2.2.2.2.2.1
  · exact facts.2.2.2.2.2.2.2

private theorem extension_static_eight (row : BinaryExtension.BinaryExtensionRow FGL)
    (facts : BinaryExtension.StaticBinaryExtensionTableSpecFacts row) (index : Fin 8) :
    BinaryExtensionTable.binaryExtensionTable.Spec (extensionMessageRow row index) := by
  fin_cases index <;> simp only [extensionMessageRow]
  · exact facts.1
  · exact facts.2.1
  · exact facts.2.2.1
  · exact facts.2.2.2.1
  · exact facts.2.2.2.2.1
  · exact facts.2.2.2.2.2.1
  · exact facts.2.2.2.2.2.2.1
  · exact facts.2.2.2.2.2.2.2

theorem old_binary_messages_valid (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    ∀ message ∈ oldBinaryMessages old, BinaryTable.binaryTable.Spec message := by
  intro message hm
  obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  have hs := Legacy45.witness_spec_of_constraints old hc hb
    (oldTable old 12) (oldTable_mem old 12) row hr
  rw [old_binary_component, Binary.staticLookupComponent_spec] at hs
  have h := hs.2
  exact binary_static_eight _ h i

theorem old_extension_messages_valid (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    ∀ message ∈ oldExtensionMessages old,
      BinaryExtensionTable.binaryExtensionTable.Spec message := by
  intro message hm
  obtain ⟨row, hr, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  have hs := Legacy45.witness_spec_of_constraints old hc hb
    (oldTable old 11) (oldTable_mem old 11) row hr
  rw [old_extension_component, BinaryExtension.shiftStaticLookupComponent_spec] at hs
  have h := hs.2.1
  exact extension_static_eight _ h i

noncomputable def oldBinaryRequests (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    List (Fin BinaryTable.tableSize) :=
  Classical.choose (binary_static_requests (oldBinaryMessages old)
    (old_binary_messages_valid old hc hb))

noncomputable def oldExtensionRequests (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    List (Fin BinaryExtensionTable.tableSize) :=
  Classical.choose (extension_static_requests (oldExtensionMessages old)
    (old_extension_messages_valid old hc hb))

theorem oldBinaryRequests_messages (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    (oldBinaryRequests old hc hb).map (fun i => BinaryTable.rowOfIndex i.val) =
      oldBinaryMessages old :=
  Classical.choose_spec (binary_static_requests (oldBinaryMessages old)
    (old_binary_messages_valid old hc hb))

theorem oldExtensionRequests_messages (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    (oldExtensionRequests old hc hb).map (fun i => BinaryExtensionTable.rowOfIndex i.val) =
      oldExtensionMessages old :=
  Classical.choose_spec (extension_static_requests (oldExtensionMessages old)
    (old_extension_messages_valid old hc hb))

private theorem eight_flatMap_length {α β : Type} (rows : List α) (f : α → Fin 8 → β) :
    (rows.flatMap fun row => List.ofFn (f row)).length = 8 * rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      rw [List.flatMap_cons, List.length_append, List.length_ofFn, ih, List.length_cons]
      omega

theorem oldBinaryRequests_length (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    (oldBinaryRequests old hc hb).length = 8 * (oldTable old 12).table.length := by
  have h := congrArg List.length (oldBinaryRequests_messages old hc hb)
  simpa only [List.length_map, oldBinaryMessages, eight_flatMap_length] using h

theorem oldExtensionRequests_length (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    (oldExtensionRequests old hc hb).length = 8 * (oldTable old 11).table.length := by
  have h := congrArg List.length (oldExtensionRequests_messages old hc hb)
  simpa only [List.length_map, oldExtensionMessages, eight_flatMap_length] using h

/-- Evaluation is in the original physical row environment, not an unrelated
`fromInput` environment. The row-input variables are unchanged by retargeting. -/
theorem binary_consumer_requests (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    (binaryConsumerTable old).interactionsWith BinaryTableChannel.toRaw =
      consumedSourceRequests BinaryTableChannel
        (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val)
        (oldBinaryRequests old hc hb) := by
  have hops : Binary.tableConsumerComponent.operations.interactionsWith
      BinaryTableChannel.toRaw = List.ofFn (fun i : Fin 8 =>
        (BinaryTableChannel.emitted (-1)
          (binaryMessage Binary.tableConsumerComponent.rowInputVar i)).toRaw) := by
    rw [Binary.tableConsumerComponent_interactionsWith_binaryTableChannel]
    rfl
  unfold consumedSourceRequests
  rw [show (fun i : Fin BinaryTable.tableSize =>
      BinaryTableChannel.pushedIfValue (-1) (BinaryTable.rowOfIndex i.val)) =
      (fun m => BinaryTableChannel.pushedIfValue (-1) m) ∘
        (fun i => BinaryTable.rowOfIndex i.val) from rfl,
    ← List.map_map, oldBinaryRequests_messages]
  simp only [Table.interactionsWith, binaryConsumerTable_table,
    oldBinaryMessages, List.map_flatMap, List.map_ofFn,
    Operations.interactionValuesWith_eq_map]
  apply congrArg ((oldTable old 12).table.flatMap)
  funext row
  change (Binary.tableConsumerComponent.operations.interactionsWith
    BinaryTableChannel.toRaw).map _ = _
  rw [hops, List.map_ofFn]
  apply congrArg (fun f : Fin 8 → Interaction FGL => List.ofFn f)
  funext i
  dsimp only [Function.comp_apply]
  change ((BinaryTableChannel.pushedIf (-1)
      (binaryMessage Binary.tableConsumerComponent.rowInputVar i)).toRaw).eval
      ((oldTable old 12).environment row) =
    BinaryTableChannel.pushedIfValue (-1)
      (binaryMessageRow (Binary.staticLookupComponent.rowInput
        ((oldTable old 12).environment row)) i)
  rw [Channel.eval_pushedIf, eval_binaryMessage]
  simp only [Component.rowInputVar, eval_varFromOffset_valueFromOffset, Component.rowInput]
  with_unfolding_all rfl

theorem extension_consumer_requests (old : OldWitness p program)
    (hc : old.Constraints) (hb : old.BalancedChannels) :
    (extensionConsumerTable old).interactionsWith BinaryExtensionTableChannel.toRaw =
      consumedSourceRequests BinaryExtensionTableChannel
        (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val)
        (oldExtensionRequests old hc hb) := by
  have hops : BinaryExtension.shiftTableConsumerComponent.operations.interactionsWith
      BinaryExtensionTableChannel.toRaw = List.ofFn (fun i : Fin 8 =>
        (BinaryExtensionTableChannel.emitted (-1)
          (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar i)).toRaw) := by
    rw [BinaryExtension.shiftTableConsumerComponent_interactionsWith,
      BinaryExtension.tableConsumer_interactionsWith_binaryExtensionTable]
    rfl
  unfold consumedSourceRequests
  rw [show (fun i : Fin BinaryExtensionTable.tableSize =>
      BinaryExtensionTableChannel.pushedIfValue (-1) (BinaryExtensionTable.rowOfIndex i.val)) =
      (fun m => BinaryExtensionTableChannel.pushedIfValue (-1) m) ∘
        (fun i => BinaryExtensionTable.rowOfIndex i.val) from rfl,
    ← List.map_map, oldExtensionRequests_messages]
  simp only [Table.interactionsWith, extensionConsumerTable_table,
    oldExtensionMessages, List.map_flatMap, List.map_ofFn,
    Operations.interactionValuesWith_eq_map]
  apply congrArg ((oldTable old 11).table.flatMap)
  funext row
  change (BinaryExtension.shiftTableConsumerComponent.operations.interactionsWith
    BinaryExtensionTableChannel.toRaw).map _ = _
  rw [hops, List.map_ofFn]
  apply congrArg (fun f : Fin 8 → Interaction FGL => List.ofFn f)
  funext i
  dsimp only [Function.comp_apply]
  change ((BinaryExtensionTableChannel.pushedIf (-1)
      (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar i)).toRaw).eval
      ((oldTable old 11).environment row) =
    BinaryExtensionTableChannel.pushedIfValue (-1)
      (extensionMessageRow (BinaryExtension.shiftStaticLookupComponent.rowInput
        ((oldTable old 11).environment row)) i)
  rw [Channel.eval_pushedIf, eval_extensionMessage]
  simp only [Component.rowInputVar, eval_varFromOffset_valueFromOffset, Component.rowInput]
  with_unfolding_all rfl

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
