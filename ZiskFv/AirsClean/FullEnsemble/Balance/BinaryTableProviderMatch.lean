import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.BinaryTableBalance

/-!
# Actual full-ensemble Binary lookup membership

Pinned production source `b632745`: `state-machines/binary/pil/binary_table.pil:335-336`
and `binary_extension_table.pil:204-205` expose the seven fixed tuple slots and
unrestricted witness multiplicity. The actual negative routes are
`binary.pil:115-124` and `binary_extension.pil:91-92`. Physical placement comes
from the actual compiler's `Extraction.PackedVirtualTables`, not a guessed
mapping or the templates' larger default `N`.

Buses125/124 are finished in `fullRv64imSoundEnsemble`. All eight real negative
consumer routes obtain their static table facts from the source-owned tuple
providers and accepted balance. Provider multiplicity is arbitrary FGL; no
positivity, count, honest-row, or caller membership hypothesis is used.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks Air.Flat
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryTableBalance
  (binaryMessage binaryMessage_mem binaryMessageRow eval_binaryMessage
   extensionMessageRow eval_extensionMessage)

private theorem interactionsWith_nil_of_channel_names
    {table : Table FGL} (channel : RawChannel FGL)
    (h_names : channel.name ∉ table.component.circuit.channels.map (·.name)) :
    table.interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro h
  exact h_names (List.mem_map_of_mem (f := fun c : RawChannel FGL => c.name) h)

private theorem full_verifier_channels (length : Nat) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.circuit.channels = [] := by
  change (fullRv64imSoundEnsemble length program).ensemble.verifier.channels = []
  rw [(fullRv64imSoundEnsemble length program).verifier_empty]
  rfl

private theorem binaryConsumer_mult {table : Table FGL}
    (hc : table.component = Binary.tableConsumerComponent)
    {interaction : Interaction FGL}
    (hi : interaction ∈ table.interactionsWith BinaryTableChannel.toRaw) :
    interaction.mult = -1 := by
  simp only [Table.interactionsWith, List.mem_flatMap] at hi
  obtain ⟨row, _, hi⟩ := hi
  rw [Operations.interactionValuesWith_eq_map, hc,
    Binary.tableConsumerComponent_interactionsWith_binaryTableChannel] at hi
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h <;> subst interaction <;> rfl

private theorem extensionConsumer_mult {table : Table FGL}
    (hc : table.component = BinaryExtension.shiftTableConsumerComponent)
    {interaction : Interaction FGL}
    (hi : interaction ∈ table.interactionsWith BinaryExtensionTableChannel.toRaw) :
    interaction.mult = -1 := by
  simp only [Table.interactionsWith, List.mem_flatMap] at hi
  obtain ⟨row, _, hi⟩ := hi
  rw [Operations.interactionValuesWith_eq_map, hc,
    BinaryExtension.shiftTableConsumerComponent_interactionsWith,
    BinaryExtension.tableConsumer_interactionsWith_binaryExtensionTable] at hi
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h <;> subst interaction <;> rfl

/-- Every non-pull on bus125 comes from its actual source component. -/
theorem binary_nonpull_source
    {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    {table : Table FGL} (ht : table ∈ w.allTables)
    {interaction : Interaction FGL}
    (hi : interaction ∈ table.interactionsWith BinaryTableChannel.toRaw)
    (hn : interaction.mult ≠ -1) :
    table.component = BinaryTableSlice.sourceComponent := by
  rcases component_mem_fullRv64im_cases
      (EnsembleWitness.mem_allTables_component_of_mem_allTables ht) with
    hc | hc | hc | hc | hc | hc | hc | hc | hc |
    hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals first
    | exact hc
    | exact False.elim (hn (binaryConsumer_mult hc hi))
    | have he : table.interactionsWith BinaryTableChannel.toRaw = [] := by
        apply interactionsWith_nil_of_channel_names
        rw [hc]
        first
        | rw [full_verifier_channels]; simp
        | exact of_decide_eq_true (by with_unfolding_all rfl)
      simp [he] at hi


/-- Every non-pull on bus124 comes from its actual source component. -/
theorem extension_nonpull_source
    {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    {table : Table FGL} (ht : table ∈ w.allTables)
    {interaction : Interaction FGL}
    (hi : interaction ∈ table.interactionsWith BinaryExtensionTableChannel.toRaw)
    (hn : interaction.mult ≠ -1) :
    table.component = BinaryExtensionTableSlice.sourceComponent := by
  rcases component_mem_fullRv64im_cases
      (EnsembleWitness.mem_allTables_component_of_mem_allTables ht) with
    hc | hc | hc | hc | hc | hc | hc | hc | hc |
    hc | hc | hc | hc | hc | hc | hc | hc | hc
  all_goals first
    | exact hc
    | exact False.elim (hn (extensionConsumer_mult hc hi))
    | have he : table.interactionsWith BinaryExtensionTableChannel.toRaw = [] := by
        apply interactionsWith_nil_of_channel_names
        rw [hc]
        first
        | rw [full_verifier_channels]; simp
        | exact of_decide_eq_true (by with_unfolding_all rfl)
      simp [he] at hi

/-- The two source-owned tuple prefixes are jointly realizable in one actual
packed physical witness. Only absent raw rows are extended with zero
multiplicity; this is not a fixed-column or unsupported-expression fallback.
This theorem makes no claim that a changed interaction count preserves the
separate `BalancedInteractions` length guard. -/
theorem source_pair_reifies
    (base : PackedVirtualTableSources.Witness FGL)
    (binary extension : Table FGL)
    (h_binary : binary.component = BinaryTableSlice.sourceComponent)
    (h_extension : extension.component = BinaryExtensionTableSlice.sourceComponent) :
    ∃ raw : PackedVirtualTableSources.Witness FGL,
      binary.table =
        (PackedVirtualTableSources.binaryProviderTable raw binary.data).table.take binary.length ∧
      extension.table =
        (PackedVirtualTableSources.extensionProviderTable raw extension.data).table.take
          extension.length ∧
      binary.interactionsWith BinaryTableChannel.toRaw =
        (PackedVirtualTableSources.binaryInteractions raw).take binary.length ∧
      extension.interactionsWith BinaryExtensionTableChannel.toRaw =
        (PackedVirtualTableSources.extensionInteractions raw).take extension.length := by
  exact ⟨PackedVirtualTableSources.reifyPrefixes base binary extension h_binary h_extension,
    PackedVirtualTableSources.binaryPrefix_materialized base binary extension h_binary h_extension,
    PackedVirtualTableSources.extensionPrefix_materialized base binary extension h_binary h_extension,
    PackedVirtualTableSources.binaryPrefix_interactionsWith base binary extension h_binary h_extension,
    PackedVirtualTableSources.extensionPrefix_interactionsWith base binary extension h_binary h_extension⟩

private theorem exists_full_table_of_component
    {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    {component : Component FGL}
    (h_component : component ∈ (fullRv64imEnsemble length program).ensemble.allTables) :
    ∃ table ∈ w.allTables, table.component = component := by
  rw [← w.allTables_map_component] at h_component
  exact List.mem_map.mp h_component

/-- A bus-125 consumer message is an actual source-defined table row. -/
theorem binary_membership_of_balance {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels)
    {interaction : Interaction FGL}
    (hi : interaction ∈ w.interactionsWith BinaryTableChannel.toRaw)
    (hm : interaction.mult = -1) :
    ∃ message : BinaryTableMessage FGL,
      BinaryTable.binaryTable.Spec message ∧
      interaction.msg = (toElements message).toArray := by
  have hbalance : BalancedInteractions (w.interactionsWith BinaryTableChannel.toRaw) := by
    simpa only [EnsembleWitness.BalancedChannel,
      EnsembleWitness.interactionsWith_allTablesWitness] using
      hb BinaryTableChannel.toRaw (by simp [fullRv64imEnsemble, fullRv64imSoundEnsemble,
        SoundEnsemble.toFormal, circuit_norm])
  obtain ⟨provider, hp, hmsg, _, hn⟩ :=
    exists_push_of_pull _ hbalance interaction hi hm
  obtain ⟨table, ht, hp⟩ := EnsembleWitness.mem_interactionsWith.mp hp
  have h_binary := binary_nonpull_source w ht hp hn
  obtain ⟨extension, h_extension_mem, h_extension⟩ := exists_full_table_of_component w
    (component := BinaryExtensionTableSlice.sourceComponent)
    (by simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
      Ensemble.allTables, SoundEnsemble.addTable_tables,
      SoundEnsemble.addFinishedChannel_tables])
  obtain ⟨raw, _, _, h_binary_prefix, _⟩ :=
    source_pair_reifies (fun _ => 0) table extension h_binary h_extension
  rw [h_binary_prefix] at hp
  have h_canonical : provider ∈ PackedVirtualTableSources.binaryInteractions raw :=
    List.mem_of_mem_take hp
  rw [← PackedVirtualTableSources.binaryProviderTable_interactionsWith raw table.data]
    at h_canonical
  obtain ⟨message, hs, he⟩ := BinaryTableSlice.sourceInteraction_mem_spec rfl
    (PackedVirtualTableSources.binaryProviderTable_constraints raw table.data) h_canonical
  exact ⟨message, hs, hmsg.symm.trans he⟩

/-- A bus-124 consumer message is an actual source-defined table row. -/
theorem extension_membership_of_balance {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels)
    {interaction : Interaction FGL}
    (hi : interaction ∈ w.interactionsWith BinaryExtensionTableChannel.toRaw)
    (hm : interaction.mult = -1) :
    ∃ message : BinaryExtensionTableMessage FGL,
      BinaryExtensionTable.binaryExtensionTable.Spec message ∧
      interaction.msg = (toElements message).toArray := by
  have hbalance : BalancedInteractions (w.interactionsWith BinaryExtensionTableChannel.toRaw) := by
    simpa only [EnsembleWitness.BalancedChannel,
      EnsembleWitness.interactionsWith_allTablesWitness] using
      hb BinaryExtensionTableChannel.toRaw (by simp [fullRv64imEnsemble, fullRv64imSoundEnsemble,
        SoundEnsemble.toFormal, circuit_norm])
  obtain ⟨provider, hp, hmsg, _, hn⟩ :=
    exists_push_of_pull _ hbalance interaction hi hm
  obtain ⟨table, ht, hp⟩ := EnsembleWitness.mem_interactionsWith.mp hp
  have h_extension := extension_nonpull_source w ht hp hn
  obtain ⟨binary, h_binary_mem, h_binary⟩ := exists_full_table_of_component w
    (component := BinaryTableSlice.sourceComponent)
    (by simp [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
      Ensemble.allTables, SoundEnsemble.addTable_tables,
      SoundEnsemble.addFinishedChannel_tables])
  obtain ⟨raw, _, _, _, h_extension_prefix⟩ :=
    source_pair_reifies (fun _ => 0) binary table h_binary h_extension
  rw [h_extension_prefix] at hp
  have h_canonical : provider ∈ PackedVirtualTableSources.extensionInteractions raw :=
    List.mem_of_mem_take hp
  rw [← PackedVirtualTableSources.extensionProviderTable_interactionsWith raw table.data]
    at h_canonical
  obtain ⟨message, hs, he⟩ := BinaryExtensionTableSlice.sourceInteraction_mem_spec rfl
    (PackedVirtualTableSources.extensionProviderTable_constraints raw table.data) h_canonical
  exact ⟨message, hs, hmsg.symm.trans he⟩

/-- All eight Binary routes obtain membership through the finished channel.
No input-row membership or provider-soundness premise is added. -/
theorem binary_all_eight {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels)
    {table : Table FGL} (ht : table ∈ w.allTables)
    (hcomp : table.component = Binary.tableConsumerComponent)
    {row : Array FGL} (hr : row ∈ table.table) (index : Fin 8) :
    BinaryTable.binaryTable.Spec (eval (table.environment row)
      (binaryMessage Binary.tableConsumerComponent.rowInputVar index)) := by
  let abstract := (BinaryTableChannel.emitted (-1)
    (binaryMessage Binary.tableConsumerComponent.rowInputVar index)).toRaw
  have hi : abstract.eval (table.environment row) ∈
      w.interactionsWith BinaryTableChannel.toRaw := by
    apply EnsembleWitness.mem_interactionsWith.mpr
    refine ⟨table, ht, ?_⟩
    simp only [Table.interactionsWith, List.mem_flatMap]
    refine ⟨row, hr, ?_⟩
    rw [Operations.interactionValuesWith_eq_map, hcomp]
    exact List.mem_map.mpr ⟨abstract, binaryMessage_mem index, rfl⟩
  obtain ⟨message, hs, he⟩ := binary_membership_of_balance w hc hb hi rfl
  have he' : (toElements (eval (table.environment row)
      (binaryMessage Binary.tableConsumerComponent.rowInputVar index))).toArray =
      (toElements message).toArray := by
    simpa only [abstract, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted, ProvableType.toElements_eval] using he
  have htyped : eval (table.environment row)
      (binaryMessage Binary.tableConsumerComponent.rowInputVar index) = message := by
    simpa only [ProvableType.fromElements_toElements] using
      congrArg (fun vector => (fromElements vector : BinaryTableMessage FGL))
        (Vector.toArray_inj.mp he')
  rw [htyped]
  exact hs

theorem extension_all_eight {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels)
    {table : Table FGL} (ht : table ∈ w.allTables)
    (hcomp : table.component = BinaryExtension.shiftTableConsumerComponent)
    {row : Array FGL} (hr : row ∈ table.table) (index : Fin 8) :
    BinaryExtensionTable.binaryExtensionTable.Spec (eval (table.environment row)
      (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar index)) := by
  let abstract := (BinaryExtensionTableChannel.emitted (-1)
    (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar index)).toRaw
  have hi : abstract.eval (table.environment row) ∈
      w.interactionsWith BinaryExtensionTableChannel.toRaw := by
    apply EnsembleWitness.mem_interactionsWith.mpr
    refine ⟨table, ht, ?_⟩
    simp only [Table.interactionsWith, List.mem_flatMap]
    refine ⟨row, hr, ?_⟩
    rw [Operations.interactionValuesWith_eq_map, hcomp,
      BinaryExtension.shiftTableConsumerComponent_interactionsWith]
    exact List.mem_map.mpr ⟨abstract,
      BinaryExtension.byteInteraction_mem_tableConsumer_operations index, rfl⟩
  obtain ⟨message, hs, he⟩ := extension_membership_of_balance w hc hb hi rfl
  have he' : (toElements (eval (table.environment row)
      (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar index))).toArray =
      (toElements message).toArray := by
    simpa only [abstract, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted, ProvableType.toElements_eval] using he
  have htyped : eval (table.environment row)
      (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar index) = message := by
    simpa only [ProvableType.fromElements_toElements] using
      congrArg (fun vector => (fromElements vector : BinaryExtensionTableMessage FGL))
        (Vector.toArray_inj.mp he')
  rw [htyped]
  exact hs

/-- Integration contract: the same eight memberships previously obtained by
    a detached static-lookup consumer now follow from the actual finished
    bus-125 composition. Existing semantic table proofs consume this bundle. -/
theorem binary_spec_facts_of_balance {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels)
    {table : Table FGL} (ht : table ∈ w.allTables)
    (hcomp : table.component = Binary.tableConsumerComponent)
    {row : Array FGL} (hr : row ∈ table.table) :
    Binary.StaticBinaryTableSpecFacts
      (Binary.tableConsumerComponent.rowInput (table.environment row)) := by
  have h : ∀ index : Fin 8, BinaryTable.binaryTable.Spec
      (binaryMessageRow
        (Binary.tableConsumerComponent.rowInput (table.environment row)) index) := by
    intro index
    have he := binary_all_eight w hc hb ht hcomp hr index
    rw [eval_binaryMessage] at he
    simpa only [Component.rowInput, Component.rowInputVar,
      eval_varFromOffset_valueFromOffset] using he
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

theorem extension_spec_facts_of_balance {length : Nat} {program : Program length}
    (w : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (hc : w.Constraints) (hb : w.BalancedChannels)
    {table : Table FGL} (ht : table ∈ w.allTables)
    (hcomp : table.component = BinaryExtension.shiftTableConsumerComponent)
    {row : Array FGL} (hr : row ∈ table.table) :
    BinaryExtension.StaticBinaryExtensionTableSpecFacts
      (BinaryExtension.shiftTableConsumerComponent.rowInput (table.environment row)) := by
  have h : ∀ index : Fin 8, BinaryExtensionTable.binaryExtensionTable.Spec
      (extensionMessageRow
        (BinaryExtension.shiftTableConsumerComponent.rowInput (table.environment row)) index) := by
    intro index
    have he := extension_all_eight w hc hb ht hcomp hr index
    rw [eval_extensionMessage] at he
    simpa only [Component.rowInput, Component.rowInputVar,
      eval_varFromOffset_valueFromOffset] using he
  exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩

/-- The old full Binary semantic table predicate is derived for the actual
consumer table, using local constraints and all eight finished-bus routes. -/
theorem binary_table_full_spec_of_accepted
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints) (h_balanced : witness.BalancedChannels)
    {providerTable : Table FGL} (h_table : providerTable ∈ witness.allTables)
    (h_component : providerTable.component = Binary.tableConsumerComponent) :
    ∀ row ∈ providerTable.table,
      Binary.Spec (Binary.tableConsumerComponent.rowInput (providerTable.environment row)) ∧
      Binary.StaticBinaryTableSpecFacts
        (Binary.tableConsumerComponent.rowInput (providerTable.environment row)) := by
  intro row h_row
  have h_core := (witness_spec_of_constraints witness h_constraints h_balanced)
    providerTable h_table row h_row
  rw [h_component] at h_core
  exact ⟨h_core, binary_spec_facts_of_balance witness h_constraints h_balanced
    h_table h_component h_row⟩

/-- The old shift-aware full semantic predicate is derived from the actual
consumer, including the retained source b0 range rather than a new premise. -/
theorem extension_table_full_spec_of_accepted
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints) (h_balanced : witness.BalancedChannels)
    {providerTable : Table FGL} (h_table : providerTable ∈ witness.allTables)
    (h_component : providerTable.component = BinaryExtension.shiftTableConsumerComponent) :
    ∀ row ∈ providerTable.table,
      BinaryExtension.Spec
        (BinaryExtension.shiftTableConsumerComponent.rowInput (providerTable.environment row)) ∧
      BinaryExtension.StaticBinaryExtensionTableSpecFacts
        (BinaryExtension.shiftTableConsumerComponent.rowInput (providerTable.environment row)) ∧
      BinaryExtension.ShiftB0RangeSpecFact
        (BinaryExtension.shiftTableConsumerComponent.rowInput (providerTable.environment row)) := by
  intro row h_row
  have h_core := (witness_spec_of_constraints witness h_constraints h_balanced)
    providerTable h_table row h_row
  rw [h_component] at h_core
  exact ⟨h_core.1, extension_spec_facts_of_balance witness h_constraints h_balanced
    h_table h_component h_row, h_core.2⟩

end ZiskFv.AirsClean.FullEnsemble
