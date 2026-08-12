import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction

/-!
# Full-ensemble MemAlign bus-107 provider match

Each of MemAlign's eight source Range Check consumer emissions
(`#982/#984/#986/#988/#990/#992/#994/#996`,
`mem_align.pil:113-118`) is a negative one-slot bus-107 interaction.  The
finished-channel protocol selects a same-message static provider push, and
that provider's constrained `rangeTable8` lookup derives byte membership.
The consumer channel carries no membership guarantee and no caller premise.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges (SpecifiedRangesSliceChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel MemAlignRangeMessage)
open ZiskFv.AirsClean.RangeTables (rangeTable8)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

private theorem memAlignRangeChannel_ne_memBus :
    MemAlignRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "MemAlignRange107" = "MemoryBus" at h_name
  simp at h_name

private theorem memAlignRangeChannel_ne_opBus :
    MemAlignRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "MemAlignRange107" = "OperationBus" at h_name
  simp at h_name

private theorem memAlignRangeChannel_ne_memAlignRom :
    MemAlignRangeChannel.toRaw ≠ MemAlignRomChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "MemAlignRange107" = "MemAlignRom133" at h_name
  simp at h_name

private theorem memAlignRangeChannel_ne_specifiedRanges :
    MemAlignRangeChannel.toRaw ≠ SpecifiedRangesSliceChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "MemAlignRange107" = "SpecifiedRangesSlice103" at h_name
  simp at h_name

/-- Project finished bus-107 balance from the full ensemble. -/
theorem memAlignRange_balanced_of_witness
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith MemAlignRangeChannel.toRaw) := by
  have h := h_balanced MemAlignRangeChannel.toRaw (by
    change MemAlignRangeChannel.toRaw ∈
      [ MemAlignRangeChannel.toRaw
      , MemBusChannel.toRaw
      , OpBusChannel.toRaw
      , MemAlignRomChannel.toRaw
      , SpecifiedRangesSliceChannel.toRaw ]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Every bus-107 interaction of MemAlign is one of the eight fixed negative
    register-byte consumers. -/
theorem memAlign_table_memAlignRange_mult_neg_one
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component) :
    ∀ {interaction : Interaction FGL},
      interaction ∈ table.interactionsWith MemAlignRangeChannel.toRaw →
        interaction.mult = -1 := by
  intro interaction h_interaction
  refine ((Table.forall_interactionsWith_iff table MemAlignRangeChannel.toRaw
    (fun interaction => interaction.mult = -1)).mpr ?_) interaction h_interaction
  intro row h_row abstractInteraction h_abstract h_channel
  have h_member :
      abstractInteraction ∈ table.component.operations.interactionsWith
        MemAlignRangeChannel.toRaw := by
    simp [Operations.interactionsWith, h_abstract, h_channel]
  have h_interactions :
      table.component.operations.interactionsWith MemAlignRangeChannel.toRaw =
        [ ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_0)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_1)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_2)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_3)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_4)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_5)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_6)).toRaw)
        , ((MemAlignRangeChannel.emitted (-1)
              (ZiskFv.AirsClean.MemAlign.memAlignRangeMessageExpr
                ZiskFv.AirsClean.MemAlign.component.rowInputVar.reg_7)).toRaw) ] := by
    simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memAlignRangeChannel
  simp [h_interactions] at h_member
  rcases h_member with h | h | h | h | h | h | h | h
  all_goals subst abstractInteraction
  all_goals rfl

/-- The only non-pull bus-107 counterpart of a MemAlign range consumer is
    the constrained byte-range provider slice. -/
theorem exists_memAlignRangeSlice_provider_of_memAlign_interaction
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {memAlignTable : Table FGL}
    (h_memAlignTable : memAlignTable ∈ witness.allTables)
    {memAlignInteraction : Interaction FGL}
    (h_memAlignInteraction :
      memAlignInteraction ∈ memAlignTable.interactionsWith MemAlignRangeChannel.toRaw)
    (h_active : memAlignInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemAlignRangeChannel.toRaw,
      providerInteraction.msg = memAlignInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ providerTable ∈ witness.allTables,
          providerInteraction ∈ providerTable.interactionsWith MemAlignRangeChannel.toRaw
            ∧ providerTable.component = ZiskFv.AirsClean.MemAlignRangeSlice.component := by
  have h_memWitness :
      memAlignInteraction ∈ witness.interactionsWith MemAlignRangeChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨memAlignTable, h_memAlignTable, h_memAlignInteraction⟩
  obtain ⟨providerInteraction, h_providerWitness, h_message, h_nonzero, h_nonpull⟩ :=
    exists_push_of_pull
      (witness.interactionsWith MemAlignRangeChannel.toRaw)
      (memAlignRange_balanced_of_witness witness h_balanced)
      memAlignInteraction h_memWitness h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_providerWitness
  obtain ⟨providerTable, h_providerTable, h_providerInteraction⟩ := h_providerWitness
  have h_component_mem :
      providerTable.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_providerTable
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_boundary | h_alignRead | h_alignByte | h_align | h_range | h_rom | h_mem |
      h_ranges | h_div | h_mul | h_extension | h_binary | h_binaryAdd | h_main
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_verifier]
      change MemAlignRangeChannel.toRaw ∉ []
      simp
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_boundary]
      change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_memBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_alignRead]
      change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_memBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_alignByte]
      change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_memBus
    simp [h_nil] at h_providerInteraction
  · exact False.elim (h_nonpull
      (memAlign_table_memAlignRange_mult_neg_one h_align h_providerInteraction))
  · refine ⟨providerInteraction, ?_, h_message, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_range⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨providerTable, h_providerTable, h_providerInteraction⟩
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_rom]
      change MemAlignRangeChannel.toRaw ∉ [MemAlignRomChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_memAlignRom
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_mem]
      change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw, SpecifiedRangesSliceChannel.toRaw]
      intro h
      have h' : MemAlignRangeChannel.toRaw = MemBusChannel.toRaw ∨
          MemAlignRangeChannel.toRaw = SpecifiedRangesSliceChannel.toRaw := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
      rcases h' with h | h
      · exact memAlignRangeChannel_ne_memBus h
      · exact memAlignRangeChannel_ne_specifiedRanges h
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_ranges]
      change MemAlignRangeChannel.toRaw ∉ [SpecifiedRangesSliceChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_specifiedRanges
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_div]
      change MemAlignRangeChannel.toRaw ∉ []
      simp
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_mul, arithMulProviderComponent]
      change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_extension]
      change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_binary]
      change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_binaryAdd]
      change MemAlignRangeChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact memAlignRangeChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith MemAlignRangeChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_main]
      change MemAlignRangeChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
      intro h
      have h' : MemAlignRangeChannel.toRaw = MemBusChannel.toRaw ∨
          MemAlignRangeChannel.toRaw = OpBusChannel.toRaw := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
      rcases h' with h | h
      · exact memAlignRangeChannel_ne_memBus h
      · exact memAlignRangeChannel_ne_opBus h
    simp [h_nil] at h_providerInteraction

/-- Unpack a static bus-107 provider interaction to its concrete provider row. -/
theorem exists_memAlignRangeSlice_provider_row_of_interaction
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRangeSlice.component)
    {interaction : Interaction FGL}
    (h_interaction : interaction ∈ table.interactionsWith MemAlignRangeChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemAlignRangeChannel.pushed
          ZiskFv.AirsClean.MemAlignRangeSlice.component.rowInputVar).toRaw).eval
          (table.environment row) := by
  have h_singleton :
      table.component.operations.interactionsWith MemAlignRangeChannel.toRaw =
        [((MemAlignRangeChannel.pushed
          ZiskFv.AirsClean.MemAlignRangeSlice.component.rowInputVar).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.MemAlignRangeSlice.component_interactionsWith_memAlignRangeChannel
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_interaction
  exact h_interaction

/-- The constrained provider row selected by bus-107 balance satisfies exact
    `rangeTable8` membership. -/
theorem memAlignRangeTable_spec_of_memAlignRangeSlice_provider_row
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_specs : witness.Spec)
    {providerTable : Table FGL}
    (h_providerTable : providerTable ∈ witness.allTables)
    (h_providerComponent :
      providerTable.component = ZiskFv.AirsClean.MemAlignRangeSlice.component)
    {providerRow : Array FGL}
    (h_providerRow : providerRow ∈ providerTable.table) :
    rangeTable8.Spec
      (Eval.eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignRangeSlice.component.rowInputVar).value := by
  have h_spec := h_specs providerTable h_providerTable providerRow h_providerRow
  rw [h_providerComponent] at h_spec
  simpa only [Component.Spec, Component.rowInput, eval_varFromOffset_valueFromOffset,
    ZiskFv.AirsClean.MemAlignRangeSlice.component,
    ZiskFv.AirsClean.MemAlignRangeSlice.circuit,
    Component.rowInputVar] using h_spec

/-- Raw finished-channel equality restores equality of the one-slot typed
    provider and consumer messages. -/
theorem memAlignRangeMessage_eq_of_eval_pushed_provider_msg_eq
    {consumerMsg providerMsg : MemAlignRangeMessage (Expression FGL)}
    {consumerEnv providerEnv : Environment FGL}
    (h_msg :
      (((MemAlignRangeChannel.pushed providerMsg).toRaw).eval providerEnv).msg =
        (((MemAlignRangeChannel.emitted (-1) consumerMsg).toRaw).eval consumerEnv).msg) :
    Eval.eval providerEnv providerMsg = Eval.eval consumerEnv consumerMsg := by
  have h_vec :
      Vector.map (Expression.eval providerEnv) (toElements providerMsg) =
        Vector.map (Expression.eval consumerEnv) (toElements consumerMsg) := by
    apply Vector.toArray_injective
    simpa [ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_from := congrArg
    (fun xs => (fromElements xs : MemAlignRangeMessage FGL)) h_vec
  simpa [ProvableType.fromElements_eval_toElements] using h_from

/-- Every explicit bus-107 MemAlign consumer interaction is matched to a
    constrained byte provider, so the evaluated one-slot tuple has exact
    membership. -/
theorem rangeTable8_spec_of_memAlign_range_interaction
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {memAlignTable : Table FGL}
    (h_memAlignTable : memAlignTable ∈ witness.allTables)
    {consumerMsg : MemAlignRangeMessage (Expression FGL)}
    {memAlignRow : Array FGL}
    (h_consumerInteraction :
      ((MemAlignRangeChannel.emitted (-1) consumerMsg).toRaw).eval
          (memAlignTable.environment memAlignRow) ∈
        memAlignTable.interactionsWith MemAlignRangeChannel.toRaw) :
    rangeTable8.Spec
      (Eval.eval (memAlignTable.environment memAlignRow) consumerMsg).value := by
  let consumerInteraction : Interaction FGL :=
    ((MemAlignRangeChannel.emitted (-1) consumerMsg).toRaw).eval
      (memAlignTable.environment memAlignRow)
  have h_consumer :
      consumerInteraction ∈ memAlignTable.interactionsWith MemAlignRangeChannel.toRaw := by
    exact h_consumerInteraction
  obtain ⟨providerInteraction, _, h_message, _, _, providerTable, h_providerTable,
      h_providerInteraction, h_providerComponent⟩ :=
    exists_memAlignRangeSlice_provider_of_memAlign_interaction witness h_balanced
      h_memAlignTable h_consumer (by rfl)
  obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
    exists_memAlignRangeSlice_provider_row_of_interaction
      h_providerComponent h_providerInteraction
  have h_providerSpec := memAlignRangeTable_spec_of_memAlignRangeSlice_provider_row
    (witness_spec_of_constraints witness h_constraints h_balanced)
    h_providerTable h_providerComponent h_providerRow
  rw [h_providerEval] at h_message
  have h_typed := memAlignRangeMessage_eq_of_eval_pushed_provider_msg_eq h_message
  rw [← h_typed]
  exact h_providerSpec

end ZiskFv.AirsClean.FullEnsemble
