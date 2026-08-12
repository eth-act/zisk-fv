import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction

/-!
# Full-ensemble bus-103 provider match

The finished bus-103 channel turns each source-linked Mem consumer pull into
a same-message `SpecifiedRangesSlice` provider push.  The provider's `Spec`
is the concrete 16-bit static-table membership fact.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges
  (SpecifiedRangeMessage SpecifiedRangesSliceChannel memDistanceMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

private theorem specifiedRangesSliceChannel_ne_memBus :
    SpecifiedRangesSliceChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice103" = "MemoryBus" at h_name
  simp at h_name

private theorem specifiedRangesSliceChannel_ne_opBus :
    SpecifiedRangesSliceChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice103" = "OperationBus" at h_name
  simp at h_name

private theorem specifiedRangesSliceChannel_ne_memAlignRom :
    SpecifiedRangesSliceChannel.toRaw ≠ MemAlignRomChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice103" = "MemAlignRom133" at h_name
  simp at h_name

private theorem specifiedRangesSliceChannel_ne_memAlignRange :
    SpecifiedRangesSliceChannel.toRaw ≠
      ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice103" = "MemAlignRange107" at h_name
  simp at h_name

/-- Project finished bus-103 balance from the full ensemble. -/
theorem specifiedRangesSlice_balanced_of_witness
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith SpecifiedRangesSliceChannel.toRaw) := by
  have h := h_balanced SpecifiedRangesSliceChannel.toRaw (by
    change SpecifiedRangesSliceChannel.toRaw ∈
      [ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw,
        MemBusChannel.toRaw, OpBusChannel.toRaw, MemAlignRomChannel.toRaw,
        SpecifiedRangesSliceChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Every bus-103 interaction of the live Mem component is a negative
consumer emission. -/
theorem mem_table_specifiedRangesSlice_mult_neg_one
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    ∀ {interaction : Interaction FGL},
      interaction ∈ table.interactionsWith SpecifiedRangesSliceChannel.toRaw →
        interaction.mult = -1 := by
  intro interaction h_interaction
  refine ((Table.forall_interactionsWith_iff table SpecifiedRangesSliceChannel.toRaw
    (fun interaction => interaction.mult = -1)).mpr ?_) interaction h_interaction
  intro row h_row abstractInteraction h_abstract h_channel
  have h_member :
      abstractInteraction ∈ table.component.operations.interactionsWith
        SpecifiedRangesSliceChannel.toRaw := by
    simp [Operations.interactionsWith, h_abstract, h_channel]
  have h_interactions :
      table.component.operations.interactionsWith SpecifiedRangesSliceChannel.toRaw =
        [ ((SpecifiedRangesSliceChannel.emitted (-1)
              (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceBase0Expr)).toRaw)
        , ((SpecifiedRangesSliceChannel.emitted (-1)
              (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceBase1Expr)).toRaw)
        , ((SpecifiedRangesSliceChannel.emitted (-1)
              (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceEnd0Expr)).toRaw)
        , ((SpecifiedRangesSliceChannel.emitted (-1)
              (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceEnd1Expr)).toRaw) ] := by
    simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_rangeChannel
  simp [h_interactions] at h_member
  rcases h_member with h | h | h | h
  all_goals subst abstractInteraction
  all_goals rfl

/-- The selected static provider is the only possible non-pull bus-103
counterpart of a Mem consumer interaction. -/
theorem exists_specifiedRangesSlice_provider_of_mem_interaction
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {memTable : Table FGL}
    (h_memTable : memTable ∈ witness.allTables)
    {memInteraction : Interaction FGL}
    (h_memInteraction :
      memInteraction ∈ memTable.interactionsWith SpecifiedRangesSliceChannel.toRaw)
    (h_active : memInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith SpecifiedRangesSliceChannel.toRaw,
      providerInteraction.msg = memInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ providerTable ∈ witness.allTables,
          providerInteraction ∈ providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw
            ∧ providerTable.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component := by
  have h_memWitness :
      memInteraction ∈ witness.interactionsWith SpecifiedRangesSliceChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨memTable, h_memTable, h_memInteraction⟩
  obtain ⟨providerInteraction, h_providerWitness, h_message, h_nonzero, h_nonpull⟩ :=
    exists_push_of_pull
      (witness.interactionsWith SpecifiedRangesSliceChannel.toRaw)
      (specifiedRangesSlice_balanced_of_witness witness h_balanced)
      memInteraction h_memWitness h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_providerWitness
  obtain ⟨providerTable, h_providerTable, h_providerInteraction⟩ := h_providerWitness
  have h_component_mem :
      providerTable.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_providerTable
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_boundary | h_alignRead | h_alignByte | h_align | h_range107 | h_memAlignRom | h_mem | h_ranges |
      h_div | h_mul | h_extension | h_binary | h_binaryAdd | h_main
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_verifier]
      change SpecifiedRangesSliceChannel.toRaw ∉ []
      simp
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_boundary]
      change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_memBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_alignRead]
      change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_memBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_alignByte]
      change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_memBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_align]
      change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw, MemAlignRomChannel.toRaw,
        ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw]
      intro h
      have h' : SpecifiedRangesSliceChannel.toRaw = MemBusChannel.toRaw ∨
          SpecifiedRangesSliceChannel.toRaw = MemAlignRomChannel.toRaw ∨
          SpecifiedRangesSliceChannel.toRaw =
            ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
      rcases h' with h | h | h
      · exact specifiedRangesSliceChannel_ne_memBus h
      · exact specifiedRangesSliceChannel_ne_memAlignRom h
      · exact specifiedRangesSliceChannel_ne_memAlignRange h
    simp [h_nil] at h_providerInteraction
  · simp [memAlignRangeSlice_table_interactionsWith_specifiedRanges_nil h_range107] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_memAlignRom]
      change SpecifiedRangesSliceChannel.toRaw ∉ [MemAlignRomChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_memAlignRom
    simp [h_nil] at h_providerInteraction
  · exact False.elim (h_nonpull
      (mem_table_specifiedRangesSlice_mult_neg_one h_mem h_providerInteraction))
  · refine ⟨providerInteraction, ?_, h_message, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_ranges⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨providerTable, h_providerTable, h_providerInteraction⟩
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_div]
      change SpecifiedRangesSliceChannel.toRaw ∉ []
      simp
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_mul, arithMulProviderComponent]
      change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_extension]
      change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_binary]
      change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_binaryAdd]
      change SpecifiedRangesSliceChannel.toRaw ∉ [OpBusChannel.toRaw]
      simp only [List.mem_singleton]
      exact specifiedRangesSliceChannel_ne_opBus
    simp [h_nil] at h_providerInteraction
  · have h_nil : providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_main]
      change SpecifiedRangesSliceChannel.toRaw ∉ [MemBusChannel.toRaw, OpBusChannel.toRaw]
      intro h
      simp only [List.mem_cons] at h
      rcases h with h | h | h
      · exact specifiedRangesSliceChannel_ne_memBus h
      · exact specifiedRangesSliceChannel_ne_opBus h
      · simp at h
    simp [h_nil] at h_providerInteraction

/-- Unpack a static bus-103 provider interaction to the provider row that
supplies its membership fact. -/
theorem exists_specifiedRangesSlice_provider_row_of_interaction
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component)
    {interaction : Interaction FGL}
    (h_interaction : interaction ∈ table.interactionsWith SpecifiedRangesSliceChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((SpecifiedRangesSliceChannel.pushed
          (memDistanceMessage ZiskFv.AirsClean.SpecifiedRangesSlice.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  have h_singleton :
      table.component.operations.interactionsWith SpecifiedRangesSliceChannel.toRaw =
        [((SpecifiedRangesSliceChannel.pushed
          (memDistanceMessage ZiskFv.AirsClean.SpecifiedRangesSlice.component.rowInputVar)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.SpecifiedRangesSlice.component_interactionsWith_rangeChannel
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_interaction
  exact h_interaction

/-- A concrete static-provider push with the bus-103 message for `value`
proves that value's 16-bit table membership. -/
theorem rangeTable16_spec_of_specifiedRangesSlice_provider_interaction
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_specs : witness.Spec)
    {providerTable : Table FGL}
    (h_providerTable : providerTable ∈ witness.allTables)
    (h_providerComponent :
      providerTable.component = ZiskFv.AirsClean.SpecifiedRangesSlice.component)
    {providerInteraction : Interaction FGL}
    (h_providerInteraction :
      providerInteraction ∈ providerTable.interactionsWith SpecifiedRangesSliceChannel.toRaw)
    {value : FGL}
    (h_message : providerInteraction.msg = (toElements (memDistanceMessage value)).toArray) :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec value := by
  obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
    exists_specifiedRangesSlice_provider_row_of_interaction
      h_providerComponent h_providerInteraction
  have h_spec := h_specs providerTable h_providerTable providerRow h_providerRow
  rw [h_providerComponent] at h_spec
  rw [h_providerEval] at h_message
  have h_eval_message (env : Environment FGL) (value : Expression FGL) :
      Eval.eval env (memDistanceMessage value) =
        memDistanceMessage (Expression.eval env value) := by
    rw [SpecifiedRangeMessage.mk.injEq]
    simp only [memDistanceMessage, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
      Expression.eval]
    repeat constructor
  rw [Channel.eval_pushed, h_eval_message] at h_message
  have h_value := congrArg (fun elements : Array FGL => elements[1]!) h_message
  have h_value' : valueFromOffset field 0 (providerTable.environment providerRow) = value := by
    simpa [Channel.pushedValue, memDistanceMessage,
      ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
      ProvableStruct.components, ProvableStruct.toComponents,
      ProvableStruct.componentsToElements,
      ZiskFv.AirsClean.SpecifiedRangesSlice.component, Component.rowInputVar,
      ProvableType.varFromOffset] using h_value
  have h_providerSpec : ZiskFv.AirsClean.RangeTables.rangeTable16.Spec
      (valueFromOffset field 0 (providerTable.environment providerRow)) := by
    simpa [Component.Spec, Component.rowInput,
      ZiskFv.AirsClean.SpecifiedRangesSlice.component,
      ZiskFv.AirsClean.SpecifiedRangesSlice.circuit,
      Component.rowInputVar] using h_spec
  simpa [h_value'] using h_providerSpec

end ZiskFv.AirsClean.FullEnsemble
