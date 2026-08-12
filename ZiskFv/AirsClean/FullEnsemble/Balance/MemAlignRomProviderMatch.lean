import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction
import ZiskFv.AirsClean.MemAlign.Bridge

/-!
# Full-ensemble bus-133 provider match

The finished bus-133 channel transports exact membership in the extracted
`MemAlignRom` static table.  MemAlign is a consumer: D3 supplies its
successor-PC payload, while balance selects the matching static provider row.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel MemAlignRomMessage)
open ZiskFv.AirsClean.MemAlignRomTable
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

private theorem memAlignRomMessage_eq_of_toElements_eq
    {left right : MemAlignRomMessage FGL}
    (h_elements : (toElements left).toArray = (toElements right).toArray) :
    left = right := by
  have h_vector : toElements left = toElements right := Vector.toArray_inj.mp h_elements
  calc
    left = fromElements (toElements left) := (ProvableType.fromElements_toElements left).symm
    _ = fromElements (toElements right) := congrArg fromElements h_vector
    _ = right := ProvableType.fromElements_toElements right

/-- Restore typed equality of the two six-slot bus-133 tuples from the raw
message equality supplied by finished-channel balance. -/
theorem memAlignRomMessage_eq_of_eval_pushed_provider_msg_eq
    {consumerMsg providerMsg : MemAlignRomMessage (Expression FGL)}
    {consumerEnv providerEnv : Environment FGL}
    (h_msg :
      (((MemAlignRomChannel.pushed providerMsg).toRaw).eval providerEnv).msg =
        (((MemAlignRomChannel.emitted (-1) consumerMsg).toRaw).eval consumerEnv).msg) :
    Eval.eval providerEnv providerMsg = Eval.eval consumerEnv consumerMsg := by
  have h_vec :
      Vector.map (Expression.eval providerEnv) (toElements providerMsg) =
        Vector.map (Expression.eval consumerEnv) (toElements consumerMsg) := by
    apply Vector.toArray_injective
    simpa [ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_from := congrArg
    (fun xs => (fromElements xs : MemAlignRomMessage FGL)) h_vec
  simpa [ProvableType.fromElements_eval_toElements] using h_from

/-- Project finished bus-133 balance from the full ensemble. -/
theorem memAlignRom_balanced_of_witness
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith MemAlignRomChannel.toRaw) := by
  have h := h_balanced MemAlignRomChannel.toRaw (by
    change MemAlignRomChannel.toRaw ∈
      [ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw
      , ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw
      , ZiskFv.Channels.OperationBus.OpBusChannel.toRaw
      , MemAlignRomChannel.toRaw
      , ZiskFv.Channels.SpecifiedRanges.SpecifiedRangesSliceChannel.toRaw ]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Every bus-133 interaction of MemAlign is the fixed negative consumer
emission.  The channel declaration carries no membership guarantee. -/
theorem memAlign_table_memAlignRom_mult_neg_one
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component) :
    ∀ {interaction : Interaction FGL},
      interaction ∈ table.interactionsWith MemAlignRomChannel.toRaw →
        interaction.mult = -1 := by
  intro interaction h_interaction
  refine ((Table.forall_interactionsWith_iff table MemAlignRomChannel.toRaw
    (fun interaction => interaction.mult = -1)).mpr ?_) interaction h_interaction
  intro row h_row abstractInteraction h_abstract h_channel
  have h_member :
      abstractInteraction ∈ table.component.operations.interactionsWith
        MemAlignRomChannel.toRaw := by
    simp [Operations.interactionsWith, h_abstract, h_channel]
  have h_interactions :
      table.component.operations.interactionsWith MemAlignRomChannel.toRaw =
        [((MemAlignRomChannel.emitted (-1)
          (ZiskFv.AirsClean.MemAlign.memAlignRomMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memAlignRomChannel
  simp [h_interactions] at h_member
  subst abstractInteraction
  rfl

/-- Finished-channel balance classifies the non-pull counterpart of a
MemAlign bus-133 consumer interaction as the unique static ROM provider. -/
theorem exists_memAlignRomSlice_provider_of_memAlign_interaction
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {memAlignTable : Table FGL}
    (h_memAlignTable : memAlignTable ∈ witness.allTables)
    {memAlignInteraction : Interaction FGL}
    (h_memAlignInteraction :
      memAlignInteraction ∈ memAlignTable.interactionsWith MemAlignRomChannel.toRaw)
    (h_active : memAlignInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemAlignRomChannel.toRaw,
      providerInteraction.msg = memAlignInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ providerTable ∈ witness.allTables,
          providerInteraction ∈ providerTable.interactionsWith MemAlignRomChannel.toRaw
            ∧ providerTable.component = ZiskFv.AirsClean.MemAlignRomSlice.component := by
  have h_memWitness :
      memAlignInteraction ∈ witness.interactionsWith MemAlignRomChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨memAlignTable, h_memAlignTable, h_memAlignInteraction⟩
  obtain ⟨providerInteraction, h_providerWitness, h_message, h_nonzero, h_nonpull⟩ :=
    exists_push_of_pull
      (witness.interactionsWith MemAlignRomChannel.toRaw)
      (memAlignRom_balanced_of_witness witness h_balanced)
      memAlignInteraction h_memWitness h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_providerWitness
  obtain ⟨providerTable, h_providerTable, h_providerInteraction⟩ := h_providerWitness
  have h_component_mem :
      providerTable.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_providerTable
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_boundary | h_alignRead | h_alignByte | h_align | h_range107 | h_rom | h_mem | h_ranges | h_regRange |
      h_div | h_mul | h_extension | h_binary | h_binaryAdd | h_main
  · have h_nil : providerTable.interactionsWith MemAlignRomChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [h_verifier]
      change MemAlignRomChannel.toRaw ∉ []
      simp
    simp [h_nil] at h_providerInteraction
  · simp [registerBoundary_table_interactionsWith_memAlignRom_nil h_boundary] at h_providerInteraction
  · simp [memAlignReadByte_table_interactionsWith_memAlignRom_nil h_alignRead] at h_providerInteraction
  · simp [memAlignByte_table_interactionsWith_memAlignRom_nil h_alignByte] at h_providerInteraction
  · exact False.elim (h_nonpull
      (memAlign_table_memAlignRom_mult_neg_one h_align h_providerInteraction))
  · simp [memAlignRangeSlice_table_interactionsWith_memAlignRom_nil h_range107] at h_providerInteraction
  · refine ⟨providerInteraction, ?_, h_message, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_rom⟩
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨providerTable, h_providerTable, h_providerInteraction⟩
  · simp [mem_table_interactionsWith_memAlignRom_nil h_mem] at h_providerInteraction
  · simp [specifiedRangesSlice_table_interactionsWith_memAlignRom_nil h_ranges] at h_providerInteraction
  · simp [registerStepRangeSlice_table_interactionsWith_memAlignRom_nil h_regRange] at h_providerInteraction
  · simp [arithDiv_table_interactionsWith_memAlignRom_nil h_div] at h_providerInteraction
  · simp [arithMul_table_interactionsWith_memAlignRom_nil h_mul] at h_providerInteraction
  · simp [staticBinaryExtension_table_interactionsWith_memAlignRom_nil h_extension] at h_providerInteraction
  · simp [staticBinary_table_interactionsWith_memAlignRom_nil h_binary] at h_providerInteraction
  · simp [binaryAdd_table_interactionsWith_memAlignRom_nil h_binaryAdd] at h_providerInteraction
  · simp [main_table_interactionsWith_memAlignRom_nil h_main] at h_providerInteraction

/-- Unpack a static bus-133 provider interaction to its concrete provider
row. -/
theorem exists_memAlignRomSlice_provider_row_of_interaction
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignRomSlice.component)
    {interaction : Interaction FGL}
    (h_interaction : interaction ∈ table.interactionsWith MemAlignRomChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemAlignRomChannel.pushed
          ZiskFv.AirsClean.MemAlignRomSlice.component.rowInputVar).toRaw).eval
          (table.environment row) := by
  have h_singleton :
      table.component.operations.interactionsWith MemAlignRomChannel.toRaw =
        [((MemAlignRomChannel.pushed
          ZiskFv.AirsClean.MemAlignRomSlice.component.rowInputVar).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.MemAlignRomSlice.component_interactionsWith_memAlignRomChannel
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_interaction
  exact h_interaction

/-- The constrained static provider row selected by bus-133 balance has the
exact extracted-ROM membership specification. -/
theorem memAlignRomTable_spec_of_memAlignRomSlice_provider_row
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_specs : witness.Spec)
    {providerTable : Table FGL}
    (h_providerTable : providerTable ∈ witness.allTables)
    (h_providerComponent :
      providerTable.component = ZiskFv.AirsClean.MemAlignRomSlice.component)
    {providerRow : Array FGL}
    (h_providerRow : providerRow ∈ providerTable.table) :
    memAlignRomTable.Spec
      (Eval.eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignRomSlice.component.rowInputVar) := by
  have h_spec := h_specs providerTable h_providerTable providerRow h_providerRow
  rw [h_providerComponent] at h_spec
  simpa only [Component.Spec, Component.rowInput, eval_varFromOffset_valueFromOffset,
    ZiskFv.AirsClean.MemAlignRomSlice.component,
    ZiskFv.AirsClean.MemAlignRomSlice.circuit,
    Component.rowInputVar] using h_spec

/-- A negative MemAlign h998 interaction is matched by balance to a concrete
static ROM row, whose exact membership is derived from witness constraints.
The message equality is raw-channel equality, preserving all six tuple slots
without a normalizing rewrite. -/
theorem exists_matched_memAlignRom_provider_row_of_memAlign_interaction
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {memAlignTable : Table FGL}
    (h_memAlignTable : memAlignTable ∈ witness.allTables)
    {memAlignInteraction : Interaction FGL}
    (h_memAlignInteraction :
      memAlignInteraction ∈ memAlignTable.interactionsWith MemAlignRomChannel.toRaw)
    (h_active : memAlignInteraction.mult = -1) :
    ∃ providerTable ∈ witness.allTables, ∃ providerRow ∈ providerTable.table,
      providerTable.component = ZiskFv.AirsClean.MemAlignRomSlice.component
        ∧ (((MemAlignRomChannel.pushed
          ZiskFv.AirsClean.MemAlignRomSlice.component.rowInputVar).toRaw).eval
            (providerTable.environment providerRow)).msg = memAlignInteraction.msg
        ∧ memAlignRomTable.Spec
          (Eval.eval (providerTable.environment providerRow)
            ZiskFv.AirsClean.MemAlignRomSlice.component.rowInputVar) := by
  obtain ⟨providerInteraction, _, h_message, _, _, providerTable, h_providerTable,
      h_providerInteraction, h_providerComponent⟩ :=
    exists_memAlignRomSlice_provider_of_memAlign_interaction witness h_balanced
      h_memAlignTable h_memAlignInteraction h_active
  obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
    exists_memAlignRomSlice_provider_row_of_interaction
      h_providerComponent h_providerInteraction
  refine ⟨providerTable, h_providerTable, providerRow, h_providerRow,
    h_providerComponent, ?_, ?_⟩
  · rw [← h_providerEval]
    exact h_message
  · exact memAlignRomTable_spec_of_memAlignRomSlice_provider_row
      (witness_spec_of_constraints witness h_constraints h_balanced)
      h_providerTable h_providerComponent h_providerRow

/-- The concrete h998 consumer interaction generated by any row of a
MemAlign table is present on the finished bus-133 channel. -/
theorem memAlign_row_mem_memAlignRom_interactionsWith
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component)
    {row : Array FGL}
    (h_row : row ∈ table.table) :
    ((MemAlignRomChannel.emitted (-1)
      (ZiskFv.AirsClean.MemAlign.memAlignRomMessageExpr
        ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
        (table.environment row) ∈ table.interactionsWith MemAlignRomChannel.toRaw := by
  have h_singleton :
      table.component.operations.interactionsWith MemAlignRomChannel.toRaw =
        [((MemAlignRomChannel.emitted (-1)
          (ZiskFv.AirsClean.MemAlign.memAlignRomMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memAlignRomChannel
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton]
  exact ⟨row, h_row, rfl⟩

/-- Exact MemAlign ROM membership for a concrete consumer row is derived
from the constrained static provider row selected by finished bus-133
balance. No membership fact is supplied by the consumer or caller. -/
theorem memAlignRomTable_spec_of_memAlign_row
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {memAlignTable : Table FGL}
    (h_memAlignTable : memAlignTable ∈ witness.allTables)
    (h_component : memAlignTable.component = ZiskFv.AirsClean.MemAlign.component)
    {memAlignRow : Array FGL}
    (h_memAlignRow : memAlignRow ∈ memAlignTable.table) :
    memAlignRomTable.Spec
      (ZiskFv.AirsClean.MemAlign.memAlignRomMessage
        (Eval.eval (memAlignTable.environment memAlignRow)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)) := by
  let consumerInteraction : Interaction FGL :=
    ((MemAlignRomChannel.emitted (-1)
      (ZiskFv.AirsClean.MemAlign.memAlignRomMessageExpr
        ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
      (memAlignTable.environment memAlignRow)
  have h_consumerInteraction :
      consumerInteraction ∈ memAlignTable.interactionsWith MemAlignRomChannel.toRaw := by
    exact memAlign_row_mem_memAlignRom_interactionsWith h_component h_memAlignRow
  obtain ⟨providerTable, h_providerTable, providerRow, h_providerRow, h_providerComponent,
      h_message, h_providerSpec⟩ :=
    exists_matched_memAlignRom_provider_row_of_memAlign_interaction witness h_constraints h_balanced
      h_memAlignTable h_consumerInteraction (by rfl)
  have h_typed := memAlignRomMessage_eq_of_eval_pushed_provider_msg_eq h_message
  rw [ZiskFv.AirsClean.MemAlign.eval_memAlignRomMessageExpr] at h_typed
  rw [← h_typed]
  exact h_providerSpec

/-- D3-indexed bus-133 membership. The selected static ROM row validates the
real h998 tuple whose `DELTA_PC` is read from Clean's intrinsic cyclic
successor, including the final effective row's successor at row zero. -/
theorem memAlignRomTable_spec_of_memAlign_cyclic_index
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {memAlignTable : Table FGL}
    (h_memAlignTable : memAlignTable ∈ witness.allTables)
    (h_component : memAlignTable.component = ZiskFv.AirsClean.MemAlign.component)
    (h_cyclic : memAlignTable.CyclicSuccessorTransitionConstraints)
    (index : Fin memAlignTable.length) :
    memAlignRomTable.Spec
      (ZiskFv.AirsClean.MemAlign.memAlignRomSuccessorMessage
        (ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment
          (memAlignTable.environmentAt index))
        (ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment
          (memAlignTable.successorEnvironment index))) := by
  let rawIndex : Fin memAlignTable.table.length :=
    ⟨index.val, by simpa only [Table.table_length] using index.isLt⟩
  let rawRow := memAlignTable.table.get rawIndex
  have h_rawRow : rawRow ∈ memAlignTable.table := List.get_mem _ _
  have h_spec := memAlignRomTable_spec_of_memAlign_row witness h_constraints h_balanced
    h_memAlignTable h_component h_rawRow
  have h_spec_current :
      memAlignRomTable.Spec
        (ZiskFv.AirsClean.MemAlign.memAlignRomMessage
          (ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment
            (memAlignTable.environmentAt index))) := by
    simpa only [rawRow, rawIndex, Table.environmentAt,
      ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment,
      Component.rowInputVar, eval_varFromOffset_valueFromOffset] using h_spec
  rw [ZiskFv.AirsClean.MemAlign.memAlignRomMessage_eq_successorMessage_of_delta_pc_eq
    _ _ (ZiskFv.AirsClean.MemAlign.delta_pc_eq_successor_pc_sub_pc
      h_component h_cyclic index)] at h_spec_current
  exact h_spec_current

end ZiskFv.AirsClean.FullEnsemble
