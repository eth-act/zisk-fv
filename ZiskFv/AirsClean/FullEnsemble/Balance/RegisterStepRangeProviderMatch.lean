import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction

/-!
# Full-ensemble bus-102 provider match

The bus-102 channel (`main.pil:333-335`, 24-bit) carries the **register-step descent**: for each
active register slot a Main row pulls `<slot>_mem_step - <slot>_reg_prev_mem_step - 1`, and the
`RegisterStepRangeSlice` provider pushes the same distance under its own `Spec`, which is
`rangeTable24.Spec`.

This file is the bus-102 twin of `RangeProviderMatch.lean`: balance turns a Main pull into a
same-message provider push, and the provider's `Spec` turns that push into the concrete 24-bit
membership fact. That fact is what rules out the register-telescope cycles described in #342 --
without it `a_reg_prev_mem_step` is a free witness column and two rows can point at each other's
timestamps.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.SpecifiedRanges
  (SpecifiedRangeMessage SpecifiedRangesSliceChannel RegisterStepRangeChannel registerStepMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

private theorem registerStepRangeChannel_ne_memBus :
    RegisterStepRangeChannel.toRaw ≠ MemBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "MemoryBus" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_opBus :
    RegisterStepRangeChannel.toRaw ≠ OpBusChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "OperationBus" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_memAlignRom :
    RegisterStepRangeChannel.toRaw ≠ MemAlignRomChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "MemAlignRom133" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_specifiedRanges :
    RegisterStepRangeChannel.toRaw ≠ SpecifiedRangesSliceChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "SpecifiedRangesSlice103" at h_name
  simp at h_name

private theorem registerStepRangeChannel_ne_memAlignRange :
    RegisterStepRangeChannel.toRaw ≠ ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw := by
  intro h
  have h_name := congrArg (fun channel : RawChannel FGL => channel.name) h
  change "SpecifiedRangesSlice102" = "MemAlignRange107" at h_name
  simp at h_name

/-- The bus-102 interactions of an accepted witness balance, because the channel is one of the
six the ensemble finishes. -/
theorem registerStepRange_balanced_of_witness
    {length : Nat} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith RegisterStepRangeChannel.toRaw) := by
  have h := h_balanced RegisterStepRangeChannel.toRaw (by
    change RegisterStepRangeChannel.toRaw ∈
      [RegisterStepRangeChannel.toRaw,
        ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw,
        MemBusChannel.toRaw, OpBusChannel.toRaw, MemAlignRomChannel.toRaw,
        SpecifiedRangesSliceChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Every bus-102 interaction of the provider slice is a single push carrying that row's value. -/
theorem exists_registerStepRangeSlice_provider_row_of_interaction
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component)
    {interaction : Interaction FGL}
    (h_interaction : interaction ∈ table.interactionsWith RegisterStepRangeChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((RegisterStepRangeChannel.pushed
          (registerStepMessage
            ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  have h_singleton :
      table.component.operations.interactionsWith RegisterStepRangeChannel.toRaw =
        [((RegisterStepRangeChannel.pushed
          (registerStepMessage
            ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.RegisterStepRangeSlice.component_interactionsWith_rangeChannel
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_interaction
  exact h_interaction

/-- **The descent fact.** A bus-102 provider push carrying `value` forces
`rangeTable24.Spec value`: the provider's `Spec` is exactly 24-bit static-table membership, and
an accepted witness satisfies every table's `Spec`. -/
theorem rangeTable24_spec_of_registerStepRange_provider_interaction
    {length : Nat} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_specs : witness.Spec)
    {providerTable : Table FGL}
    (h_providerTable : providerTable ∈ witness.allTables)
    (h_providerComponent :
      providerTable.component = ZiskFv.AirsClean.RegisterStepRangeSlice.component)
    {providerInteraction : Interaction FGL}
    (h_providerInteraction :
      providerInteraction ∈ providerTable.interactionsWith RegisterStepRangeChannel.toRaw)
    {value : FGL}
    (h_message : providerInteraction.msg = (toElements (registerStepMessage value)).toArray) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec value := by
  obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
    exists_registerStepRangeSlice_provider_row_of_interaction
      h_providerComponent h_providerInteraction
  have h_spec := h_specs providerTable h_providerTable providerRow h_providerRow
  rw [h_providerComponent] at h_spec
  rw [h_providerEval] at h_message
  have h_eval_message (env : Environment FGL) (value : Expression FGL) :
      Eval.eval env (registerStepMessage value) =
        registerStepMessage (Expression.eval env value) := by
    rw [SpecifiedRangeMessage.mk.injEq]
    simp only [registerStepMessage, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
      Expression.eval]
    repeat constructor
  rw [Channel.eval_pushed, h_eval_message] at h_message
  have h_value := congrArg (fun elements : Array FGL => elements[1]!) h_message
  have h_value' : valueFromOffset field 0 (providerTable.environment providerRow) = value := by
    simpa [Channel.pushedValue, registerStepMessage,
      ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
      ProvableStruct.components, ProvableStruct.toComponents,
      ProvableStruct.componentsToElements,
      ZiskFv.AirsClean.RegisterStepRangeSlice.component, Component.rowInputVar,
      ProvableType.varFromOffset] using h_value
  have h_providerSpec : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec
      (valueFromOffset field 0 (providerTable.environment providerRow)) := by
    simpa [Component.Spec, Component.rowInput,
      ZiskFv.AirsClean.RegisterStepRangeSlice.component,
      ZiskFv.AirsClean.RegisterStepRangeSlice.circuit,
      Component.rowInputVar] using h_spec
  simpa [h_value'] using h_providerSpec

end ZiskFv.AirsClean.FullEnsemble
