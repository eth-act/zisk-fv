import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.Compliance.EnsembleWitnessBuilder

/-!
# Concrete bus-103 range-wiring witness

This acceptance witness isolates the two real full-ensemble components that
participate in Mem's source-linked 16-bit range channel: the live Mem consumer
and the constructive `SpecifiedRanges` provider. It has no accepted-trace
fields and no caller-supplied range fact.
-/

open Goldilocks
open Air.Flat
open ZiskFv.Channels.SpecifiedRanges
  (SpecifiedRangeMessage SpecifiedRangesSliceChannel memDistanceMessage)

namespace ZiskFv.Compliance.RangeWiringWitness

open ZiskFv.AirsClean.Mem

private def demoMemTable : Table FGL where
  component := ZiskFv.AirsClean.Mem.componentWithDualMemBus
  rawRows := [memRawRowWithProverData distanceBase0DemoData distanceBase0DemoRow]
  data := distanceBase0DemoData
  raw_uniform_width := by
    intro raw h_raw
    simp only [List.mem_singleton] at h_raw
    subst raw
    simp [ZiskFv.AirsClean.Mem.componentWithDualMemBus, memRawRowWithProverData]
  fixed_domain := by
    intro columns h_columns
    have h_columns' : columns = memFixedColumns := by
      simpa [ZiskFv.AirsClean.Mem.componentWithDualMemBus] using h_columns.symm
    subst columns
    norm_num [memFixedColumns, memFixedCapacity]

private theorem demoMemTable_effectiveRows :
    demoMemTable.table =
      [memFixedColumns.materialize 0
        (memRawRowWithProverData distanceBase0DemoData distanceBase0DemoRow)] := by
  simp [demoMemTable, Table.table, ZiskFv.AirsClean.Mem.componentWithDualMemBus]

private def demoProviderTable : Table FGL where
  component := ZiskFv.AirsClean.SpecifiedRangesSlice.component
  rawRows := [#[7], #[0], #[0], #[0]]
  data := distanceBase0DemoData
  raw_uniform_width := by
    intro raw h_raw
    simp at h_raw
    rcases h_raw with rfl | rfl <;> rfl
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.SpecifiedRangesSlice.component] at h_columns

private def demoEnsemble : Ensemble FGL unit where
  tables := [ ZiskFv.AirsClean.Mem.componentWithDualMemBus
    , ZiskFv.AirsClean.SpecifiedRangesSlice.component ]
  channels := [SpecifiedRangesSliceChannel.toRaw]

private def demoWitness : EnsembleWitness demoEnsemble where
  tables := [demoMemTable, demoProviderTable]
  data := distanceBase0DemoData
  publicInput := ()
  same_length := by
    simp [demoEnsemble]
  same_circuits := by
    intro i h_i
    have h_i' : i < 2 := by
      simpa [demoEnsemble] using h_i
    interval_cases i <;> rfl
  same_data := by
    intro table h_table
    simp at h_table
    rcases h_table with rfl | rfl <;> rfl

private def demoZeroMessage : SpecifiedRangeMessage FGL := memDistanceMessage 0

private def consumerValue (msg : SpecifiedRangeMessage FGL) : Interaction FGL where
  channel := SpecifiedRangesSliceChannel.toRaw
  mult := -1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

private def demoInteractions : List (Interaction FGL) :=
  [ consumerValue distanceBase0DemoMessage
  , consumerValue demoZeroMessage
  , consumerValue demoZeroMessage
  , consumerValue demoZeroMessage
  , SpecifiedRangesSliceChannel.pushedValue distanceBase0DemoMessage
  , SpecifiedRangesSliceChannel.pushedValue demoZeroMessage
  , SpecifiedRangesSliceChannel.pushedValue demoZeroMessage
  , SpecifiedRangesSliceChannel.pushedValue demoZeroMessage ]

private def demoMemEnvironment : Environment FGL :=
  Environment.fromArray
    (memFixedColumns.materialize 0
      (memRawRowWithProverData distanceBase0DemoData distanceBase0DemoRow))
    distanceBase0DemoData

private theorem eval_memDistanceMessage
    (env : Environment FGL) (value : Expression FGL) :
    Eval.eval env (memDistanceMessage value) =
      memDistanceMessage (Expression.eval env value) := by
  rw [SpecifiedRangeMessage.mk.injEq]
  simp only [memDistanceMessage, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
    Expression.eval]
  repeat constructor

private theorem eval_demoDistanceBase0Message :
    Eval.eval demoMemEnvironment (memDistanceMessage memDistanceBase0Expr) =
      distanceBase0DemoMessage := by
  rw [eval_memDistanceMessage]
  rfl

private theorem eval_demoDistanceBase1Message :
    Eval.eval demoMemEnvironment (memDistanceMessage memDistanceBase1Expr) = demoZeroMessage := by
  rw [eval_memDistanceMessage]
  unfold demoMemEnvironment
  rw [eval_memDistanceBase1Expr_materialize]
  have h_key : MemRawSidecarDataKey.Segment.distanceBase1 ≠
      MemRawSidecarDataKey.Segment.distanceBase0 := by decide
  simp [distanceBase0DemoData, proverDataScalar, proverDataColumn, demoZeroMessage, h_key]

private theorem eval_demoDistanceEnd0Message :
    Eval.eval demoMemEnvironment (memDistanceMessage memDistanceEnd0Expr) = demoZeroMessage := by
  rw [eval_memDistanceMessage]
  unfold demoMemEnvironment
  rw [eval_memDistanceEnd0Expr_materialize]
  have h_key : MemRawSidecarDataKey.Segment.distanceEnd0 ≠
      MemRawSidecarDataKey.Segment.distanceBase0 := by decide
  simp [distanceBase0DemoData, proverDataScalar, proverDataColumn, demoZeroMessage, h_key]

private theorem eval_demoDistanceEnd1Message :
    Eval.eval demoMemEnvironment (memDistanceMessage memDistanceEnd1Expr) = demoZeroMessage := by
  rw [eval_memDistanceMessage]
  unfold demoMemEnvironment
  rw [eval_memDistanceEnd1Expr_materialize]
  have h_key : MemRawSidecarDataKey.Segment.distanceEnd1 ≠
      MemRawSidecarDataKey.Segment.distanceBase0 := by decide
  simp [distanceBase0DemoData, proverDataScalar, proverDataColumn, demoZeroMessage, h_key]

private theorem demoMemTable_rangeInteractions :
    demoMemTable.interactionsWith SpecifiedRangesSliceChannel.toRaw =
      [ consumerValue distanceBase0DemoMessage
      , consumerValue demoZeroMessage
      , consumerValue demoZeroMessage
      , consumerValue demoZeroMessage ] := by
  rw [Table.interactionsWith, demoMemTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.interactionValuesWith
        SpecifiedRangesSliceChannel.toRaw demoMemEnvironment = _
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_rangeChannel]
  simp only [List.map_cons, List.map_nil]
  have h_base0 :
      ((SpecifiedRangesSliceChannel.emitted (-1)
        (memDistanceMessage memDistanceBase0Expr)).toRaw).eval demoMemEnvironment =
        consumerValue distanceBase0DemoMessage := by
    simp [consumerValue, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · rfl
    · rw [← Vector.toArray_map, ← ProvableType.toElements_eval,
        eval_demoDistanceBase0Message]
  have h_base1 :
      ((SpecifiedRangesSliceChannel.emitted (-1)
        (memDistanceMessage memDistanceBase1Expr)).toRaw).eval demoMemEnvironment =
        consumerValue demoZeroMessage := by
    simp [consumerValue, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · rfl
    · rw [← Vector.toArray_map, ← ProvableType.toElements_eval,
        eval_demoDistanceBase1Message]
  have h_end0 :
      ((SpecifiedRangesSliceChannel.emitted (-1)
        (memDistanceMessage memDistanceEnd0Expr)).toRaw).eval demoMemEnvironment =
        consumerValue demoZeroMessage := by
    simp [consumerValue, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · rfl
    · rw [← Vector.toArray_map, ← ProvableType.toElements_eval,
        eval_demoDistanceEnd0Message]
  have h_end1 :
      ((SpecifiedRangesSliceChannel.emitted (-1)
        (memDistanceMessage memDistanceEnd1Expr)).toRaw).eval demoMemEnvironment =
        consumerValue demoZeroMessage := by
    simp [consumerValue, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted]
    constructor
    · rfl
    · rw [← Vector.toArray_map, ← ProvableType.toElements_eval,
        eval_demoDistanceEnd1Message]
  rw [h_base0, h_base1, h_end0, h_end1]

private theorem demoProviderTable_rangeInteractions :
    demoProviderTable.interactionsWith SpecifiedRangesSliceChannel.toRaw =
      [ SpecifiedRangesSliceChannel.pushedValue distanceBase0DemoMessage
      , SpecifiedRangesSliceChannel.pushedValue demoZeroMessage
      , SpecifiedRangesSliceChannel.pushedValue demoZeroMessage
      , SpecifiedRangesSliceChannel.pushedValue demoZeroMessage ] := by
  rw [Table.interactionsWith]
  change List.flatMap (fun row =>
    ZiskFv.AirsClean.SpecifiedRangesSlice.component.operations.interactionValuesWith
      SpecifiedRangesSliceChannel.toRaw (Environment.fromArray row distanceBase0DemoData))
    [#[7], #[0], #[0], #[0]] = _
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp_rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.SpecifiedRangesSlice.component_interactionsWith_rangeChannel]
  simp only [List.map_cons, List.map_nil]
  simp_rw [Channel.eval_pushed, eval_memDistanceMessage]
  change
    [ SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage 7)
    , SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage 0)
    , SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage 0)
    , SpecifiedRangesSliceChannel.pushedValue (memDistanceMessage 0) ] = _
  rfl

private theorem demoWitness_rangeInteractions :
    demoWitness.interactionsWith SpecifiedRangesSliceChannel.toRaw = demoInteractions := by
  rw [EnsembleWitness.interactionsWith_of_verifier_empty (by rfl)]
  change [demoMemTable, demoProviderTable].flatMap
    (·.interactionsWith SpecifiedRangesSliceChannel.toRaw) = demoInteractions
  simp [demoInteractions, demoMemTable_rangeInteractions,
    demoProviderTable_rangeInteractions]

private theorem demoInteractions_balanced : BalancedInteractions demoInteractions := by
  constructor
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro msg
    have h_messages : (toElements distanceBase0DemoMessage).toArray ≠
        (toElements demoZeroMessage).toArray := by
      change #[103, (7 : FGL)] ≠ #[103, (0 : FGL)]
      decide
    have h_messages_symm : (toElements demoZeroMessage).toArray ≠
        (toElements distanceBase0DemoMessage).toArray := fun h => h_messages h.symm
    by_cases h_base : (toElements distanceBase0DemoMessage).toArray = msg
    · subst msg
      simp [demoInteractions, consumerValue, balanceOf, Channel.pushedValue, h_messages_symm]
    · by_cases h_zero : (toElements demoZeroMessage).toArray = msg
      · subst msg
        simp [demoInteractions, consumerValue, balanceOf, Channel.pushedValue, h_base]
        ring
      · simp [demoInteractions, consumerValue, balanceOf, Channel.pushedValue,
          h_base, h_zero]

private theorem demoBaseProviderMembership :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec distanceBase0DemoValue := by
  rw [distanceBase0DemoValue_eq]
  norm_num [ZiskFv.AirsClean.RangeTables.rangeTable16,
    ZiskFv.AirsClean.RangeTables.rangeStaticTable]

private theorem demoZeroProviderMembership :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec 0 := by
  norm_num [ZiskFv.AirsClean.RangeTables.rangeTable16,
    ZiskFv.AirsClean.RangeTables.rangeStaticTable]

private theorem demoInteractions_requirements :
    ∀ interaction ∈ demoInteractions, interaction.Requirements distanceBase0DemoData := by
  intro interaction h_interaction
  simp only [demoInteractions, List.mem_cons] at h_interaction
  rcases h_interaction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_empty
  · change (-1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees distanceBase0DemoMessage distanceBase0DemoData
    simp
  · change (-1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees demoZeroMessage distanceBase0DemoData
    simp
  · change (-1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees demoZeroMessage distanceBase0DemoData
    simp
  · change (-1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees demoZeroMessage distanceBase0DemoData
    simp
  · change (1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees distanceBase0DemoMessage distanceBase0DemoData
    intro _
    exact ⟨rfl, demoBaseProviderMembership⟩
  · change (1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees demoZeroMessage distanceBase0DemoData
    intro _
    exact ⟨rfl, demoZeroProviderMembership⟩
  · change (1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees demoZeroMessage distanceBase0DemoData
    intro _
    exact ⟨rfl, demoZeroProviderMembership⟩
  · change (1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees demoZeroMessage distanceBase0DemoData
    intro _
    exact ⟨rfl, demoZeroProviderMembership⟩
  · simp at h_empty

private theorem demoStaticProvider_membership_of_balance_match
    (provider : Interaction FGL)
    (h_provider : provider ∈ demoInteractions)
    (h_message : provider.msg = (toElements distanceBase0DemoMessage).toArray)
    (h_nonnegative : provider.mult ≠ -1) :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec distanceBase0DemoValue := by
  have h_messages : (toElements distanceBase0DemoMessage).toArray ≠
      (toElements demoZeroMessage).toArray := by
    change #[103, (7 : FGL)] ≠ #[103, (0 : FGL)]
    decide
  simp only [demoInteractions, List.mem_cons] at h_provider
  rcases h_provider with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_empty
  · exact (h_nonnegative rfl).elim
  · exact (h_nonnegative rfl).elim
  · exact (h_nonnegative rfl).elim
  · exact (h_nonnegative rfl).elim
  · have h_requirement := demoInteractions_requirements
      (SpecifiedRangesSliceChannel.pushedValue distanceBase0DemoMessage) (by
        simp [demoInteractions])
    change (1 : FGL) ≠ -1 →
      SpecifiedRangesSliceChannel.Guarantees distanceBase0DemoMessage distanceBase0DemoData
      at h_requirement
    exact ZiskFv.Channels.SpecifiedRanges.memDistanceMessage_guarantees_iff
      distanceBase0DemoValue distanceBase0DemoData |>.mp (h_requirement h_nonnegative)
  · exact (h_messages h_message.symm).elim
  · exact (h_messages h_message.symm).elim
  · exact (h_messages h_message.symm).elim
  · simp at h_empty

/-- PR 2a's non-empty acceptance witness: the selected Mem table emits the
`ProverData`-sourced c29 value with multiplicity `-1`; bus-103 balance finds
its non-negative static-provider counterpart, whose requirement yields the
16-bit membership fact. -/
theorem distanceBase0Demo_membership_from_balancedWitness :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec distanceBase0DemoValue := by
  have h_balanced :
      BalancedInteractions
        (demoWitness.interactionsWith SpecifiedRangesSliceChannel.toRaw) := by
    rw [demoWitness_rangeInteractions]
    exact demoInteractions_balanced
  have h_consumer :
      consumerValue distanceBase0DemoMessage ∈
        demoWitness.interactionsWith SpecifiedRangesSliceChannel.toRaw := by
    rw [demoWitness_rangeInteractions]
    simp [demoInteractions]
  obtain ⟨provider, h_provider, h_message, h_nonnegative, _⟩ :=
    exists_nonzero_push_of_pull
      (demoWitness.interactionsWith SpecifiedRangesSliceChannel.toRaw)
      h_balanced (consumerValue distanceBase0DemoMessage) h_consumer rfl
  have h_provider_demo : provider ∈ demoInteractions := by
    rw [← demoWitness_rangeInteractions]
    exact h_provider
  have h_message' : provider.msg = (toElements distanceBase0DemoMessage).toArray := by
    simpa [consumerValue] using h_message
  exact demoStaticProvider_membership_of_balance_match provider h_provider_demo h_message'
    h_nonnegative

end ZiskFv.Compliance.RangeWiringWitness
