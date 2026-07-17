import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance.RangeProviderMatch

/-!
# Derived mutable-Mem segment range facts

The two `distance_base` 16-bit facts are recovered from the accepted Mem
table's source-linked bus-103 consumer interactions, finished-channel balance,
and the static `SpecifiedRangesSlice` provider.  No completeness-side prover
assumption participates in this derivation.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.SpecifiedRanges
  (SpecifiedRangeMessage SpecifiedRangesSliceChannel memDistanceMessage)

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

/-- The indexed live Mem transition carries the source bridge for every row
of the selected mutable-Mem table. -/
theorem AcceptedZiskTrace.memReplayRangeSidecarBridge
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness)
    (idx : Fin (trace.memReplayTable h_present).length) :
    ZiskFv.AirsClean.Mem.memRangeSidecarBridge
      ((trace.memReplayTable h_present).environmentAt idx) := by
  have h_transition := trace.transitions_hold (trace.memReplayTable h_present)
    (trace.mem_replay_table h_present).2.1 idx
  have h_component : (trace.memReplayTable h_present).component =
      ZiskFv.AirsClean.Mem.componentWithDualMemBus := by
    simpa [AcceptedZiskTrace.memReplayTable] using (trace.mem_replay_table h_present).2.2.1
  rw [h_component] at h_transition
  change ZiskFv.AirsClean.Mem.generatedTransition ZiskFv.AirsClean.Mem.memFixedColumns
    idx.val ((trace.memReplayTable h_present).previousEnvironment idx)
      ((trace.memReplayTable h_present).environmentAt idx) at h_transition
  have h_generated :=
    (generatedTransition_iff_canonicalTableData (trace.memReplayTable h_present)
      (trace.mem_replay_table h_present).2.2.1 idx).mp
      h_transition
  exact h_generated.2.2

private theorem AcceptedZiskTrace.memReplayDistanceBase0Range
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec
      (ZiskFv.AirsClean.Mem.proverDataScalar
        (trace.memReplayTable h_present).data
        ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.distanceBase0) := by
  let table := trace.memReplayTable h_present
  have h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus := by
    simpa [table, AcceptedZiskTrace.memReplayTable] using
      (trace.mem_replay_table h_present).2.2.1
  let idx : Fin table.length := ⟨0, by
    simpa only [Table.table_length] using (trace.mem_replay_table h_present).2.2.2⟩
  let rowIdx : Fin table.table.length := ⟨idx.val, by
    simpa only [Table.table_length] using idx.isLt⟩
  let row := table.table.get rowIdx
  have h_row : row ∈ table.table := List.mem_iff_get.mpr ⟨rowIdx, rfl⟩
  have h_bridge := trace.memReplayRangeSidecarBridge h_present idx
  have h_source : table.environment row ZiskFv.AirsClean.Mem.memDistanceBase0Expr =
      ZiskFv.AirsClean.Mem.proverDataScalar table.data
        ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.distanceBase0 := by
    simpa [table, idx, row, Table.environmentAt] using h_bridge.1
  let consumerInteraction : Interaction FGL :=
    ((SpecifiedRangesSliceChannel.emitted (-1)
      (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceBase0Expr)).toRaw).eval
      (table.environment row)
  have h_consumer :
      consumerInteraction ∈ table.interactionsWith SpecifiedRangesSliceChannel.toRaw := by
    rw [Table.interactionsWith]
    refine List.mem_flatMap.mpr ⟨row, h_row, ?_⟩
    rw [Operations.interactionValuesWith_eq_map]
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
    rw [h_interactions]
    simp [consumerInteraction]
  have h_active : consumerInteraction.mult = -1 := by
    simp [consumerInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted, Expression.eval]
  obtain ⟨providerInteraction, _h_providerWitness, h_message, h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_specifiedRangesSlice_provider_of_mem_interaction
      trace.witness trace.channels_balanced (trace.mem_replay_table h_present).2.1 h_consumer h_active
  have h_consumerMessage : consumerInteraction.msg =
      (toElements (memDistanceMessage
        (ZiskFv.AirsClean.Mem.proverDataScalar table.data
          ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.distanceBase0))).toArray := by
    change (Vector.map (Expression.eval (table.environment row))
      (toElements (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceBase0Expr))).toArray = _
    rw [← ProvableType.toElements_eval, eval_memDistanceMessage]
    simp [h_source]
  apply rangeTable16_spec_of_specifiedRangesSlice_provider_interaction trace.spec_holds
    h_providerTable h_providerComponent h_providerInteraction
  rw [h_message, h_consumerMessage]

private theorem AcceptedZiskTrace.memReplayDistanceBase1Range
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec
      (ZiskFv.AirsClean.Mem.proverDataScalar
        (trace.memReplayTable h_present).data
        ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.distanceBase1) := by
  let table := trace.memReplayTable h_present
  have h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus := by
    simpa [table, AcceptedZiskTrace.memReplayTable] using
      (trace.mem_replay_table h_present).2.2.1
  let idx : Fin table.length := ⟨0, by
    simpa only [Table.table_length] using (trace.mem_replay_table h_present).2.2.2⟩
  let rowIdx : Fin table.table.length := ⟨idx.val, by
    simpa only [Table.table_length] using idx.isLt⟩
  let row := table.table.get rowIdx
  have h_row : row ∈ table.table := List.mem_iff_get.mpr ⟨rowIdx, rfl⟩
  have h_bridge := trace.memReplayRangeSidecarBridge h_present idx
  have h_source : table.environment row ZiskFv.AirsClean.Mem.memDistanceBase1Expr =
      ZiskFv.AirsClean.Mem.proverDataScalar table.data
        ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.distanceBase1 := by
    simpa [table, idx, row, Table.environmentAt] using h_bridge.2.1
  let consumerInteraction : Interaction FGL :=
    ((SpecifiedRangesSliceChannel.emitted (-1)
      (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceBase1Expr)).toRaw).eval
      (table.environment row)
  have h_consumer :
      consumerInteraction ∈ table.interactionsWith SpecifiedRangesSliceChannel.toRaw := by
    rw [Table.interactionsWith]
    refine List.mem_flatMap.mpr ⟨row, h_row, ?_⟩
    rw [Operations.interactionValuesWith_eq_map]
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
    rw [h_interactions]
    simp [consumerInteraction]
  have h_active : consumerInteraction.mult = -1 := by
    simp [consumerInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted, emitted, Expression.eval]
  obtain ⟨providerInteraction, _h_providerWitness, h_message, h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_specifiedRangesSlice_provider_of_mem_interaction
      trace.witness trace.channels_balanced (trace.mem_replay_table h_present).2.1 h_consumer h_active
  have h_consumerMessage : consumerInteraction.msg =
      (toElements (memDistanceMessage
        (ZiskFv.AirsClean.Mem.proverDataScalar table.data
          ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.distanceBase1))).toArray := by
    change (Vector.map (Expression.eval (table.environment row))
      (toElements (memDistanceMessage ZiskFv.AirsClean.Mem.memDistanceBase1Expr))).toArray = _
    rw [← ProvableType.toElements_eval, eval_memDistanceMessage]
    simp [h_source]
  apply rangeTable16_spec_of_specifiedRangesSlice_provider_interaction trace.spec_holds
    h_providerTable h_providerComponent h_providerInteraction
  rw [h_message, h_consumerMessage]

/-- The selected mutable-Mem segment's two base-distance chunks are 16-bit.
This derives the former accepted-trace promise entirely from the accepted
constraints, finished bus-103 balance, and indexed transition source bridge. -/
theorem AcceptedZiskTrace.memReplaySegmentRanges
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    MemSegmentGeneratedRangeFacts
      (memSegmentOfTableData (trace.memReplayTable h_present)) := by
  refine ⟨?_, ?_⟩
  · exact trace.memReplayDistanceBase0Range h_present
  · exact trace.memReplayDistanceBase1Range h_present

/-- The accepted Mem replay bridge selected when the accepted witness has
mutable-Mem rows. Its segment range source is now derived from the accepted
constraints, finished bus-103 balance, and indexed transition bridge. -/
def AcceptedZiskTrace.memReplayBridge {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    FullWitnessMemReplayBridge trace.witness (trace.memReplayRows h_present) :=
  fullWitnessMemReplayBridge_of_memTable_with_fixedColumns
    (segment := memSegmentOfTableData (trace.memReplayTable h_present))
    (permutation := memPermutationOfTableData (trace.memReplayTable h_present))
    (gsum := ZiskFv.AirsClean.Mem.memSidecarGsumOfProverData
      (trace.memReplayTable h_present).data)
    (im0 := ZiskFv.AirsClean.Mem.memSidecarIm0OfProverData
      (trace.memReplayTable h_present).data)
    (im1 := ZiskFv.AirsClean.Mem.memSidecarIm1OfProverData
      (trace.memReplayTable h_present).data)
    (trace.mem_replay_table h_present).2.1
    (trace.mem_replay_table h_present).2.2.1
    (by
      simpa only [memOfTableData] using
        generatedAt_of_memTableGeneratedConstraintFacts
          (trace.memReplayGeneratedConstraintFacts h_present))
    (by
      simpa only [memOfTableData] using trace.memReplayRowRanges h_present)
    (trace.memReplaySegmentRanges h_present)
    (memTableGeneratedFixedColumnFacts_of_component_fixedColumns
      (trace.memReplayTable h_present) (trace.mem_replay_table h_present).2.2.1)
    (trace.mem_replay_table h_present).2.2.2

@[simp]
theorem AcceptedZiskTrace.memReplayBridge_table {n : Nat}
    (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    (trace.memReplayBridge h_present).table = trace.memReplayTable h_present :=
  rfl

end ZiskFv.Compliance
