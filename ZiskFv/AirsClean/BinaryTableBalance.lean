import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryExtension.ExtractedWiring
import ZiskFv.AirsClean.BinaryExtension.StaticCircuit
import ZiskFv.AirsClean.BinaryTableSlice
import ZiskFv.AirsClean.BinaryExtensionTableSlice
import ZiskFv.AirsClean.PackedVirtualTableSources
import ZiskFv.AirsClean.BinaryTablePrefix
import ZiskFv.AirsClean.BinaryTableRequests
import Clean.Air.FlatEnsemble

/-!
# Source Binary-table providers and their actual eight-route consumers

This local ensemble finishes buses 125 and 124. The result below is derived
from its checked operations and balance, not from `ProverAssumptions`, a
channel guarantee of membership, or a detached static-lookup consumer.
The operation bus is deliberately not finished by this local slice.
-/

namespace ZiskFv.AirsClean.BinaryTableBalance

open Goldilocks Air.Flat
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable

/-- Both actual negative-emission consumers and both source-multiplicity
providers. The provider fixed schemas own all seven tuple slots. -/
def ensemble : Ensemble FGL unit where
  tables := [Binary.tableConsumerComponent, BinaryExtension.shiftTableConsumerComponent,
    BinaryTableSlice.sourceComponent, BinaryExtensionTableSlice.sourceComponent]
  channels := [BinaryTableChannel.toRaw, BinaryExtensionTableChannel.toRaw]

/-- All eight actual Binary routes, including the special first/last-byte
position and carry/mode encodings. -/
def binaryMessage (row : Var Binary.BinaryRow FGL) : Fin 8 →
    BinaryTableMessage (Expression FGL)
  | ⟨0, _⟩ => Binary.lookupMessage0 row
  | ⟨1, _⟩ => Binary.lookupMessage1 row
  | ⟨2, _⟩ => Binary.lookupMessage2 row
  | ⟨3, _⟩ => Binary.lookupMessage3 row
  | ⟨4, _⟩ => Binary.lookupMessage4 row
  | ⟨5, _⟩ => Binary.lookupMessage5 row
  | ⟨6, _⟩ => Binary.lookupMessage6 row
  | ⟨7, _⟩ => Binary.lookupMessage7 row

theorem binaryMessage_mem (index : Fin 8) :
    (BinaryTableChannel.emitted (-1)
      (binaryMessage Binary.tableConsumerComponent.rowInputVar index)).toRaw ∈
        Binary.tableConsumerComponent.operations.interactionsWith
          BinaryTableChannel.toRaw := by
  rw [Binary.tableConsumerComponent_interactionsWith_binaryTableChannel]
  fin_cases index <;> simp [binaryMessage]

private theorem component_cases {component : Component FGL}
    (h : component ∈ ensemble.allTables) :
    component = ensemble.verifierTable ∨
    component = Binary.tableConsumerComponent ∨
    component = BinaryExtension.shiftTableConsumerComponent ∨
    component = BinaryTableSlice.sourceComponent ∨
    component = BinaryExtensionTableSlice.sourceComponent := by
  simpa only [ensemble, Ensemble.allTables, List.mem_cons, List.not_mem_nil,
    or_false] using h

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

/-- Classification is proved from the concrete component list, not supplied
as an aggregate promise by a caller. The source multiplicity may be any field
value; only balance distinguishes a nonzero non-pull from a consumer. -/
theorem binary_nonpull_source (w : EnsembleWitness ensemble)
    {table : Table FGL} (ht : table ∈ w.allTables)
    {interaction : Interaction FGL}
    (hi : interaction ∈ table.interactionsWith BinaryTableChannel.toRaw)
    (hn : interaction.mult ≠ -1) :
    table.component = BinaryTableSlice.sourceComponent := by
  rcases component_cases (EnsembleWitness.mem_allTables_component_of_mem_allTables ht) with
    hc | hc | hc | hc | hc
  · have he : table.interactionsWith BinaryTableChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [hc]
      simp [ensemble, Ensemble.verifierTable, GeneralFormalCircuit.empty, circuit_norm]
    simp [he] at hi
  · exact False.elim (hn (binaryConsumer_mult hc hi))
  · have he : table.interactionsWith BinaryTableChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [hc]
      simp [BinaryExtension.shiftTableConsumerComponent,
        BinaryExtension.shiftTableConsumerCircuit,
        BinaryExtension.tableConsumerCircuit, circuit_norm,
        BinaryTableChannel, BinaryExtensionTableChannel,
        ZiskFv.Channels.OperationBus.OpBusChannel]
    simp [he] at hi
  · exact hc
  · have he : table.interactionsWith BinaryTableChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [hc]
      simp [BinaryExtensionTableSlice.sourceComponent,
        BinaryExtensionTableSlice.sourceCircuit, circuit_norm,
        BinaryTableChannel, BinaryExtensionTableChannel]
    simp [he] at hi

theorem extension_nonpull_source (w : EnsembleWitness ensemble)
    {table : Table FGL} (ht : table ∈ w.allTables)
    {interaction : Interaction FGL}
    (hi : interaction ∈ table.interactionsWith BinaryExtensionTableChannel.toRaw)
    (hn : interaction.mult ≠ -1) :
    table.component = BinaryExtensionTableSlice.sourceComponent := by
  rcases component_cases (EnsembleWitness.mem_allTables_component_of_mem_allTables ht) with
    hc | hc | hc | hc | hc
  · have he : table.interactionsWith BinaryExtensionTableChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [hc]
      simp [ensemble, Ensemble.verifierTable, GeneralFormalCircuit.empty, circuit_norm]
    simp [he] at hi
  · have he : table.interactionsWith BinaryExtensionTableChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [hc]
      simp [Binary.tableConsumerComponent, Binary.tableConsumerCircuit,
        circuit_norm, BinaryTableChannel, BinaryExtensionTableChannel,
        ZiskFv.Channels.OperationBus.OpBusChannel]
    simp [he] at hi
  · exact False.elim (hn (extensionConsumer_mult hc hi))
  · have he : table.interactionsWith BinaryExtensionTableChannel.toRaw = [] := by
      apply Table.interactionsWith_nil_of_channel_not_mem
      rw [hc]
      simp [BinaryTableSlice.sourceComponent, BinaryTableSlice.sourceCircuit,
        circuit_norm, BinaryTableChannel, BinaryExtensionTableChannel]
    simp [he] at hi
  · exact hc

/-- A bus-125 consumer message is an actual source-defined table row. -/
theorem binary_membership_of_balance (w : EnsembleWitness ensemble)
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
      hb BinaryTableChannel.toRaw (by simp [ensemble])
  obtain ⟨provider, hp, hmsg, _, hn⟩ :=
    exists_push_of_pull _ hbalance interaction hi hm
  obtain ⟨table, ht, hp⟩ := EnsembleWitness.mem_interactionsWith.mp hp
  obtain ⟨message, hs, he⟩ := BinaryTableSlice.sourceInteraction_mem_spec
    (binary_nonpull_source w ht hp hn) (hc table ht) hp
  exact ⟨message, hs, hmsg.symm.trans he⟩

/-- A bus-124 consumer message is an actual source-defined table row. -/
theorem extension_membership_of_balance (w : EnsembleWitness ensemble)
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
      hb BinaryExtensionTableChannel.toRaw (by simp [ensemble])
  obtain ⟨provider, hp, hmsg, _, hn⟩ :=
    exists_push_of_pull _ hbalance interaction hi hm
  obtain ⟨table, ht, hp⟩ := EnsembleWitness.mem_interactionsWith.mp hp
  obtain ⟨message, hs, he⟩ := BinaryExtensionTableSlice.sourceInteraction_mem_spec
    (extension_nonpull_source w ht hp hn) (hc table ht) hp
  exact ⟨message, hs, hmsg.symm.trans he⟩

/-- All eight Binary routes obtain membership through the finished channel.
No input-row membership or provider-soundness premise is added. -/
theorem binary_all_eight (w : EnsembleWitness ensemble)
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

theorem extension_all_eight (w : EnsembleWitness ensemble)
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

def binaryMessageRow (row : Binary.BinaryRow FGL) : Fin 8 → BinaryTableMessage FGL
  | ⟨0, _⟩ => Binary.lookupMessage0Row row
  | ⟨1, _⟩ => Binary.lookupMessage1Row row
  | ⟨2, _⟩ => Binary.lookupMessage2Row row
  | ⟨3, _⟩ => Binary.lookupMessage3Row row
  | ⟨4, _⟩ => Binary.lookupMessage4Row row
  | ⟨5, _⟩ => Binary.lookupMessage5Row row
  | ⟨6, _⟩ => Binary.lookupMessage6Row row
  | ⟨7, _⟩ => Binary.lookupMessage7Row row


/-- Evaluation preserves every slot of every actual Binary byte message,
    including all three flag encodings and the first/last-byte position. -/
theorem eval_binaryMessage (env : Environment FGL) (row : Var Binary.BinaryRow FGL)
    (index : Fin 8) :
    eval env (binaryMessage row index) = binaryMessageRow (eval env row) index := by
  fin_cases index <;>
    simp [binaryMessage, binaryMessageRow,
      Binary.lookupMessage0, Binary.lookupMessage1, Binary.lookupMessage2,
      Binary.lookupMessage3, Binary.lookupMessage4, Binary.lookupMessage5,
      Binary.lookupMessage6, Binary.lookupMessage7,
      Binary.lookupMessage0Row, Binary.lookupMessage1Row, Binary.lookupMessage2Row,
      Binary.lookupMessage3Row, Binary.lookupMessage4Row, Binary.lookupMessage5Row,
      Binary.lookupMessage6Row, Binary.lookupMessage7Row,
      Binary.lookupFlags012, Binary.lookupFlags3456, Binary.lookupFlags7,
      Binary.lookupFlags012Row, Binary.lookupFlags3456Row, Binary.lookupFlags7Row,
      ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
      ProvableStruct.components, ProvableStruct.toComponents, ProvableStruct.eval.go,
      sub_eq_add_neg] <;>
    unfold Eval.eval <;>
    simp [CircuitType.instVerifierEvalExpression, CircuitType.verifierEval,
      CircuitType.evalVerifier, ProvableType.toCircuitType, ProvableType.eval,
      ProvableStruct.instProvableTypeType, instProvableTypeField,
      toElements, fromElements, Expression.eval, sub_eq_add_neg]

/-- Integration contract: the same eight memberships previously obtained by
    a detached static-lookup consumer now follow from the actual finished
    bus-125 composition. Existing semantic table proofs consume this bundle. -/
theorem binary_spec_facts_of_balance (w : EnsembleWitness ensemble)
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

def extensionMessageRow (row : BinaryExtension.BinaryExtensionRow FGL) :
    Fin 8 → BinaryExtensionTableMessage FGL
  | ⟨0, _⟩ => ⟨row.flags.op, 0, row.aCols.free_in_a_0, row.flags.free_in_b,
      row.cColsLo.free_in_c_0, row.cColsLo.free_in_c_1, row.flags.op_is_shift⟩
  | ⟨1, _⟩ => ⟨row.flags.op, 1, row.aCols.free_in_a_1, row.flags.free_in_b,
      row.cColsLo.free_in_c_2, row.cColsLo.free_in_c_3, row.flags.op_is_shift⟩
  | ⟨2, _⟩ => ⟨row.flags.op, 2, row.aCols.free_in_a_2, row.flags.free_in_b,
      row.cColsLo.free_in_c_4, row.cColsLo.free_in_c_5, row.flags.op_is_shift⟩
  | ⟨3, _⟩ => ⟨row.flags.op, 3, row.aCols.free_in_a_3, row.flags.free_in_b,
      row.cColsLo.free_in_c_6, row.cColsLo.free_in_c_7, row.flags.op_is_shift⟩
  | ⟨4, _⟩ => ⟨row.flags.op, 4, row.aCols.free_in_a_4, row.flags.free_in_b,
      row.cColsHi.free_in_c_8, row.cColsHi.free_in_c_9, row.flags.op_is_shift⟩
  | ⟨5, _⟩ => ⟨row.flags.op, 5, row.aCols.free_in_a_5, row.flags.free_in_b,
      row.cColsHi.free_in_c_10, row.cColsHi.free_in_c_11, row.flags.op_is_shift⟩
  | ⟨6, _⟩ => ⟨row.flags.op, 6, row.aCols.free_in_a_6, row.flags.free_in_b,
      row.cColsHi.free_in_c_12, row.cColsHi.free_in_c_13, row.flags.op_is_shift⟩
  | ⟨7, _⟩ => ⟨row.flags.op, 7, row.aCols.free_in_a_7, row.flags.free_in_b,
      row.cColsHi.free_in_c_14, row.cColsHi.free_in_c_15, row.flags.op_is_shift⟩

theorem eval_extensionMessage (env : Environment FGL)
    (row : Var BinaryExtension.BinaryExtensionRow FGL) (index : Fin 8) :
    eval env (BinaryExtension.byteMessage row index) =
      extensionMessageRow (eval env row) index := by
  fin_cases index <;>
    simp [BinaryExtension.byteMessage, extensionMessageRow,
      ProvableStruct.eval_eq_eval, ProvableStruct.eval, ProvableStruct.fromComponents,
      ProvableStruct.components, ProvableStruct.toComponents, ProvableStruct.eval.go] <;>
    unfold Eval.eval <;>
    simp [CircuitType.instVerifierEvalExpression, CircuitType.verifierEval,
      CircuitType.evalVerifier, ProvableType.toCircuitType, ProvableType.eval,
      ProvableStruct.instProvableTypeType, instProvableTypeField,
      toElements, fromElements, Expression.eval]

theorem extension_spec_facts_of_balance (w : EnsembleWitness ensemble)
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

/-- Assemble the actual consumer tables with the canonical full-domain
    projections of one physical packed witness. The hypotheses are only table
    identity/data coherence, never table membership or semantic guarantees. -/
def withPackedProviders
    (raw : PackedVirtualTableSources.Witness FGL) (data : ProverData FGL)
    (binary extension : Table FGL)
    (h_binary : binary.component = Binary.tableConsumerComponent)
    (h_extension : extension.component = BinaryExtension.shiftTableConsumerComponent)
    (h_binary_data : binary.data = data) (h_extension_data : extension.data = data) :
    EnsembleWitness ensemble where
  tables := [binary, extension,
    PackedVirtualTableSources.binaryProviderTable raw data,
    PackedVirtualTableSources.extensionProviderTable raw data]
  data := data
  publicInput := ()
  same_length := rfl
  same_circuits := by
    intro index hi
    change index < 4 at hi
    interval_cases index
    · exact h_binary.symm
    · exact h_extension.symm
    · rfl
    · rfl
  same_data := by
    intro table ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact h_binary_data
    · exact h_extension_data
    · rfl
    · rfl

/-- The bus-125 bundle through the actual packed raw witness projection.
    All source multiplicities come from the intrinsic production map. -/
theorem binary_spec_facts_from_packed
    (raw : PackedVirtualTableSources.Witness FGL) (data : ProverData FGL)
    (binary extension : Table FGL)
    (h_binary : binary.component = Binary.tableConsumerComponent)
    (h_extension : extension.component = BinaryExtension.shiftTableConsumerComponent)
    (h_binary_data : binary.data = data) (h_extension_data : extension.data = data)
    (hc : (withPackedProviders raw data binary extension h_binary h_extension
      h_binary_data h_extension_data).Constraints)
    (hb : (withPackedProviders raw data binary extension h_binary h_extension
      h_binary_data h_extension_data).BalancedChannels)
    {row : Array FGL} (hr : row ∈ binary.table) :
    Binary.StaticBinaryTableSpecFacts
      (Binary.tableConsumerComponent.rowInput (binary.environment row)) := by
  exact binary_spec_facts_of_balance _ hc hb
    (by simp [withPackedProviders, EnsembleWitness.allTables]) h_binary hr

theorem extension_spec_facts_from_packed
    (raw : PackedVirtualTableSources.Witness FGL) (data : ProverData FGL)
    (binary extension : Table FGL)
    (h_binary : binary.component = Binary.tableConsumerComponent)
    (h_extension : extension.component = BinaryExtension.shiftTableConsumerComponent)
    (h_binary_data : binary.data = data) (h_extension_data : extension.data = data)
    (hc : (withPackedProviders raw data binary extension h_binary h_extension
      h_binary_data h_extension_data).Constraints)
    (hb : (withPackedProviders raw data binary extension h_binary h_extension
      h_binary_data h_extension_data).BalancedChannels)
    {row : Array FGL} (hr : row ∈ extension.table) :
    BinaryExtension.StaticBinaryExtensionTableSpecFacts
      (BinaryExtension.shiftTableConsumerComponent.rowInput (extension.environment row)) := by
  exact extension_spec_facts_of_balance _ hc hb
    (by simp [withPackedProviders, EnsembleWitness.allTables]) h_extension hr

end ZiskFv.AirsClean.BinaryTableBalance
