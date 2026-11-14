import ZiskFv.AirsClean.BinaryTableBalance

/-!
# Constructible Binary-family provider/consumer balance

The request indices are concrete source-row indices. The tuple weld is checked
against all eight actual consumer messages, not against a fabricated request
stream. These constructor lemmas add no accepted-trace or root premise; closed
witnesses supply their already explicit honest source indices.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks Air.Flat
open ZiskFv.Channels.BinaryTable
open ZiskFv.Channels.BinaryExtensionTable
open ZiskFv.AirsClean.BinaryTableBalance
open ZiskFv.AirsClean.PackedVirtualTableSources
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- Retain the actual operation-bus emission while adding table requests. -/
theorem binary_consumer_interactionsWith_opBus :
    Binary.tableConsumerComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed
        (Binary.opBusMessageExpr Binary.tableConsumerComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  simp [Binary.tableConsumerComponent, Binary.tableConsumerCircuit,
    Component.exposedChannels, expose]

theorem extension_consumer_interactionsWith_opBus :
    BinaryExtension.shiftTableConsumerComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed
        (BinaryExtension.opBusMessageExpr
          BinaryExtension.shiftTableConsumerComponent.rowInputVar)).toRaw)] := by
  rw [BinaryExtension.shiftTableConsumerComponent_interactionsWith]
  change BinaryExtension.tableConsumerComponent.operations.interactionsWith
    OpBusChannel.toRaw =
      [((OpBusChannel.pushed (BinaryExtension.opBusMessageExpr
        BinaryExtension.tableConsumerComponent.rowInputVar)).toRaw)]
  apply Component.interactionsWith_of_exposedChannels
  simp [BinaryExtension.tableConsumerComponent, BinaryExtension.tableConsumerCircuit,
    Component.exposedChannels, expose]

/-- Preserve the existing honest source-index row builders while moving their
table placement to the real emitting circuit. This is a constructor adapter,
not an accepted-trace or semantic caller premise. -/
theorem binary_consumer_prover_of_static
    (row : Binary.BinaryRow FGL) (data : ProverData FGL) (hint : ProverHint FGL)
    (h : Binary.staticLookupCircuit.ProverAssumptions row data hint) :
    Binary.tableConsumerCircuit.ProverAssumptions row data hint := by
  obtain ⟨mode32, resultIsA, useFirstByte, cIsSigned, carry7,
    i0, i1, i2, i3, i4, i5, i6, i7,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrow⟩ := h
  exact ⟨mode32, resultIsA, useFirstByte, cIsSigned, carry7,
    _, _, _, _, _, _, _, _, _, _, _, hrow⟩

theorem extension_consumer_prover_of_static
    (row : BinaryExtension.BinaryExtensionRow FGL)
    (data : ProverData FGL) (hint : ProverHint FGL)
    (h : BinaryExtension.shiftStaticLookupCircuit.ProverAssumptions row data hint) :
    BinaryExtension.shiftTableConsumerCircuit.ProverAssumptions row data hint := by
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, b0, b1,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    h_range, hrow⟩ := h
  rw [hrow]
  simpa only [BinaryExtension.shiftTableConsumerCircuit,
    BinaryExtension.binaryExtensionStaticRowOf] using h_range

theorem binary_consumer_interactions_fromInput
    (row : Binary.BinaryRow FGL) (data : ProverData FGL) :
    Binary.tableConsumerComponent.operations.interactionValuesWith BinaryTableChannel.toRaw
        (Environment.fromInput row data) =
      List.ofFn (fun index : Fin 8 =>
        BinaryTableChannel.pushedIfValue (-1) (binaryMessageRow row index)) := by
  have h_operations :
      Binary.tableConsumerComponent.operations.interactionsWith BinaryTableChannel.toRaw =
        List.ofFn (fun index : Fin 8 => (BinaryTableChannel.emitted (-1)
          (binaryMessage Binary.tableConsumerComponent.rowInputVar index)).toRaw) := by
    rw [Binary.tableConsumerComponent_interactionsWith_binaryTableChannel]
    rfl
  have h_input : eval (Environment.fromInput row data)
      Binary.tableConsumerComponent.rowInputVar = row :=
    ProvableType.eval_fromInput_varFromOffset_zero row data
  rw [Operations.interactionValuesWith_eq_map, h_operations, List.map_ofFn]
  apply congrArg (fun f : Fin 8 → Interaction FGL => List.ofFn f)
  funext index
  change (BinaryTableChannel.pushedIf (-1)
      (binaryMessage Binary.tableConsumerComponent.rowInputVar index)).toRaw.eval
      (Environment.fromInput row data) = _
  rw [Channel.eval_pushedIf, eval_binaryMessage, h_input]
  with_unfolding_all rfl

theorem extension_consumer_interactions_fromInput
    (row : BinaryExtension.BinaryExtensionRow FGL) (data : ProverData FGL) :
    BinaryExtension.shiftTableConsumerComponent.operations.interactionValuesWith
        BinaryExtensionTableChannel.toRaw (Environment.fromInput row data) =
      List.ofFn (fun index : Fin 8 =>
        BinaryExtensionTableChannel.pushedIfValue (-1) (extensionMessageRow row index)) := by
  have h_operations :
      BinaryExtension.shiftTableConsumerComponent.operations.interactionsWith
          BinaryExtensionTableChannel.toRaw =
        List.ofFn (fun index : Fin 8 => (BinaryExtensionTableChannel.emitted (-1)
          (BinaryExtension.byteMessage
            BinaryExtension.tableConsumerComponent.rowInputVar index)).toRaw) := by
    rw [BinaryExtension.shiftTableConsumerComponent_interactionsWith,
      BinaryExtension.tableConsumer_interactionsWith_binaryExtensionTable]
    rfl
  have h_input : eval (Environment.fromInput row data)
      BinaryExtension.tableConsumerComponent.rowInputVar = row :=
    ProvableType.eval_fromInput_varFromOffset_zero row data
  rw [Operations.interactionValuesWith_eq_map, h_operations, List.map_ofFn]
  apply congrArg (fun f : Fin 8 → Interaction FGL => List.ofFn f)
  funext index
  change (BinaryExtensionTableChannel.pushedIf (-1)
      (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar index)).toRaw.eval
      (Environment.fromInput row data) = _
  rw [Channel.eval_pushedIf, eval_extensionMessage, h_input]
  with_unfolding_all rfl

/-- The actual eight Binary negative messages balance the counted source
provider. Duplicate indices are counted, and both sources share one raw. -/
theorem binary_actual_row_requests_balanced
    (base : Witness FGL) (data : ProverData FGL) (row : Binary.BinaryRow FGL)
    (requests : Fin 8 → Fin BinaryTable.tableSize)
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize))
    (h_requests : ∀ index, BinaryTable.rowOfIndex (requests index).val =
      binaryMessageRow row index) :
    BalancedInteractions
      (binaryInteractions (physicalOfRequests base (List.ofFn requests) extensionRequests) ++
        Binary.tableConsumerComponent.operations.interactionValuesWith BinaryTableChannel.toRaw
          (Environment.fromInput row data)) := by
  rw [binary_consumer_interactions_fromInput]
  have h_consumer : consumedSourceRequests BinaryTableChannel
      (fun index : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex index.val)
      (List.ofFn requests) =
        List.ofFn (fun index : Fin 8 =>
          BinaryTableChannel.pushedIfValue (-1) (binaryMessageRow row index)) := by
    simp only [consumedSourceRequests, List.map_ofFn]
    apply congrArg (fun f : Fin 8 → Interaction FGL => List.ofFn f)
    funext index
    rw [Function.comp_apply, h_requests]
  rw [← h_consumer]
  exact binaryEightRequests_balanced base requests extensionRequests

/-- The shift-range circuit's actual eight negative messages, not a sidecar
consumer, balance its source provider. Local b0 range constraints remain
separate and are not weakened by this channel-balance construction. -/
theorem extension_actual_row_requests_balanced
    (base : Witness FGL) (data : ProverData FGL)
    (row : BinaryExtension.BinaryExtensionRow FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (requests : Fin 8 → Fin BinaryExtensionTable.tableSize)
    (h_requests : ∀ index, BinaryExtensionTable.rowOfIndex (requests index).val =
      extensionMessageRow row index) :
    BalancedInteractions
      (extensionInteractions (physicalOfRequests base binaryRequests (List.ofFn requests)) ++
        BinaryExtension.shiftTableConsumerComponent.operations.interactionValuesWith
          BinaryExtensionTableChannel.toRaw (Environment.fromInput row data)) := by
  rw [extension_consumer_interactions_fromInput]
  have h_consumer : consumedSourceRequests BinaryExtensionTableChannel
      (fun index : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex index.val)
      (List.ofFn requests) =
        List.ofFn (fun index : Fin 8 =>
          BinaryExtensionTableChannel.pushedIfValue (-1) (extensionMessageRow row index)) := by
    simp only [consumedSourceRequests, List.map_ofFn]
    apply congrArg (fun f : Fin 8 → Interaction FGL => List.ofFn f)
    funext index
    rw [Function.comp_apply, h_requests]
  rw [← h_consumer]
  exact extensionEightRequests_balanced base binaryRequests requests

/-- A real source provider with no Binary requests still contains its entire
fixed domain, with zero raw multiplicities. Its interaction count is bounded
by the actual source domain, not by a caller promise. -/
theorem binary_no_requests_balanced
    (base : Witness FGL)
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize)) :
    BalancedInteractions (binaryInteractions (physicalOfRequests base [] extensionRequests)) := by
  rw [binaryInteractions_physicalOfRequests]
  have h_count : BinaryTable.tableSize + ([] : List (Fin BinaryTable.tableSize)).length <
      ringChar FGL := by
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    norm_num [BinaryTable.tableSize]
  simpa only [consumedSourceRequests, List.map_nil, List.append_nil] using
    (countedSourceRequests_balanced BinaryTableChannel
      (fun index : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex index.val) [] h_count)

theorem extension_no_requests_balanced
    (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize)) :
    BalancedInteractions
      (extensionInteractions (physicalOfRequests base binaryRequests [])) := by
  rw [extensionInteractions_physicalOfRequests]
  have h_count : BinaryExtensionTable.tableSize +
      ([] : List (Fin BinaryExtensionTable.tableSize)).length < ringChar FGL := by
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    norm_num [BinaryExtensionTable.tableSize,
      BinaryExtensionTable.shiftBlockSize, BinaryExtensionTable.sextBlockSize]
  simpa only [consumedSourceRequests, List.map_nil, List.append_nil] using
    (countedSourceRequests_balanced BinaryExtensionTableChannel
      (fun index : Fin BinaryExtensionTable.tableSize =>
        BinaryExtensionTable.rowOfIndex index.val) [] h_count)

/-- The zero-request physical witness is shared by both canonical providers
in the existing examples whose Binary-family consumer tables are empty. -/
def noRequestPackedSources : Witness FGL :=
  physicalOfRequests (fun _ => 0) [] []

theorem binary_source_transitions {table : Table FGL}
    (h_component : table.component = BinaryTableSlice.sourceComponent) :
    table.TransitionConstraints := by
  intro index
  rw [h_component]
  trivial

theorem extension_source_transitions {table : Table FGL}
    (h_component : table.component = BinaryExtensionTableSlice.sourceComponent) :
    table.TransitionConstraints := by
  intro index
  rw [h_component]
  trivial

theorem binary_source_cyclicSuccessorTransitions {table : Table FGL}
    (h_component : table.component = BinaryTableSlice.sourceComponent) :
    table.CyclicSuccessorTransitionConstraints := by
  intro index
  rw [h_component]
  trivial

theorem extension_source_cyclicSuccessorTransitions {table : Table FGL}
    (h_component : table.component = BinaryExtensionTableSlice.sourceComponent) :
    table.CyclicSuccessorTransitionConstraints := by
  intro index
  rw [h_component]
  trivial

/-- Materialize actual bus-125 consumers, rather than the detached static-lookup
component. Honest source-index evidence is adapted by
`binary_consumer_prover_of_static`, not added to acceptance. -/
def binaryConsumerRowsTable (data : ProverData FGL)
    (rows : List (Binary.BinaryRow FGL)) : Table FGL where
  component := Binary.tableConsumerComponent
  rawRows := rows.map (fun row => (toElements row).toArray)
  data := data
  raw_uniform_width := by
    intro array h_array
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp h_array
    have h_width : Binary.tableConsumerComponent.rawWidth = size Binary.BinaryRow := by
      change Binary.tableConsumerCircuit.size = size Binary.BinaryRow
      rw [GeneralFormalCircuit.size_eq]
      rfl
    rw [h_width]
    simp
  fixed_domain := by
    intro columns h_columns
    simp [Binary.tableConsumerComponent] at h_columns

/-- Actual bus-124 consumers retain the existing shift-range lookup. -/
def extensionConsumerRowsTable (data : ProverData FGL)
    (rows : List (BinaryExtension.BinaryExtensionRow FGL)) : Table FGL where
  component := BinaryExtension.shiftTableConsumerComponent
  rawRows := rows.map (fun row => (toElements row).toArray)
  data := data
  raw_uniform_width := by
    intro array h_array
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp h_array
    have h_width :
        BinaryExtension.shiftTableConsumerComponent.rawWidth =
          size BinaryExtension.BinaryExtensionRow := by
      change BinaryExtension.shiftTableConsumerCircuit.size =
        size BinaryExtension.BinaryExtensionRow
      rw [GeneralFormalCircuit.size_eq]
      rfl
    rw [h_width]
    simp
  fixed_domain := by
    intro columns h_columns
    simp [BinaryExtension.shiftTableConsumerComponent] at h_columns

end ZiskFv.AirsClean.FullEnsemble
