import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-! ## Full-ensemble operation-bus row bridges -/

/-- Spec-carrying full-ensemble operation-bus projection: an active
    unified-Main operation-bus interaction has a balanced same-message
    provider counterpart, and the Binary-family provider branches are
    resolved to concrete table rows carrying `witness.Spec`.
    The ArithMul provider branch is also resolved to a concrete row. -/
theorem exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧ mainInteraction =
          ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw).eval
            (mainTable.environment mainRow)
        ∧ ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = arithMulProviderComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                            arithMulProviderComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        shiftStaticLookupComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                            shiftStaticLookupComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Binary.staticLookupComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.Binary.opBusMessageExpr
                            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))) := by
  have h_main_witness :
      mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_op_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_provider_op_component_of_active_main_interaction
      witness h_constraints h_balanced h_main_witness h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_arithMul_row_eval_of_interaction_mem
        h_arithMul h_providerInteraction
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_arithMul, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinaryExtension_row_eval_of_interaction_mem
        h_binExt h_providerInteraction
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binExt, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinary_row_eval_of_interaction_mem
        h_binary h_providerInteraction
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binary, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binaryAdd_row_eval_of_interaction_mem
        h_binaryAdd h_providerInteraction
    right
    right
    right
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binaryAdd, h_providerEval⟩

/-- Legacy-entry view of the full-ensemble operation-bus bridge.

    Clean balance proves equality of raw operation-bus message arrays.  This
    adapter keeps the full-ensemble provider row/spec information while
    translating each provider branch into the `OperationBus.matches_entry`
    shape consumed by the existing opcode proofs. -/
theorem exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧ mainInteraction =
          ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw).eval
            (mainTable.environment mainRow)
        ∧ ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = arithMulProviderComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                              arithMulProviderComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        shiftStaticLookupComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                              shiftStaticLookupComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Binary.staticLookupComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Binary.opBusMessageExpr
                              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))) := by
  obtain ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
      h_providerTable, h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_arithMul
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binExt
    right
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binary
    right
    right
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binaryAdd
    right
    right
    right
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg

/-- Legacy-Main view of the full-ensemble operation-bus bridge.

    This specializes the selected unified Clean Main row back to the existing
    `Valid_Main` row used by opcode proofs.  It deliberately preserves all
    full-ensemble provider alternatives: later opcode-specific adapters may
    rule out branches only from provider-local facts, not by caller promise. -/
theorem exists_op_provider_row_matches_legacy_main_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_main_row :
      ∀ mainRow ∈ mainTable.table,
        eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.core =
          ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ providerTable ∈ witness.allTables,
          providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
            ∧
            ((∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component = arithMulProviderComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                          arithMulProviderComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component =
                    shiftStaticLookupComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                          shiftStaticLookupComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component =
                    ZiskFv.AirsClean.Binary.staticLookupComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Binary.opBusMessageExpr
                          ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                          ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))) := by
  obtain ⟨mainRow, h_mainRow, _h_mainSpec, _h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
      h_providerTable, h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row mainRow h_mainRow]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  refine ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
    h_nonzero, providerTable, h_providerTable, h_providerInteraction, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_arithMul
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binExt
    right
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binary
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binaryAdd
    right
    right
    right
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩

/-- XOR specialization of the full-ensemble operation-bus provider bridge.

    For an active legacy Main row whose opcode is `OP_XOR`, balanced operation-bus
    coverage cannot use ArithMul, BinaryExtension, or BinaryAdd.  The remaining
    branch is the lookup-aware Binary provider row, with the provider table's
    full `Spec` retained for wrapper construction. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_main_row :
      ∀ mainRow ∈ mainTable.table,
        eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.core =
          ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  obtain ⟨providerInteraction, _h_provider_witness, _h_msg, _h_nonpull,
      _h_nonzero, providerTable, h_providerTable, _h_providerInteraction,
      h_providerBranches⟩ :=
    exists_op_provider_row_matches_legacy_main_spec_of_active_main_table_interaction
      m r_main witness h_constraints h_balanced h_specs h_mainTable
      h_mainComponent h_main_row h_main_active h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component, h_match⟩ :=
      h_arithMul
    exact False.elim
      (arithMul_provider_branch_ne_xor h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component, h_match⟩ :=
      h_binExt
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_xor h_component h_providerSpec
        h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component, h_match⟩ :=
      h_binary
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component, h_match⟩ :=
      h_binaryAdd
    exact False.elim (binaryAdd_provider_branch_ne_xor h_match h_main_op)

/-- Row-indexed XOR specialization of the full-ensemble operation-bus provider
    bridge.

Unlike `exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_table_interaction`,
this adapter rewrites only the concrete Main table row that emitted the selected
interaction.  It is the construction-facing form: callers identify row `i` in
the selected Main table, and balance supplies the Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_xor h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_xor h_component h_providerSpec
        h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_xor h_match h_main_op)

/-- Row-indexed logical-Binary specialization of the full-ensemble operation-bus
    provider bridge.

For a concrete active Main row whose opcode is `AND`, `OR`, or `XOR`, balance
cannot use ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryLogic
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryLogic
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryLogic h_match h_main_op)

/-- Row-indexed comparison-Binary specialization of the full-ensemble
    operation-bus provider bridge.

For a concrete active Main row whose opcode is `LT` or `LTU`, balance cannot
use ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_compare_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryCompare
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryCompare
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryCompare h_match h_main_op)

/-- Row-indexed `SUB` Binary specialization of the full-ensemble operation-bus
    provider bridge.

For a concrete active Main row whose opcode is `SUB`, balance cannot use
ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_sub_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinarySub
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinarySub
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinarySub h_match h_main_op)

/-- Row-indexed ADD provider specialization of the full-ensemble operation-bus
    provider bridge.

For a concrete active Main row whose opcode is `ADD`, balance cannot use
ArithMul or BinaryExtension. The remaining honest providers are lookup-aware
Binary and BinaryAdd, so the result preserves that disjunction for callers. -/
theorem exists_add_provider_row_matches_legacy_main_of_add_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_ADD) :
    (∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1))
    ∨
    (∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryAdd.opBusMessage
                (ZiskFv.AirsClean.BinaryAdd.component.rowInput
                  (providerTable.environment providerRow))) 1)) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryAdd
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryAdd
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact Or.inl ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.BinaryAdd.opBusMessage
              (ZiskFv.AirsClean.BinaryAdd.component.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.BinaryAdd.component_eval_opBusMessageExpr]
        using h_match
    exact Or.inr ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩

/-- Row-indexed W-mode ADD/SUB Binary specialization of the full-ensemble
    operation-bus provider bridge.

For a concrete active Main row whose opcode is `ADDW` or `SUBW`, balance cannot
use ArithMul, BinaryExtension, or BinaryAdd.  The remaining branch is the
lookup-aware Binary provider row. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_w_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryW
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryW
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryW h_match h_main_op)

/-- Row-indexed BinaryExtension shift specialization of the full-ensemble
    operation-bus provider bridge.

For a concrete active Main row whose opcode is one of the BinaryExtension shift
opcodes, balance cannot use ArithMul, static Binary, or BinaryAdd.  The
remaining branch is the lookup-aware BinaryExtension provider row. -/
theorem exists_binaryExtension_provider_row_matches_legacy_main_of_shift_active_main_row_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainRow : Array FGL}
    (_h_mainRow : mainRow ∈ mainTable.table)
    (h_main_row :
      eval (mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_mainInteraction_eval :
      mainInteraction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = shiftStaticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryExtension.opBusMessage
                (shiftStaticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerBranches⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  rcases h_providerBranches with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryExtensionShift
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                shiftStaticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.BinaryExtension.opBusMessage
              (shiftStaticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
  · obtain ⟨providerRow, _h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (staticBinary_provider_branch_ne_staticBinaryExtensionShift
        h_component h_providerSpec h_match h_main_op)
  · obtain ⟨providerRow, _h_providerRow, _h_providerSpec, _h_component,
      h_providerEval⟩ := h_binaryAdd
    have h_match :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1) := by
      rw [← h_main_entry]
      apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
      rw [← h_providerEval, ← h_mainInteraction_eval]
      exact h_msg
    exact False.elim
      (binaryAdd_provider_branch_ne_staticBinaryExtensionShift h_match h_main_op)

end ZiskFv.AirsClean.FullEnsemble
