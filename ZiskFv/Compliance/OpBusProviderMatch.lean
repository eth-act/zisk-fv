import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.AirsClean.FullEnsemble.ArithBalance

/-!
# Layer-A op-bus provider-match existence lemmas

The `exists_*_provider_row_matches_*` lemmas: for an active Main op row, they
build the Main op-bus interaction, prove its membership and `mult = -1`, and
discharge the op-bus provider match by delegating to the axiom-free Layer-B
permutation theorems in `AirsClean/FullEnsemble/{Balance,ArithBalance}.lean`.
They are the only consumers of `trace.channels_balanced` in the construction
spine; the honest sound construction built on top lives in
`ZiskFv/Compliance/ConstructionSub.lean`.
-/

namespace ZiskFv.Compliance

open ZiskFv.AirsClean.FullEnsemble

theorem exists_staticBinary_provider_row_matches_logic
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_AND
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_OR
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_staticBinary_provider_row_matches_sub
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_SUB) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_sub_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_add_provider_row_matches
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_ADD) :
    ZiskFv.Airs.Main.add_subset_holds
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      i.val
    ∧
      ((∃ providerTable ∈ trace.witness.allTables,
        ∃ providerRow ∈ providerTable.table,
          providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
            ∧ providerTable.Spec
            ∧ ZiskFv.Airs.OperationBus.matches_entry
              (ZiskFv.Airs.OperationBus.opBus_row_Main
                (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
                i.val)
              (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                (ZiskFv.AirsClean.Binary.opBusMessage
                  (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                    (providerTable.environment providerRow))) 1))
      ∨
      (∃ providerTable ∈ trace.witness.allTables,
        ∃ providerRow ∈ providerTable.table,
          providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
            ∧ providerTable.Spec
            ∧ ZiskFv.Airs.OperationBus.matches_entry
              (ZiskFv.Airs.OperationBus.opBus_row_Main
                (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
                i.val)
              (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                (ZiskFv.AirsClean.BinaryAdd.opBusMessage
                  (ZiskFv.AirsClean.BinaryAdd.component.rowInput
                    (providerTable.environment providerRow))) 1))) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  have h_main_component_spec :
      trace.mainTable.component.Spec
        (trace.mainTable.environment (trace.mainTable.table.get mainIdx)) := by
    simpa [mainRow] using
      trace.spec_holds trace.mainTable trace.mainTable_mem mainRow h_mainRow_mem
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec
        (ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val) := by
    simpa [mainIdx] using
      ZiskFv.AirsClean.FullEnsemble.mainSpec_rowAt_mainOfTable_of_component_spec
        trace.program trace.mainTable mainIdx trace.mainTable_component
        h_main_component_spec
  have h_main_subset :
      ZiskFv.Airs.Main.add_subset_holds
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      i.val h_main_spec
  exact ⟨h_main_subset,
    exists_add_provider_row_matches_legacy_main_of_add_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op⟩

theorem exists_staticBinary_provider_row_matches_compare
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_LT
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_LTU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_compare_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_staticBinary_provider_row_matches_w
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_ADD_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SUB_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_w_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_binaryExtension_provider_row_matches_shift
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SLL
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SRL
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SRA
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SLL_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SRL_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_SRA_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component =
            ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryExtension.opBusMessage
                (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_binaryExtension_provider_row_matches_legacy_main_of_shift_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith MULW operation
    (`OP_MUL_W = 182`).  Mirrors
    `exists_staticBinary_provider_row_matches_sub`: it builds the
    Main op-bus interaction, proves membership + `mult = -1`, and delegates to
    the keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction`.

    Unlike the static-Binary wrappers, the provider here is the lookup-aware
    `arithMulProviderComponent` (= `ArithMul.componentWithArithTable`), so
    `providerTable.Spec` is `FullSpec (rowInput …)` and the match is against the
    ArithMul primary op-bus message. -/
theorem exists_arithMul_provider_row_matches_primary_of_mulw
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_MUL_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith MULHU operation
    (`OP_MULUH = 177`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_mulw`, but
    delegates to the MULHU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction`.

    The returned match is still against the muxed `primaryOpBusMessage`; the
    MULHU-mode bridge in `ArithMul/Bridge.lean` later reduces it to the
    secondary d-lane `opBus_row_ArithMulSecondary`. -/
theorem exists_arithMul_provider_row_matches_secondary_of_mulhu
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_MULUH) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith DIVU operation
    (`OP_DIVU = 184`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_mulw`, but
    delegates to the DIVU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The DIVU-mode bridge in
    `ArithMul/Bridge.lean` later reduces it to the div quotient-lane
    `opBus_row_ArithDiv`. -/
theorem exists_arithMul_provider_row_matches_primary_of_divu
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_DIVU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith DIVUW operation
    (`OP_DIVU_W = 188`, W-mode `m32 = 1`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_divu`, but
    delegates to the DIVUW keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_divuw_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The DIVU-mode op-bus bridge later
    reduces it to the div quotient-lane `opBus_row_ArithDiv`. -/
theorem exists_arithMul_provider_row_matches_primary_of_divuw
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_DIVU_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_divuw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith REMU operation
    (`OP_REMU = 185`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_divu`, but
    delegates to the REMU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_remu_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The REMU-mode bridge in
    `ConstructionRemu.lean` later reduces it (at `div = 1`, `main_div = 0`,
    `main_mul = 0`) to the div remainder-lane `opBus_row_ArithDivSecondary`. -/
theorem exists_arithMul_provider_row_matches_primary_of_remu
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_REMU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_remu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith REMUW operation
    (`OP_REMU_W = 189`, W-mode `m32 = 1`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_remu`, but
    delegates to the REMUW keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_remuw_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The REMU-mode secondary bridge in
    `ConstructionRemu.lean` later reduces it (at `div = 1`, `main_div = 0`,
    `main_mul = 0`) to the div remainder-lane `opBus_row_ArithDivSecondary`; the
    `m32` flag plays no role in the mux. -/
theorem exists_arithMul_provider_row_matches_primary_of_remuw
    (trace : AcceptedZiskTrace)
    (i : Fin trace.numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_REMU_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        trace.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.numInstructions) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.numInstructions trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.numInstructions trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.numInstructions) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_remuw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

end ZiskFv.Compliance
