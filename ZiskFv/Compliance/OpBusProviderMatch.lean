import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.AirsClean.FullEnsemble.ArithBalance

/-!
# Layer-A op-bus request lemmas

The `main_request_<op>_provided` lemmas: for an active Main op row, they prove
Main's op-bus request (the interaction with `mult = -1`) is matched by a provider
push in the witness — building the Main interaction, proving its membership and
`mult = -1`, and discharging the match via the axiom-free Layer-B permutation
theorems in `AirsClean/FullEnsemble/{Balance,ArithBalance}.lean`.
They are the only consumers of `trace.channels_balanced` in the construction
spine; the honest sound construction built on top lives in
`ZiskFv/Compliance/ConstructionSub.lean`.
-/

namespace ZiskFv.Compliance

open ZiskFv.AirsClean.FullEnsemble

theorem main_request_logic_provided_at
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.mainTable.table.length)
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
  let mainIdx : Fin trace.mainTable.table.length := i
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_logic_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                  (providerTable.environment providerRow))) 1) :=
  main_request_logic_provided_at trace
    ⟨i.val, trace.mainTable_index i⟩ h_main_active h_main_op

theorem main_request_sub_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_sub_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_add_provided_at
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.mainTable.table.length)
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
  let mainIdx : Fin trace.mainTable.table.length := i
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
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

theorem main_request_add_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                    (providerTable.environment providerRow))) 1))) :=
  main_request_add_provided_at trace
    ⟨i.val, trace.mainTable_index i⟩ h_main_active h_main_op

theorem main_request_compare_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_compare_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_eq_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_EQ) :
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
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_eq_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_w_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_w_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_shift_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
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
    `main_request_sub_provided`: it builds the
    Main op-bus interaction, proves membership + `mult = -1`, and delegates to
    the keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction`.

    Unlike the static-Binary wrappers, the provider here is the lookup-aware
    `arithMulProviderComponent` (= `ArithMul.componentComplete`), so
    `providerTable.Spec` is `FullSpec (rowInput …)` and the match is against the
    ArithMul primary op-bus message. -/
theorem main_request_mulw_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
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
    `main_request_mulw_provided`, but
    delegates to the MULHU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction`.

    The returned match is still against the muxed `primaryOpBusMessage`; the
    MULHU-mode bridge in `ArithMul/Bridge.lean` later reduces it to the
    secondary d-lane `opBus_row_ArithMulSecondary`. -/
theorem main_request_mulhu_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
    h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the signed high-half Arith MULH
    operation (`OP_MULH = 181`).  The provider's `Spec` is the lookup-aware
    `ArithMul.FullSpec`, obtained from finished operation-bus balance. -/
theorem main_request_mulh_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_MULH) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_secondary_of_mulh_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the signed-times-unsigned high
    Arith MULHSU operation (`OP_MULSUH = 179`). -/
theorem main_request_mulhsu_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_MULSUH) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_secondary_of_mulhsu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith DIVU operation
    (`OP_DIVU = 184`).  Mirrors
    `main_request_mulw_provided`, but
    delegates to the DIVU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The DIVU-mode bridge in
    `ArithMul/Bridge.lean` later reduces it to the div quotient-lane
    `opBus_row_ArithDiv`. -/
theorem main_request_divu_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_DIVU
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val = ZiskFv.Trusted.OP_DIV) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Signed DIV specialization of the shared Div-family provider selection. -/
theorem main_request_div_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_DIV) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) :=
  main_request_divu_provided trace i h_main_active (Or.inr h_main_op)

private theorem arithMul_div_pin_of_op_186
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 186) :
    row.flags.div = 1 := by
  rcases h_table with ⟨i, hi⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hi h_op ⊢
  all_goals
    rcases hi with ⟨hop, _hm32, hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv0, _hoverflow, _hmainMul, _hmainDiv, _hsigned, _hrangeAB, _hrangeCD⟩
    first
    | exact hdiv
    | rw [h_op] at hop
      have hv := congrArg Fin.val hop
      norm_num at hv

private theorem arithMul_remainder_sign_cases_of_constraints
    (env : Environment FGL)
    (h_constraints :
      ZiskFv.AirsClean.ArithMul.componentComplete.operations.ConstraintsHold env) :
    let row := ZiskFv.AirsClean.ArithMul.componentComplete.rowInput env
    (row.flags.nr = 0 ∨ row.flags.nr = 1)
      ∧ (row.flags.nb = 0 ∨ row.flags.nb = 1) := by
  have h_operations :=
    (Air.Flat.Component.constraintsHold_iff
      (component := ZiskFv.AirsClean.ArithMul.componentComplete) env).mp h_constraints
  have h_divBlock :=
    ZiskFv.AirsClean.ArithMul.sharedDivBlockSpec_of_constraints
      ZiskFv.AirsClean.ArithMul.componentComplete.rowOffset env
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar h_operations
  have h_row_eval :
      eval env ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar =
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInput env := by
    simpa using
      (eval_varFromOffset_valueFromOffset
        ZiskFv.AirsClean.ArithMul.componentComplete.Input 0 env)
  rw [h_row_eval] at h_divBlock
  rcases h_divBlock.1 with
    ⟨_, _, _, _, _, _, _, _, _, h_nb_bool, h_nr_bool, _, _⟩
  constructor
  · rcases mul_eq_zero.mp h_nr_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  · rcases mul_eq_zero.mp h_nb_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm

private theorem staticBinary_remainder_provider_of_active
    {length : ℕ}
    {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    (env : Environment FGL)
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    {consumerInteraction : Interaction FGL}
    (h_consumer :
      consumerInteraction ∈ witness.interactionsWith
        ZiskFv.Channels.OperationBus.OpBusChannel.toRaw)
    (h_active : consumerInteraction.mult = -1)
    (h_consumerEval :
      consumerInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags.div *
            (1 -
              ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags.div_by_zero)))
          (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessageExpr
            ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar)).toRaw).eval env)
    (h_row_eval :
      eval env ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar = row)
    (h_op :
      (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage row).op.val = 6
        ∨ (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage row).op.val = 80
        ∨ (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage row).op.val = 81
        ∨ (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage row).op.val = 8) :
    ∃ binaryTable ∈ witness.allTables,
      ∃ binaryRow ∈ binaryTable.table,
        binaryTable.component.Spec (binaryTable.environment binaryRow)
          ∧ binaryTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage row) 1)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (eval (binaryTable.environment binaryRow)
                (ZiskFv.AirsClean.Binary.opBusMessageExpr
                  ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
  have h_eval_msg :
      eval env (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessageExpr
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar) =
        ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage row := by
    rw [ZiskFv.AirsClean.ArithMul.eval_remainderBoundOpBusMessageExpr, h_row_eval]
  have h_eval_op := h_op
  rw [← h_eval_msg] at h_eval_op
  have h_result :=
    ZiskFv.AirsClean.FullEnsemble.exists_staticBinary_provider_of_active_remainder_bound_interaction
      witness h_constraints h_balanced h_specs h_consumer h_active h_consumerEval h_eval_op
  rw [h_eval_msg] at h_result
  exact h_result

set_option maxHeartbeats 1000000 in
/-- The live signed-DIV Arith row's remainder-bound request is served by a
    concrete static Binary row. -/
theorem signedDiv_remainder_bound_provider
    (trace : AcceptedZiskTrace numInstructions)
    {providerTable : Air.Flat.Table FGL}
    (h_providerTable : providerTable ∈ trace.witness.allTables)
    {providerRow : Array FGL} (h_providerRow : providerRow ∈ providerTable.table)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_op :
      (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (providerTable.environment providerRow)).flags.op = 186)
    (h_div_by_zero :
      (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (providerTable.environment providerRow)).flags.div_by_zero = 0) :
    ∃ binaryTable ∈ trace.witness.allTables,
      ∃ binaryRow ∈ binaryTable.table,
        binaryTable.component.Spec (binaryTable.environment binaryRow)
          ∧ binaryTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (eval (binaryTable.environment binaryRow)
                (ZiskFv.AirsClean.Binary.opBusMessageExpr
                  ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1) := by
  let env := providerTable.environment providerRow
  let row := ZiskFv.AirsClean.ArithMul.componentComplete.rowInput env
  have h_full : ZiskFv.AirsClean.ArithMul.FullSpec row := by
    simpa [env, row] using
      ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
        h_component h_providerSpec
  have h_rowConstraints :=
    trace.constraints_hold providerTable h_providerTable providerRow h_providerRow
  rw [h_component] at h_rowConstraints
  have h_row_eval :
      eval env ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar = row := by
    simpa [row] using
      (eval_varFromOffset_valueFromOffset
        ZiskFv.AirsClean.ArithMul.componentComplete.Input 0 env)
  obtain ⟨h_nr, h_nb⟩ :=
    arithMul_remainder_sign_cases_of_constraints env h_rowConstraints
  have h_div : row.flags.div = 1 :=
    arithMul_div_pin_of_op_186 row h_full.2.1 h_op
  let consumerInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags.div *
        (1 - ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags.div_by_zero)))
      (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessageExpr
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar)).toRaw).eval env
  have h_consumerLocal :
      consumerInteraction ∈
        providerTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    exact ZiskFv.AirsClean.FullEnsemble.arithMul_remainderBoundInteraction_mem
      h_component h_providerRow
  have h_consumer :
      consumerInteraction ∈
        trace.witness.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    exact Air.Flat.EnsembleWitness.mem_interactionsWith.mpr
      ⟨providerTable, h_providerTable, h_consumerLocal⟩
  have h_active : consumerInteraction.mult = -1 := by
    dsimp [consumerInteraction]
    apply ZiskFv.AirsClean.ArithMul.eval_remainderBoundInteraction_mult_neg_one
    · simpa [h_row_eval] using h_div
    · simpa [h_row_eval, env, row] using h_div_by_zero
  have h_consumerEval :
      consumerInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags.div *
            (1 -
              ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags.div_by_zero)))
          (ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessageExpr
            ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar)).toRaw).eval env := rfl
  have h_remainder_op :=
    ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage_op_of_signs row h_nr h_nb
  exact staticBinary_remainder_provider_of_active
    trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
    env row h_consumer h_active h_consumerEval h_row_eval h_remainder_op

/-- Layer-A op-bus provider-match wrapper for the Arith DIVUW operation
    (`OP_DIVU_W = 188`, W-mode `m32 = 1`).  Mirrors
    `main_request_divu_provided`, but
    delegates to the DIVUW keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_divuw_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The DIVU-mode op-bus bridge later
    reduces it to the div quotient-lane `opBus_row_ArithDiv`. -/
theorem main_request_divuw_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
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
    `main_request_divu_provided`, but
    delegates to the REMU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_remu_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The REMU-mode bridge in
    `ConstructionRemu.lean` later reduces it (at `div = 1`, `main_div = 0`,
    `main_mul = 0`) to the div remainder-lane `opBus_row_ArithDivSecondary`. -/
theorem main_request_remu_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
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
    `main_request_remu_provided`, but
    delegates to the REMUW keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_remuw_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The REMU-mode secondary bridge in
    `ConstructionRemu.lean` later reduces it (at `div = 1`, `main_div = 0`,
    `main_mul = 0`) to the div remainder-lane `opBus_row_ArithDivSecondary`; the
    `m32` flag plays no role in the mux. -/
theorem main_request_remuw_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_remuw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_mul_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_MUL) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_mul_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_rem_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_REM) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_rem_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_divw_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_DIV_W) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_divw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem main_request_remw_provided
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin numInstructions)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val = ZiskFv.Trusted.OP_REM_W) :
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
                (ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core)).toRaw).eval
      (trace.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core =
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
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)).toRaw).eval
          (trace.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.programLength) (program := trace.program)
        (trace.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_remw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
        trace.mainTable_mem trace.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

end ZiskFv.Compliance
