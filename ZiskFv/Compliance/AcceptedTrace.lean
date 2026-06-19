import ZiskFv.AirsClean.FullEnsemble.Balance
import ZiskFv.AirsClean.FullEnsemble.ArithBalance
import ZiskFv.Compliance.AeneasBridgeTrust
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Bridge.BinaryExtension
import ZiskFv.EquivCore.Promises.BranchHelpers
import ZiskFv.EquivCore.Promises.Fence
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.EquivCore.Promises.Jump
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.ShiftImm
import ZiskFv.EquivCore.Promises.UType


/-!
# Accepted trace construction spine (salvage)

The accepted-trace spine and the Layer-A op-bus provider-match wrappers that
genuinely consume `trace.balanced`. The P4 relabel (the per-op `*RowBinding`
records, the `construction_<op>` arms, and the entangled
`exists_construction_*_from_balance` wrappers) has been stripped; it smuggled
bucket-(a)/(c) facts through caller-supplied records instead of deriving them.

What remains here is the salvageable infrastructure:

* `AcceptedTrace` — the committed full-ensemble trace record.
* `ProgramBinding` — the table-skeleton bucket-(b) premise (Sail state sequence,
  the selected Main table, and its membership / component / index facts). The
  per-op decode/provenance projections that the relabel hung off this record are
  gone; the sound construction sources its residuals as honest top-level binders.
* The Layer-A `exists_*_provider_row_matches_*_from_binding` wrappers, which
  consume `trace.balanced` and the honest `h_main_active`/`h_main_op` hypotheses
  to derive the op-bus provider match (backed by the axiom-free Layer-B
  permutation theorems in `AirsClean/FullEnsemble/Balance.lean`).

The honest sound construction built on top of this lives in
`ZiskFv/Compliance/ConstructionSub.lean`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble

/-- Accepted committed trace for the full RV64IM Clean ensemble. -/
structure AcceptedTrace where
  length : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program length
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble
  constraints : witness.Constraints
  spec : witness.Spec
  balanced : witness.BalancedChannels


/-- The named program-binding premise for the P4 construction (table skeleton).

It supplies the Sail state sequence, the selected Main table, and the table's
membership / component / index facts. The sound construction sources its decode
and Sail-binding residuals as explicit top-level binders (see
`ConstructionSub.lean`), not as per-op projections of this record. -/
structure ProgramBinding (trace : AcceptedTrace) where
  stateAt :
    Fin trace.length →
      PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  mainTable : Air.Flat.Table FGL
  mainTable_mem : mainTable ∈ trace.witness.allTables
  mainTable_component :
    mainTable.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.length trace.program
  mainTable_index : ∀ i : Fin trace.length, i.val < mainTable.table.length

theorem exists_staticBinary_provider_row_matches_logic_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_AND
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_OR
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_staticBinary_provider_row_matches_sub_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_SUB) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_sub_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_add_provider_row_matches_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_ADD) :
    ZiskFv.Airs.Main.add_subset_holds
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val
    ∧
      ((∃ providerTable ∈ trace.witness.allTables,
        ∃ providerRow ∈ providerTable.table,
          providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
            ∧ providerTable.Spec
            ∧ ZiskFv.Airs.OperationBus.matches_entry
              (ZiskFv.Airs.OperationBus.opBus_row_Main
                (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
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
                (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
                i.val)
              (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                (ZiskFv.AirsClean.BinaryAdd.opBusMessage
                  (ZiskFv.AirsClean.BinaryAdd.component.rowInput
                    (providerTable.environment providerRow))) 1))) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  have h_main_component_spec :
      binding.mainTable.component.Spec
        (binding.mainTable.environment (binding.mainTable.table.get mainIdx)) := by
    simpa [mainRow] using
      trace.spec binding.mainTable binding.mainTable_mem mainRow h_mainRow_mem
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec
        (ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val) := by
    simpa [mainIdx] using
      ZiskFv.AirsClean.FullEnsemble.mainSpec_rowAt_mainOfTable_of_component_spec
        trace.program binding.mainTable mainIdx binding.mainTable_component
        h_main_component_spec
  have h_main_subset :
      ZiskFv.Airs.Main.add_subset_holds
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val h_main_spec
  exact ⟨h_main_subset,
    exists_add_provider_row_matches_legacy_main_of_add_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op⟩

theorem exists_staticBinary_provider_row_matches_compare_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_LT
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_LTU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_compare_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_staticBinary_provider_row_matches_w_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_ADD_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SUB_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_staticBinary_provider_row_matches_legacy_main_of_w_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

theorem exists_binaryExtension_provider_row_matches_shift_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SLL
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRL
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRA
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SLL_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRL_W
        ∨ ZiskFv.Airs.Main.Valid_Main.op
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val = ZiskFv.Trusted.OP_SRA_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component =
            ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.BinaryExtension.opBusMessage
                (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    exists_binaryExtension_provider_row_matches_legacy_main_of_shift_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith MULW operation
    (`OP_MUL_W = 182`).  Mirrors
    `exists_staticBinary_provider_row_matches_sub_from_binding`: it builds the
    Main op-bus interaction, proves membership + `mult = -1`, and delegates to
    the keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction`.

    Unlike the static-Binary wrappers, the provider here is the lookup-aware
    `arithMulProviderComponent` (= `ArithMul.componentWithArithTable`), so
    `providerTable.Spec` is `FullSpec (rowInput …)` and the match is against the
    ArithMul primary op-bus message. -/
theorem exists_arithMul_provider_row_matches_primary_of_mulw_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_MUL_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith MULHU operation
    (`OP_MULUH = 177`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_mulw_from_binding`, but
    delegates to the MULHU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction`.

    The returned match is still against the muxed `primaryOpBusMessage`; the
    MULHU-mode bridge in `ArithMul/Bridge.lean` later reduces it to the
    secondary d-lane `opBus_row_ArithMulSecondary`. -/
theorem exists_arithMul_provider_row_matches_secondary_of_mulhu_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_MULUH) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith DIVU operation
    (`OP_DIVU = 184`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_mulw_from_binding`, but
    delegates to the DIVU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The DIVU-mode bridge in
    `ArithMul/Bridge.lean` later reduces it to the div quotient-lane
    `opBus_row_ArithDiv`. -/
theorem exists_arithMul_provider_row_matches_primary_of_divu_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_DIVU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith DIVUW operation
    (`OP_DIVU_W = 188`, W-mode `m32 = 1`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_divu_from_binding`, but
    delegates to the DIVUW keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_divuw_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The DIVU-mode op-bus bridge later
    reduces it to the div quotient-lane `opBus_row_ArithDiv`. -/
theorem exists_arithMul_provider_row_matches_primary_of_divuw_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_DIVU_W) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_divuw_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

/-- Layer-A op-bus provider-match wrapper for the Arith REMU operation
    (`OP_REMU = 185`).  Mirrors
    `exists_arithMul_provider_row_matches_primary_of_divu_from_binding`, but
    delegates to the REMU keep-arithMul balance theorem
    `exists_arithMul_provider_row_matches_primary_of_remu_active_main_row_interaction`.

    The provider is the shared lookup-aware `arithMulProviderComponent` (the
    ArithDiv component carries no op-bus in the ensemble); the returned match is
    against the muxed `primaryOpBusMessage`.  The REMU-mode bridge in
    `ConstructionRemu.lean` later reduces it (at `div = 1`, `main_div = 0`,
    `main_mul = 0`) to the div remainder-lane `opBus_row_ArithDivSecondary`. -/
theorem exists_arithMul_provider_row_matches_primary_of_remu_from_binding
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (h_main_active :
      ZiskFv.Airs.Main.Valid_Main.is_external_op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = 1)
    (h_main_op :
      ZiskFv.Airs.Main.Valid_Main.op
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val = ZiskFv.Trusted.OP_REMU) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
              i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                  (providerTable.environment providerRow))) 1) := by
  have h_mainIdx_lt : i.val < binding.mainTable.table.length :=
    binding.mainTable_index i
  let mainIdx : Fin binding.mainTable.table.length :=
    ⟨i.val, h_mainIdx_lt⟩
  let mainRow := binding.mainTable.table.get mainIdx
  let mainInteraction :=
    ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core)).toRaw).eval
      (binding.mainTable.environment mainRow)
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by
    simp [mainRow]
  have h_main_row :
      eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core =
        ZiskFv.AirsClean.Main.rowAt
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
          i.val := by
    simpa [mainIdx, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable_core
        trace.program binding.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈
        binding.mainTable.interactionsWith
          ZiskFv.Channels.OperationBus.OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mem_interactionsWith
        (length := trace.length) (program := trace.program)
        binding.mainTable_component h_mainRow_mem
  have h_mainInteraction_eval :
      mainInteraction =
        ((ZiskFv.Channels.OperationBus.OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.length trace.program).rowInputVar.core)).toRaw).eval
          (binding.mainTable.environment mainRow) := rfl
  have h_active_row :
      (eval (binding.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.length trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_main_active
  have h_active : mainInteraction.mult = -1 := by
    rw [h_mainInteraction_eval]
    exact
      ZiskFv.AirsClean.FullEnsemble.main_op_row_eval_mult_neg_one_of_active
        (length := trace.length) (program := trace.program)
        (binding.mainTable.environment mainRow) h_active_row
  exact
    ZiskFv.AirsClean.FullEnsemble.exists_arithMul_provider_row_matches_primary_of_remu_active_main_row_interaction
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val trace.witness trace.constraints trace.balanced trace.spec
        binding.mainTable_mem binding.mainTable_component h_mainRow_mem
        h_main_row h_main_active h_mainInteraction_mem
        h_mainInteraction_eval h_active h_main_op

end ZiskFv.Compliance
