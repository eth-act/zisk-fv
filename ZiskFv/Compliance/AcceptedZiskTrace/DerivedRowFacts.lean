import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.Compliance.SharedBundles
import ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridges

/-!
# Facts derived once at the accepted-trace ensemble seam

This module is the proof-facing boundary between a verifier-accepted Clean
ensemble and opcode constructions.  It deliberately exposes facts in two
layers:

* `opProviderRowFacts` is opcode-independent.  Every active Main operation-bus
  pull has one concrete provider row, carrying its component `Spec`, and an
  exact legacy-entry match.  The four possible provider components remain an
  explicit sum; opcode-local facts may eliminate the impossible branches.
* `registerWriteLanes` derives Main's register-write lane relation for the
  concrete row selected by an instruction index.  Constructions no longer need
  to repeat the `mainTableRowAtOrZero`/`rowAt` transport proof.
* `mainRowPins` packages the accepted trace's indexed Main activation/opcode
  facts after transporting them to the canonical `mainOfTable` view.

Both results are consequences of `AcceptedZiskTrace`: no new premise or trust
surface is introduced.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- The four operation-bus provider row shapes present in the full RV64IM
ensemble.  Each branch carries row membership, the row-local Clean spec, the
provider component identity, and equality with the selected Main request in the
legacy `matches_entry` view used by the current equivalence layer. -/
def OpProviderRowBranch
    (mainEntry : ZiskFv.Airs.OperationBus.OperationBusEntry FGL)
    (providerTable : Table FGL) : Prop :=
  (∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component = arithMulProviderComponent
        ∧ ZiskFv.Airs.OperationBus.matches_entry mainEntry
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                arithMulProviderComponent.rowInputVar)) 1))
  ∨ (∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component =
          ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
        ∧ ZiskFv.Airs.OperationBus.matches_entry mainEntry
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInputVar)) 1))
  ∨ (∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
        ∧ ZiskFv.Airs.OperationBus.matches_entry mainEntry
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.Binary.opBusMessageExpr
                ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
  ∨ (∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
        ∧ ZiskFv.Airs.OperationBus.matches_entry mainEntry
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (eval (providerTable.environment providerRow)
              (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))

/-- Opcode-independent operation-bus provider facts for one indexed Main row.
The branch itself contains the concrete provider row, its `Spec`, component
identity, and exact entry match. -/
def OpProviderRowFacts
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n) : Prop :=
  ∃ providerTable ∈ trace.witness.allTables,
    OpProviderRowBranch
      (ZiskFv.Airs.OperationBus.opBus_row_Main
        (mainOfTable trace.program trace.mainTable) i.val)
      providerTable

/-- Channel balance, table constraints, and table soundness derive a concrete
provider row for every active indexed Main operation-bus request. -/
theorem AcceptedZiskTrace.opProviderRowFacts
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n)
    (h_active : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1) :
    OpProviderRowFacts trace i := by
  have h_mainIdx_lt : i.val < trace.mainTable.table.length :=
    trace.mainTable_index i
  let mainIdx : Fin trace.mainTable.table.length := ⟨i.val, h_mainIdx_lt⟩
  let mainRow := trace.mainTable.table.get mainIdx
  let mainInteraction :=
    ((OpBusChannel.emitted
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
          (mainOfTable trace.program trace.mainTable) i.val := by
    simpa [mainIdx, mainRow] using
      rowAt_mainOfTable_core trace.program trace.mainTable mainIdx
  have h_mainInteraction_mem :
      mainInteraction ∈ trace.mainTable.interactionsWith OpBusChannel.toRaw := by
    simpa [mainInteraction, mainRow] using
      main_op_row_eval_mem_interactionsWith
        (length := trace.programLength) (program := trace.program)
        trace.mainTable_component h_mainRow_mem
  have h_active_row :
      (eval (trace.mainTable.environment mainRow)
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar.core).is_external_op = 1 := by
    rw [h_main_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_active
  have h_interaction_active : mainInteraction.mult = -1 := by
    exact main_op_row_eval_mult_neg_one_of_active
      (length := trace.programLength) (program := trace.program)
      (trace.mainTable.environment mainRow) h_active_row
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (trace.mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              trace.programLength trace.program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main
          (mainOfTable trace.program trace.mainTable) i.val := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr, h_main_row]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_active]
  obtain ⟨_selectedMainRow, _h_selectedMainRow, _h_mainSpec, _h_selectedMainEval,
      _providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, _h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      trace.witness trace.constraints_hold trace.channels_balanced trace.spec_holds
      trace.mainTable_mem trace.mainTable_component
      h_mainInteraction_mem h_interaction_active
  refine ⟨providerTable, h_providerTable, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_arithMul
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_component, ?_⟩
    rw [← h_main_entry]
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binExt
    right; left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_component, ?_⟩
    rw [← h_main_entry]
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binary
    right; right; left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_component, ?_⟩
    rw [← h_main_entry]
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_component,
      h_providerEval⟩ := h_binaryAdd
    right; right; right
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_component, ?_⟩
    rw [← h_main_entry]
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval]
    exact h_msg

/-- Specialize the generic provider branch to the static-Binary provider for
`OP_SUB`.  Only opcode-local impossibility lemmas remain here; row selection,
balance, table classification, and entry matching are all inherited from
`opProviderRowFacts`. -/
theorem AcceptedZiskTrace.staticBinarySubProviderRowFacts
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n)
    (h_active : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_op : (mainOfTable trace.program trace.mainTable).op i.val =
      ZiskFv.Trusted.OP_SUB) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable trace.program trace.mainTable) i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  obtain ⟨providerTable, h_providerTable, h_branch⟩ :=
    trace.opProviderRowFacts i h_active
  rcases h_branch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_row, h_spec, h_component, h_match⟩ := h_arithMul
    exact False.elim
      (arithMul_provider_branch_ne_staticBinarySub
        h_component h_spec h_match h_op)
  · obtain ⟨providerRow, _h_row, h_spec, h_component, h_match⟩ := h_binExt
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinarySub
        h_component h_spec h_match h_op)
  · obtain ⟨providerRow, h_row, _h_spec, h_component, h_match⟩ := h_binary
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main
            (mainOfTable trace.program trace.mainTable) i.val)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_row, h_component,
      trace.spec_holds providerTable h_providerTable, h_match_row⟩
  · obtain ⟨_providerRow, _h_row, _h_spec, _h_component, h_match⟩ := h_binaryAdd
    exact False.elim (binaryAdd_provider_branch_ne_staticBinarySub h_match h_op)

/-- Specialize the generic provider branch to the static-Binary provider for
Boolean logic operations.  This is the shape-level counterpart of
`staticBinarySubProviderRowFacts`: balance and row selection stay generic while
only the opcode-family branch eliminations are specialized. -/
theorem AcceptedZiskTrace.staticBinaryLogicProviderRowFacts
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n)
    (h_active : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND
        ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR
        ∨ (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR) :
    ∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main
              (mainOfTable trace.program trace.mainTable) i.val)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.Binary.opBusMessage
                (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                  (providerTable.environment providerRow))) 1) := by
  obtain ⟨providerTable, h_providerTable, h_branch⟩ :=
    trace.opProviderRowFacts i h_active
  rcases h_branch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, _h_row, h_spec, h_component, h_match⟩ := h_arithMul
    exact False.elim
      (arithMul_provider_branch_ne_staticBinaryLogic
        h_component h_spec h_match h_op)
  · obtain ⟨providerRow, _h_row, h_spec, h_component, h_match⟩ := h_binExt
    exact False.elim
      (staticBinaryExtension_provider_branch_ne_staticBinaryLogic
        h_component h_spec h_match h_op)
  · obtain ⟨providerRow, h_row, _h_spec, h_component, h_match⟩ := h_binary
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main
            (mainOfTable trace.program trace.mainTable) i.val)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_row, h_component,
      trace.spec_holds providerTable h_providerTable, h_match_row⟩
  · obtain ⟨_providerRow, _h_row, _h_spec, _h_component, h_match⟩ := h_binaryAdd
    exact False.elim (binaryAdd_provider_branch_ne_staticBinaryLogic h_match h_op)

/-- The canonical indexed Main row pins its own activation and opcode columns.
This is the hypothesis-free seam fact; an opcode arm specializes the two indices
using the decode equalities already derived from the accepted Main/ROM row. -/
theorem AcceptedZiskTrace.mainRowPins
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n) :
    ZiskFv.Compliance.MainRowPins
      (mainOfTable trace.program trace.mainTable) i.val
      ((mainOfTable trace.program trace.mainTable).is_external_op i.val)
      ((mainOfTable trace.program trace.mainTable).op i.val) := by
  exact ⟨rfl, rfl⟩

/-- Specialize the hypothesis-free Main pins to literals established by an
accepted instruction arm's decode facts. -/
theorem AcceptedZiskTrace.mainRowPinsOfEq
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n)
    (active opKind : FGL)
    (h_active : (mainOfTable trace.program trace.mainTable).is_external_op i.val = active)
    (h_op : (mainOfTable trace.program trace.mainTable).op i.val = opKind) :
    ZiskFv.Compliance.MainRowPins
      (mainOfTable trace.program trace.mainTable) i.val active opKind := by
  exact ⟨h_active, h_op⟩

/-- Main's concrete `c` memory-bus message has the register-write lane relation
whenever the indexed Main row is in the arithmetic (`store_pc = 0`) mode. -/
theorem AcceptedZiskTrace.registerWriteLanes
    {n : Nat} (trace : AcceptedZiskTrace n) (i : Fin n)
    (h_store_pc : (mainOfTable trace.program trace.mainTable).store_pc i.val = 0) :
    ZiskFv.Airs.MemoryBus.register_write_lanes_match
      (mainOfTable trace.program trace.mainTable) i.val
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage
          (mainTableRowAtOrZero trace.program trace.mainTable i.val)) 1 1) := by
  let row := mainTableRowAtOrZero trace.program trace.mainTable i.val
  have h_row :
      row.core = ZiskFv.AirsClean.Main.rowAt
        (mainOfTable trace.program trace.mainTable) i.val := by
    have h := rowAt_mainOfTable trace.program trace.mainTable
      ⟨i.val, trace.mainTable_index i⟩
    simpa [row, mainTableRowAtOrZero_get
      (idx := ⟨i.val, trace.mainTable_index i⟩)] using h.symm
  have h_row_store_pc : row.core.store_pc = 0 := by
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  have h_lanes :=
    ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
      row h_row_store_pc
  rw [h_row] at h_lanes
  simpa [row, ZiskFv.AirsClean.Main.validOfRow,
    ZiskFv.AirsClean.Main.rowAt] using h_lanes

end ZiskFv.Compliance
