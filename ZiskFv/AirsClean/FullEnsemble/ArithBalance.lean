import ZiskFv.AirsClean.FullEnsemble.Balance

/-!
# Full Clean ensemble balance projections — Arith MULW keep/refute

This module mirrors the BinaryExtension-shift keep/refute projections in
`FullEnsemble.Balance` for the Arith MULW operation (`OP_MUL_W = 182`).
The shift module keeps the BinaryExtension provider branch and refutes the
ArithMul / Binary / BinaryAdd provider branches; here the roles are swapped:
MULW keeps the ArithMul provider branch and refutes the BinaryExtension /
static Binary / BinaryAdd provider branches.

## Trust note

0 PROJECT (`ZiskFv.*`) axioms; Sail+kernel as documented external trust.
These lemmas only reuse the static-table op-value exclusions
(`*_ne_arith_mul_w`) and the same `EnsembleWitness.BalancedChannels`
unpacking as `FullEnsemble.Balance`.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- A lookup-aware static Binary provider branch cannot be the provider for a
    Main Arith MULW operation (`OP_MUL_W = 182`). -/
theorem staticBinary_provider_branch_ne_arithMulPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Binary.opBusMessageExpr
              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_MUL_W) :
    False := by
  let env := providerTable.environment providerRow
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput env
  have h_componentSpec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_componentSpec
  have h_provider_op :
      m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := by
    have h_op := h_match.2.1
    simpa [env, row, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_op
  exact ZiskFv.AirsClean.Binary.static_table_op_val_ne_arith_mul_w_of_emit
    row h_componentSpec.1 h_componentSpec.2
    (by
      rw [← h_provider_op, h_main_op]
      norm_num [ZiskFv.Trusted.OP_MUL_W])

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Arith MULW operation (`OP_MUL_W = 182`). -/
theorem staticBinaryExtension_provider_branch_ne_arithMulPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_MUL_W) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_arith_mul_w_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.1 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_MUL_W])

/-- The BinaryAdd provider branch cannot be the provider for a Main Arith MULW
    operation (`OP_MUL_W = 182`). -/
theorem binaryAdd_provider_branch_ne_arithMulPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_MUL_W) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rw [h_main_op] at h_provider_op
  norm_num [ZiskFv.Trusted.OP_MUL_W] at h_provider_op

/-- An active unified-Main MULW operation-bus interaction is balanced by an
    Arith-Mul provider row carrying `witness.Spec`, whose primary operation-bus
    message matches the Main row's emission. This keeps the ArithMul provider
    branch and refutes the BinaryExtension / static Binary / BinaryAdd
    provider branches via the `*_ne_arithMulPrimary` exclusions. -/
theorem exists_arithMul_provider_row_matches_primary_of_mulw_active_main_row_interaction
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
      m.op r_main = ZiskFv.Trusted.OP_MUL_W) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
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
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
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
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
              (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                (providerTable.environment providerRow))) 1) := by
      rw [ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr] at h_match
      have h_row_eq :
          eval (providerTable.environment providerRow)
              arithMulProviderComponent.rowInputVar =
            arithMulProviderComponent.rowInput
              (providerTable.environment providerRow) := by
        simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar]
          using
            (eval_varFromOffset_valueFromOffset arithMulProviderComponent.Input 0
              (providerTable.environment providerRow))
      rwa [h_row_eq] at h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
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
      (staticBinaryExtension_provider_branch_ne_arithMulPrimary
        h_component h_providerSpec h_match h_main_op)
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
      (staticBinary_provider_branch_ne_arithMulPrimary
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
      (binaryAdd_provider_branch_ne_arithMulPrimary h_match h_main_op)

/-! ## Arith MULHU keep/refute (`OP_MULUH = 177`)

Mirror of the MULW keep/refute above, for the unsigned high-half MUL.  The
keep theorem produces the SAME muxed `primaryOpBusMessage` match (the balance
machinery only emits the provider's primary message); the MULHU-mode bridge
in `ArithMul/Bridge.lean` reduces that muxed message — at `main_mul = 0`,
`main_div = 0`, `div = 0` — to the secondary d-lane message
`opBus_row_ArithMulSecondary` the wrapper consumes.  The three non-arith
provider branches are refuted via the op-177 static-table exclusions. -/

/-- A lookup-aware static Binary provider branch cannot be the provider for a
    Main Arith MULHU operation (`OP_MULUH = 177`). -/
theorem staticBinary_provider_branch_ne_arithMulSecondary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Binary.opBusMessageExpr
              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_MULUH) :
    False := by
  let env := providerTable.environment providerRow
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput env
  have h_componentSpec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_componentSpec
  have h_provider_op :
      m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := by
    have h_op := h_match.2.1
    simpa [env, row, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_op
  exact ZiskFv.AirsClean.Binary.static_table_op_val_ne_arith_mul_uh_of_emit
    row h_componentSpec.1 h_componentSpec.2
    (by
      rw [← h_provider_op, h_main_op]
      norm_num [ZiskFv.Trusted.OP_MULUH])

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Arith MULHU operation (`OP_MULUH = 177`). -/
theorem staticBinaryExtension_provider_branch_ne_arithMulSecondary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_MULUH) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_arith_mul_uh_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.1 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_MULUH])

/-- The BinaryAdd provider branch cannot be the provider for a Main Arith MULHU
    operation (`OP_MULUH = 177`). -/
theorem binaryAdd_provider_branch_ne_arithMulSecondary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_MULUH) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rw [h_main_op] at h_provider_op
  norm_num [ZiskFv.Trusted.OP_MULUH] at h_provider_op

/-- An active unified-Main MULHU operation-bus interaction is balanced by an
    Arith-Mul provider row carrying `witness.Spec`, whose primary (muxed)
    operation-bus message matches the Main row's emission.  Keeps the ArithMul
    provider branch and refutes the BinaryExtension / static Binary / BinaryAdd
    provider branches via the `*_ne_arithMulSecondary` exclusions. -/
theorem exists_arithMul_provider_row_matches_secondary_of_mulhu_active_main_row_interaction
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
      m.op r_main = ZiskFv.Trusted.OP_MULUH) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
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
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
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
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
              (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                (providerTable.environment providerRow))) 1) := by
      rw [ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr] at h_match
      have h_row_eq :
          eval (providerTable.environment providerRow)
              arithMulProviderComponent.rowInputVar =
            arithMulProviderComponent.rowInput
              (providerTable.environment providerRow) := by
        simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar]
          using
            (eval_varFromOffset_valueFromOffset arithMulProviderComponent.Input 0
              (providerTable.environment providerRow))
      rwa [h_row_eq] at h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
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
      (staticBinaryExtension_provider_branch_ne_arithMulSecondary
        h_component h_providerSpec h_match h_main_op)
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
      (staticBinary_provider_branch_ne_arithMulSecondary
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
      (binaryAdd_provider_branch_ne_arithMulSecondary h_match h_main_op)

/-! ## Arith DIVU keep/refute (`OP_DIVU = 184`)

Mirror of the MULW keep/refute above, for the unsigned DIVU operation.  The
provider is still the shared ArithMul `componentWithArithTable` (the ArithDiv
component carries no op-bus interactions in the ensemble — see
`arithDiv_table_interactionsWith_opBus_nil`).  The keep theorem produces the
SAME muxed `primaryOpBusMessage` match; the DIVU-mode bridge in
`ArithMul/Bridge.lean` reduces that muxed message — at `div = 1`,
`main_div = 1`, `main_mul = 0` — to the div quotient-lane message
`opBus_row_ArithDiv` the DIVU wrapper consumes.  The three non-arith provider
branches are refuted via the op-184 static-table exclusions. -/

/-- A lookup-aware static Binary provider branch cannot be the provider for a
    Main Arith DIVU operation (`OP_DIVU = 184`). -/
theorem staticBinary_provider_branch_ne_arithDivuPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Binary.opBusMessageExpr
              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_DIVU) :
    False := by
  let env := providerTable.environment providerRow
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput env
  have h_componentSpec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_componentSpec
  have h_provider_op :
      m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := by
    have h_op := h_match.2.1
    simpa [env, row, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_op
  exact ZiskFv.AirsClean.Binary.static_table_op_val_ne_arith_divu_of_emit
    row h_componentSpec.1 h_componentSpec.2
    (by
      rw [← h_provider_op, h_main_op]
      norm_num [ZiskFv.Trusted.OP_DIVU])

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Arith DIVU operation (`OP_DIVU = 184`). -/
theorem staticBinaryExtension_provider_branch_ne_arithDivuPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_DIVU) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_arith_divu_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.1 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_DIVU])

/-- The BinaryAdd provider branch cannot be the provider for a Main Arith DIVU
    operation (`OP_DIVU = 184`). -/
theorem binaryAdd_provider_branch_ne_arithDivuPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_DIVU) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rw [h_main_op] at h_provider_op
  norm_num [ZiskFv.Trusted.OP_DIVU] at h_provider_op

/-- An active unified-Main DIVU operation-bus interaction is balanced by an
    Arith-Mul provider row carrying `witness.Spec`, whose primary (muxed)
    operation-bus message matches the Main row's emission.  Keeps the ArithMul
    provider branch and refutes the BinaryExtension / static Binary / BinaryAdd
    provider branches via the `*_ne_arithDivuPrimary` exclusions. -/
theorem exists_arithMul_provider_row_matches_primary_of_divu_active_main_row_interaction
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
      m.op r_main = ZiskFv.Trusted.OP_DIVU) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
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
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
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
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
              (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                (providerTable.environment providerRow))) 1) := by
      rw [ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr] at h_match
      have h_row_eq :
          eval (providerTable.environment providerRow)
              arithMulProviderComponent.rowInputVar =
            arithMulProviderComponent.rowInput
              (providerTable.environment providerRow) := by
        simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar]
          using
            (eval_varFromOffset_valueFromOffset arithMulProviderComponent.Input 0
              (providerTable.environment providerRow))
      rwa [h_row_eq] at h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
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
      (staticBinaryExtension_provider_branch_ne_arithDivuPrimary
        h_component h_providerSpec h_match h_main_op)
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
      (staticBinary_provider_branch_ne_arithDivuPrimary
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
      (binaryAdd_provider_branch_ne_arithDivuPrimary h_match h_main_op)

/-! ## Arith DIVUW keep/refute (`OP_DIVU_W = 188`)

Mirror of the DIVU keep/refute above, for the unsigned W-mode DIVUW operation
(`m32 = 1`).  The provider is still the shared ArithMul `componentWithArithTable`
(the ArithDiv component carries no op-bus in the ensemble).  The keep theorem
produces the SAME muxed `primaryOpBusMessage` match; the DIVU-mode op-bus bridge
reduces that muxed message — at `div = 1`, `main_div = 1`, `main_mul = 0` (all
uniform for op 188) — to the div quotient-lane message `opBus_row_ArithDiv` the
DIVUW wrapper consumes.  The three non-arith provider branches are refuted via
the op-188 static-table exclusions. -/

/-- A lookup-aware static Binary provider branch cannot be the provider for a
    Main Arith DIVUW operation (`OP_DIVU_W = 188`). -/
theorem staticBinary_provider_branch_ne_arithDivuwPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Binary.opBusMessageExpr
              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_DIVU_W) :
    False := by
  let env := providerTable.environment providerRow
  let row := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput env
  have h_componentSpec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_componentSpec
  have h_provider_op :
      m.op r_main = row.chain.b_op + 16 * row.mode.mode32 := by
    have h_op := h_match.2.1
    simpa [env, row, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr,
      ZiskFv.AirsClean.Binary.opBusMessage] using h_op
  exact ZiskFv.AirsClean.Binary.static_table_op_val_ne_arith_divuw_of_emit
    row h_componentSpec.1 h_componentSpec.2
    (by
      rw [← h_provider_op, h_main_op]
      norm_num [ZiskFv.Trusted.OP_DIVU_W])

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Arith DIVUW operation (`OP_DIVU_W = 188`). -/
theorem staticBinaryExtension_provider_branch_ne_arithDivuwPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component :
      providerTable.component = shiftStaticLookupComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              shiftStaticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_DIVU_W) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_arith_divuw_of_spec
      env h_componentSpec
  have h_provider_op :
      (m.op r_main).val =
        (shiftStaticLookupComponent.rowInput env).flags.op.val := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [env, ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_eval_opBusMessageExpr_op]
      using h_op_val
  exact h_ne.1 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_DIVU_W])

/-- The BinaryAdd provider branch cannot be the provider for a Main Arith DIVUW
    operation (`OP_DIVU_W = 188`). -/
theorem binaryAdd_provider_branch_ne_arithDivuwPrimary
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_DIVU_W) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rw [h_main_op] at h_provider_op
  norm_num [ZiskFv.Trusted.OP_DIVU_W] at h_provider_op

/-- An active unified-Main DIVUW operation-bus interaction is balanced by an
    Arith-Mul provider row carrying `witness.Spec`, whose primary (muxed)
    operation-bus message matches the Main row's emission.  Keeps the ArithMul
    provider branch and refutes the BinaryExtension / static Binary / BinaryAdd
    provider branches via the `*_ne_arithDivuwPrimary` exclusions. -/
theorem exists_arithMul_provider_row_matches_primary_of_divuw_active_main_row_interaction
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
      m.op r_main = ZiskFv.Trusted.OP_DIVU_W) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = arithMulProviderComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
            (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
            (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
              (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
                (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
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
  · obtain ⟨providerRow, h_providerRow, _h_providerSpec, h_component,
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
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
          (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
              (ZiskFv.AirsClean.ArithMul.componentWithArithTable.rowInput
                (providerTable.environment providerRow))) 1) := by
      rw [ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr] at h_match
      have h_row_eq :
          eval (providerTable.environment providerRow)
              arithMulProviderComponent.rowInputVar =
            arithMulProviderComponent.rowInput
              (providerTable.environment providerRow) := by
        simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar]
          using
            (eval_varFromOffset_valueFromOffset arithMulProviderComponent.Input 0
              (providerTable.environment providerRow))
      rwa [h_row_eq] at h_match
    exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_component, h_specs providerTable h_providerTable, h_match_row⟩
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
      (staticBinaryExtension_provider_branch_ne_arithDivuwPrimary
        h_component h_providerSpec h_match h_main_op)
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
      (staticBinary_provider_branch_ne_arithDivuwPrimary
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
      (binaryAdd_provider_branch_ne_arithDivuwPrimary h_match h_main_op)

end ZiskFv.AirsClean.FullEnsemble
