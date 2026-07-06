import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-! ## Row extraction from full-ensemble channel interactions -/

/-- If a table's operation-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_opBus_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- If a table's memory-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_memBus_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- If a table's memory-bus abstract interactions are exactly two entries,
    any concrete table-level interaction on that channel is one of those two
    entries evaluated at some row. -/
theorem exists_memBus_row_eval_of_pair_interactionsWith
    {table : Table FGL} {left right : AbstractInteraction FGL}
    (h_pair :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [left, right])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    (∃ row ∈ table.table,
      interaction = left.eval (table.environment row))
    ∨ (∃ row ∈ table.table,
      interaction = right.eval (table.environment row)) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_pair] at h_mem
  obtain ⟨row, h_row, h_eval⟩ := h_mem
  rcases h_eval with h_left | h_right
  · exact Or.inl ⟨row, h_row, h_left⟩
  · exact Or.inr ⟨row, h_row, h_right⟩

/-- Row extraction for the unified Main operation-bus interaction in the full
    ensemble. The extracted row is a `MainRowWithRom`; its `.core` is the same
    row that emits Main's memory-bus interactions. -/
theorem exists_main_op_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  · exact h_mem

/-- The concrete unified Main operation-bus interaction for any row of the
    selected Main table is a member of that table's op-bus interactions. -/
theorem main_op_row_eval_mem_interactionsWith
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {row : Array FGL}
    (h_row : row ∈ table.table) :
    ((OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core)).toRaw).eval
      (table.environment row) ∈ table.interactionsWith OpBusChannel.toRaw := by
  have h_singleton :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw)] := by
    simpa [h_component] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton]
  exact ⟨row, h_row, rfl⟩

/-- Row extraction for the unified Main memory-bus interactions in the full
    ensemble. Main exposes three memory interactions (`a`, `b`, and
    `c/store`), so the result keeps that side disjunction explicit. -/
theorem exists_main_mem_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg))
            (ZiskFv.AirsClean.Main.aMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg))
            (ZiskFv.AirsClean.Main.bMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg))
            (ZiskFv.AirsClean.Main.cMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row) := by
  have h_interactions :=
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_memBus
      length program
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_component, h_interactions] at h_mem
  rcases h_mem with ⟨row, h_row, h_eq | h_eq | h_eq⟩
  · exact ⟨row, h_row, Or.inl h_eq⟩
  · exact ⟨row, h_row, Or.inr (Or.inl h_eq)⟩
  · exact ⟨row, h_row, Or.inr (Or.inr h_eq)⟩

/-- Row extraction for a BinaryAdd operation-bus provider interaction in the
    full ensemble. -/
theorem exists_binaryAdd_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a lookup-aware Binary operation-bus provider
    interaction in the full ensemble. -/
theorem exists_staticBinary_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.Binary.opBusMessageExpr
            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Binary.staticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a lookup-aware BinaryExtension operation-bus provider
    interaction in the full ensemble. -/
theorem exists_staticBinaryExtension_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component :
      table.component = shiftStaticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            shiftStaticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for an ArithMul operation-bus provider interaction in the
    full ensemble. -/
theorem exists_arithMul_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = arithMulProviderComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
            arithMulProviderComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.ArithMul.componentWithArithTable_interactionsWith_opBus
  · exact h_mem

/-- Project the lookup-aware ArithMul provider branch's generic component
    `Spec` to the concrete `FullSpec`. -/
theorem arithMul_fullSpec_of_component_spec
    {table : Table FGL} {row : Array FGL}
    (h_component : table.component = arithMulProviderComponent)
    (h_spec : table.component.Spec (table.environment row)) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (arithMulProviderComponent.rowInput
        (table.environment row)) := by
  rw [h_component] at h_spec
  simpa [arithMulProviderComponent,
    ZiskFv.AirsClean.ArithMul.componentWithArithTable_spec] using h_spec

/-- A lookup-aware ArithMul provider branch can only match Main rows whose
    operation-bus opcode lies in the Arith ROM opcode range. -/
theorem arithMul_primary_provider_match_main_op_val_ge_176
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_full : ZiskFv.AirsClean.ArithMul.FullSpec row)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage row) 1)) :
    176 <= (m.op r_main).val := by
  have h_provider_ge :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.op_val_ge_176 row h_full.2.1
  have h_op_match : m.op r_main = row.flags.op := by
    simpa [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.ArithMul.primaryOpBusMessage] using h_match.2.1
  simpa [h_op_match] using h_provider_ge

/-- Full-ensemble version of
    `arithMul_primary_provider_match_main_op_val_ge_176`, projecting the
    generic component `Spec` to ArithMul `FullSpec` first. -/
theorem arithMul_provider_branch_main_op_val_ge_176
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1)) :
    176 <= (m.op r_main).val := by
  have h_full := arithMul_fullSpec_of_component_spec h_component h_providerSpec
  let env := providerTable.environment providerRow
  let row := eval env arithMulProviderComponent.rowInputVar
  have h_row_eq : row = arithMulProviderComponent.rowInput env := by
    dsimp [row]
    simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
      (eval_varFromOffset_valueFromOffset arithMulProviderComponent.Input 0 env)
  have h_full_row :
      ZiskFv.AirsClean.ArithMul.FullSpec row := by
    simpa [h_row_eq] using h_full
  have h_provider_ge :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.op_val_ge_176
      row h_full_row.2.1
  have h_op_match : m.op r_main = row.flags.op := by
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.eval_primaryOpBusMessageExpr_toEntry_op] at h_op
    simpa [row, env, ZiskFv.Airs.OperationBus.opBus_row_Main] using h_op
  simpa [h_op_match] using h_provider_ge

/-- The lookup-aware ArithMul branch cannot be the provider for a Main XOR
    operation.  This is the first Binary-family branch exclusion used by the
    P4 provider-match discharge. -/
theorem arithMul_provider_branch_ne_xor
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_XOR] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main XOR operation. -/
theorem staticBinaryExtension_provider_branch_ne_xor
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
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_bitwise_of_spec
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
  exact h_ne.2.2 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_XOR])

/-- The BinaryAdd provider branch cannot be the provider for a Main XOR
    operation. -/
theorem binaryAdd_provider_branch_ne_xor
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_XOR) :
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
  norm_num [ZiskFv.Trusted.OP_XOR] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main logical
    Binary operation (`AND`, `OR`, or `XOR`). -/
theorem arithMul_provider_branch_ne_staticBinaryLogic
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_and | h_or | h_xor
  · rw [h_and] at h_ge
    norm_num [ZiskFv.Trusted.OP_AND] at h_ge
  · rw [h_or] at h_ge
    norm_num [ZiskFv.Trusted.OP_OR] at h_ge
  · rw [h_xor] at h_ge
    norm_num [ZiskFv.Trusted.OP_XOR] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main logical Binary operation (`AND`, `OR`, or `XOR`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryLogic
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
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_bitwise_of_spec
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
  rcases h_main_op with h_and | h_or | h_xor
  · exact h_ne.1 (by
      rw [← h_provider_op, h_and]
      norm_num [ZiskFv.Trusted.OP_AND])
  · exact h_ne.2.1 (by
      rw [← h_provider_op, h_or]
      norm_num [ZiskFv.Trusted.OP_OR])
  · exact h_ne.2.2 (by
      rw [← h_provider_op, h_xor]
      norm_num [ZiskFv.Trusted.OP_XOR])

/-- The BinaryAdd provider branch cannot be the provider for a Main logical
    Binary operation (`AND`, `OR`, or `XOR`). -/
theorem binaryAdd_provider_branch_ne_staticBinaryLogic
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
      m.op r_main = ZiskFv.Trusted.OP_AND
        ∨ m.op r_main = ZiskFv.Trusted.OP_OR
        ∨ m.op r_main = ZiskFv.Trusted.OP_XOR) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_and | h_or | h_xor
  · rw [h_and] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_AND] at h_provider_op
  · rw [h_or] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_OR] at h_provider_op
  · rw [h_xor] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_XOR] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    comparison operation (`LT` or `LTU`). -/
theorem arithMul_provider_branch_ne_staticBinaryCompare
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_lt | h_ltu
  · rw [h_lt] at h_ge
    norm_num [ZiskFv.Trusted.OP_LT] at h_ge
  · rw [h_ltu] at h_ge
    norm_num [ZiskFv.Trusted.OP_LTU] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary comparison operation (`LT` or `LTU`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryCompare
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
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_compare_of_spec
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
  rcases h_main_op with h_lt | h_ltu
  · exact h_ne.2 (by
      rw [← h_provider_op, h_lt]
      norm_num [ZiskFv.Trusted.OP_LT])
  · exact h_ne.1 (by
      rw [← h_provider_op, h_ltu]
      norm_num [ZiskFv.Trusted.OP_LTU])

/-- The BinaryAdd provider branch cannot be the provider for a Main Binary
    comparison operation (`LT` or `LTU`). -/
theorem binaryAdd_provider_branch_ne_staticBinaryCompare
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
      m.op r_main = ZiskFv.Trusted.OP_LT
        ∨ m.op r_main = ZiskFv.Trusted.OP_LTU) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_lt | h_ltu
  · rw [h_lt] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_LT] at h_provider_op
  · rw [h_ltu] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_LTU] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    equality operation (`EQ`, value 9 < 176). -/
theorem arithMul_provider_branch_ne_staticBinaryEq
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_EQ) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_EQ] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary equality operation (`EQ`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryEq
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
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_EQ) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_eq_of_spec
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
  exact h_ne (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_EQ])

/-- The BinaryAdd provider branch cannot be the provider for a Main Binary
    equality operation (`EQ`, value 9 ≠ 10). -/
theorem binaryAdd_provider_branch_ne_staticBinaryEq
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_EQ) :
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
  norm_num [ZiskFv.Trusted.OP_EQ] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    `SUB` operation. -/
theorem arithMul_provider_branch_ne_staticBinarySub
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_SUB] at h_ge

/-- The lookup-aware ArithMul branch cannot be the provider for a Main Binary
    `ADD` operation. -/
theorem arithMul_provider_branch_ne_staticBinaryAdd
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_ADD) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rw [h_main_op] at h_ge
  norm_num [ZiskFv.Trusted.OP_ADD] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary `SUB` operation. -/
theorem staticBinaryExtension_provider_branch_ne_staticBinarySub
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
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_add_sub_of_spec
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
  exact h_ne.2 (by
    rw [← h_provider_op, h_main_op]
    norm_num [ZiskFv.Trusted.OP_SUB])

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main Binary `ADD` operation. -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryAdd
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
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_ADD) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_add_sub_of_spec
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
    norm_num [ZiskFv.Trusted.OP_ADD])

/-- The BinaryAdd provider branch cannot be the provider for a Main Binary
    `SUB` operation. -/
theorem binaryAdd_provider_branch_ne_staticBinarySub
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SUB) :
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
  norm_num [ZiskFv.Trusted.OP_SUB] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main W-mode
    Binary ADD/SUB operation (`ADDW` or `SUBW`). -/
theorem arithMul_provider_branch_ne_staticBinaryW
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_addw | h_subw
  · rw [h_addw] at h_ge
    norm_num [ZiskFv.Trusted.OP_ADD_W] at h_ge
  · rw [h_subw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SUB_W] at h_ge

/-- A lookup-aware BinaryExtension provider branch cannot be the provider for a
    Main W-mode Binary ADD/SUB operation (`ADDW` or `SUBW`). -/
theorem staticBinaryExtension_provider_branch_ne_staticBinaryW
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
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    False := by
  let env := providerTable.environment providerRow
  have h_componentSpec :
      shiftStaticLookupComponent.Spec env := by
    simpa [env, h_component] using h_providerSpec
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_op_val_ne_W_add_sub_of_spec
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
  rcases h_main_op with h_addw | h_subw
  · exact h_ne.1 (by
      rw [← h_provider_op, h_addw]
      norm_num [ZiskFv.Trusted.OP_ADD_W])
  · exact h_ne.2 (by
      rw [← h_provider_op, h_subw]
      norm_num [ZiskFv.Trusted.OP_SUB_W])

/-- The BinaryAdd provider branch cannot be the provider for a Main W-mode
    Binary ADD/SUB operation (`ADDW` or `SUBW`). -/
theorem binaryAdd_provider_branch_ne_staticBinaryW
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
      m.op r_main = ZiskFv.Trusted.OP_ADD_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SUB_W) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_addw | h_subw
  · rw [h_addw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_ADD_W] at h_provider_op
  · rw [h_subw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SUB_W] at h_provider_op

/-- The lookup-aware ArithMul branch cannot be the provider for a Main
    BinaryExtension shift operation. -/
theorem arithMul_provider_branch_ne_staticBinaryExtensionShift
    {m : ZiskFv.Airs.Main.Valid_Main FGL FGL} {r_main : ℕ}
    {providerTable : Table FGL} {providerRow : Array FGL}
    (h_component : providerTable.component = arithMulProviderComponent)
    (h_providerSpec :
      providerTable.component.Spec (providerTable.environment providerRow))
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
              arithMulProviderComponent.rowInputVar)) 1))
    (h_main_op :
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    False := by
  have h_ge :=
    arithMul_provider_branch_main_op_val_ge_176 h_component h_providerSpec h_match
  rcases h_main_op with h_sll | h_srl | h_sra | h_sllw | h_srlw | h_sraw
  · rw [h_sll] at h_ge
    norm_num [ZiskFv.Trusted.OP_SLL] at h_ge
  · rw [h_srl] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRL] at h_ge
  · rw [h_sra] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRA] at h_ge
  · rw [h_sllw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SLL_W] at h_ge
  · rw [h_srlw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRL_W] at h_ge
  · rw [h_sraw] at h_ge
    norm_num [ZiskFv.Trusted.OP_SRA_W] at h_ge

/-- A lookup-aware static Binary provider branch cannot be the provider for a
    Main BinaryExtension shift operation. -/
theorem staticBinary_provider_branch_ne_staticBinaryExtensionShift
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
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
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
  have h_contra
      (op_val : ℕ)
      (h_shift :
        op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W
          ∨ op_val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W)
      (h_emit : row.chain.b_op + 16 * row.mode.mode32 = (op_val : FGL)) :
      False :=
    ZiskFv.AirsClean.Binary.static_table_op_val_ne_binaryExtension_shift_of_emit
      row h_componentSpec.1 h_componentSpec.2 op_val h_shift h_emit
  rcases h_main_op with h_sll | h_srl | h_sra | h_sllw | h_srlw | h_sraw
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL
      (Or.inl rfl)
      (by
        rw [← h_provider_op, h_sll]
        norm_num [ZiskFv.Trusted.OP_SLL,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL
      (Or.inr (Or.inl rfl))
      (by
        rw [← h_provider_op, h_srl]
        norm_num [ZiskFv.Trusted.OP_SRL,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA
      (Or.inr (Or.inr (Or.inl rfl)))
      (by
        rw [← h_provider_op, h_sra]
        norm_num [ZiskFv.Trusted.OP_SRA,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W
      (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (by
        rw [← h_provider_op, h_sllw]
        norm_num [ZiskFv.Trusted.OP_SLL_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (by
        rw [← h_provider_op, h_srlw]
        norm_num [ZiskFv.Trusted.OP_SRL_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W])
  · exact h_contra ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (by
        rw [← h_provider_op, h_sraw]
        norm_num [ZiskFv.Trusted.OP_SRA_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W])

/-- The BinaryAdd provider branch cannot be the provider for a Main
    BinaryExtension shift operation. -/
theorem binaryAdd_provider_branch_ne_staticBinaryExtensionShift
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
      m.op r_main = ZiskFv.Trusted.OP_SLL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA
        ∨ m.op r_main = ZiskFv.Trusted.OP_SLL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRL_W
        ∨ m.op r_main = ZiskFv.Trusted.OP_SRA_W) :
    False := by
  have h_provider_op : (m.op r_main).val = 10 := by
    have h_op := h_match.2.1
    have h_op_val := congrArg Fin.val h_op
    simpa [ZiskFv.Airs.OperationBus.opBus_row_Main,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr,
      ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
      using h_op_val
  rcases h_main_op with h_sll | h_srl | h_sra | h_sllw | h_srlw | h_sraw
  · rw [h_sll] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SLL] at h_provider_op
  · rw [h_srl] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRL] at h_provider_op
  · rw [h_sra] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRA] at h_provider_op
  · rw [h_sllw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SLL_W] at h_provider_op
  · rw [h_srlw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRL_W] at h_provider_op
  · rw [h_sraw] at h_provider_op
    norm_num [ZiskFv.Trusted.OP_SRA_W] at h_provider_op


end ZiskFv.AirsClean.FullEnsemble
