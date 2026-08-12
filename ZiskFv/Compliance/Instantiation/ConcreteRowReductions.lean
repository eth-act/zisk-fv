import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.RegisterStepRangeProviderMatch
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.StaticCircuit
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.RegisterStepRangeSlice
import ZiskFv.AirsClean.RegisterBoundary

/-!
# Concrete row interaction reductions

Reusable reductions from one-row Clean tables to explicit channel interactions.
These are intended as row-local inputs to the forward channel-balance witness in #219.
-/

namespace ZiskFv.Compliance.Instantiation

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.RegisterBoundary (RegisterBoundaryRow bootMessage reloadMessage)

def emptyData : ProverData FGL := fun _ _ => #[]

private def proverEnvFromInput {Input : TypeMap} [ProvableType Input]
    (row : Input FGL) : ProverEnvironment FGL where
  get := (Environment.fromInput row emptyData).get
  data := emptyData
  hint := ProverHint.empty FGL

private def proverEnvFromEnvironment (env : Environment FGL) : ProverEnvironment FGL where
  get := env.get
  data := env.data
  hint := ProverHint.empty FGL

private theorem eval_proverEnvFromInput_varFromOffset_zero
    {Input : TypeMap} [ProvableType Input] (row : Input FGL) :
    Eval.eval (proverEnvFromInput row) (varFromOffset (F := FGL) Input 0) = row := by
  rw [ProvableType.eval_varFromOffset_prover, ProvableType.fromElements_eq_iff, Vector.ext_iff]
  intro i hi
  simp [proverEnvFromInput, Vector.getElem_mapRange, Vector.getElem?_toArray,
    Vector.getElem?_eq_getElem hi]

private theorem flatForAllWitness_of_localLength_zero
    {env : ProverEnvironment FGL} {offset : ℕ} {ops : List (FlatOperation FGL)}
    (h_len : FlatOperation.localLength ops = 0) :
    FlatOperation.forAll offset
      { witness := fun offset _ compute => env.ExtendsVector (compute env) offset }
      ops := by
  induction ops generalizing offset with
  | nil => trivial
  | cons op ops ih =>
      cases op with
      | witness m compute =>
          simp [FlatOperation.localLength] at h_len
          have h_m : m = 0 := by omega
          have h_ops : FlatOperation.localLength ops = 0 := by omega
          subst m
          constructor
          · intro i
            exact Fin.elim0 i
          · simpa [Nat.zero_add] using ih (offset := offset) h_ops
      | assert e =>
          simp [FlatOperation.localLength] at h_len
          simpa [FlatOperation.forAll] using ih (offset := offset) h_len
      | lookup l =>
          simp [FlatOperation.localLength] at h_len
          simpa [FlatOperation.forAll] using ih (offset := offset) h_len
      | interact i =>
          simp [FlatOperation.localLength] at h_len
          simpa [FlatOperation.forAll] using ih (offset := offset) h_len

private theorem usesLocalWitnesses_of_localLength_zero
    {env : ProverEnvironment FGL} {offset : ℕ} {ops : Operations FGL}
    (h_len : ops.localLength = 0) :
    env.UsesLocalWitnesses offset ops := by
  rw [ProverEnvironment.UsesLocalWitnesses, Operations.forAllFlat]
  induction ops using Operations.induct generalizing offset with
  | empty => trivial
  | witness m compute ops ih =>
      simp [Operations.localLength] at h_len
      have h_m : m = 0 := by omega
      have h_ops : ops.localLength = 0 := by omega
      subst m
      constructor
      · intro i
        exact Fin.elim0 i
      · simpa [Nat.zero_add] using ih (offset := offset) h_ops
  | assert e ops ih =>
      simp [Operations.localLength] at h_len
      simpa [Operations.forAll] using ih (offset := offset) h_len
  | lookup l ops ih =>
      simp [Operations.localLength] at h_len
      simpa [Operations.forAll] using ih (offset := offset) h_len
  | interact i ops ih =>
      simp [Operations.localLength] at h_len
      simpa [Operations.forAll] using ih (offset := offset) h_len
  | subcircuit s ops ih =>
      simp [Operations.localLength] at h_len
      have h_s : s.localLength = 0 := by omega
      have h_ops : ops.localLength = 0 := by omega
      constructor
      · apply flatForAllWitness_of_localLength_zero
        rw [← s.localLength_eq]
        exact h_s
      · exact ih (offset := s.localLength + offset) h_ops

private theorem component_constraintsHold_of_proverAssumptions
    (component : Component FGL) (row : component.Input FGL)
    (h_localLength : component.circuit.localLength component.rowInputVar = 0)
    (h_assumptions :
      component.circuit.ProverAssumptions row emptyData (ProverHint.empty FGL)) :
    component.operations.ConstraintsHold (Environment.fromInput row emptyData) := by
  let env := proverEnvFromInput row
  have h_env : env.UsesLocalWitnesses component.rowOffset component.rowOperations := by
    apply usesLocalWitnesses_of_localLength_zero
    change ((component.circuit.main component.rowInputVar).localLength component.rowOffset) = 0
    rw [component.circuit.localLength_eq]
    exact h_localLength
  have h_input : Eval.eval env component.rowInputVar = row := by
    dsimp [env, Component.rowInputVar]
    exact eval_proverEnvFromInput_varFromOffset_zero row
  have h_assumptions' :
      component.circuit.ProverAssumptions (Eval.eval env component.rowInputVar)
        env.data env.hint := by
    rw [h_input]
    simpa [env, proverEnvFromInput] using h_assumptions
  have h_full :=
    component.circuit.original_full_completeness component.rowOffset env component.rowInputVar
      h_env h_assumptions'
  have h_row : component.rowOperations.ConstraintsHold (env : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  have h_env_eq : (env : Environment FGL) = Environment.fromInput row emptyData := by
    rfl
  rw [← h_env_eq]
  exact (Component.constraintsHold_iff (component := component) (env : Environment FGL)).mpr h_row

private theorem component_constraintsHold_of_proverAssumptions_at
    (component : Component FGL) (env : Environment FGL) (row : component.Input FGL)
    (h_localLength : component.circuit.localLength component.rowInputVar = 0)
    (h_input : Eval.eval env component.rowInputVar = row)
    (h_data : env.data = emptyData)
    (h_assumptions :
      component.circuit.ProverAssumptions row emptyData (ProverHint.empty FGL)) :
    component.operations.ConstraintsHold env := by
  let proverEnv := proverEnvFromEnvironment env
  have h_env : proverEnv.UsesLocalWitnesses component.rowOffset component.rowOperations := by
    apply usesLocalWitnesses_of_localLength_zero
    change ((component.circuit.main component.rowInputVar).localLength component.rowOffset) = 0
    rw [component.circuit.localLength_eq]
    exact h_localLength
  have h_input' : Eval.eval proverEnv component.rowInputVar = row := by
    unfold Component.rowInputVar at h_input ⊢
    rw [ProvableType.eval_varFromOffset_prover]
    rw [← h_input]
    rw [ProvableType.eval_varFromOffset]
    congr
  have h_assumptions' :
      component.circuit.ProverAssumptions (Eval.eval proverEnv component.rowInputVar)
        proverEnv.data proverEnv.hint := by
    rw [h_input']
    simpa [proverEnv, proverEnvFromEnvironment, h_data] using h_assumptions
  have h_full :=
    component.circuit.original_full_completeness component.rowOffset proverEnv component.rowInputVar
      h_env h_assumptions'
  have h_row : component.rowOperations.ConstraintsHold (proverEnv : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  simpa [proverEnv, proverEnvFromEnvironment] using
    (Component.constraintsHold_iff (component := component)
      (env := (proverEnv : Environment FGL))).mpr h_row

theorem component_constraintsHold_of_proverAssumptions_at_data
    (component : Component FGL) (env : Environment FGL) (row : component.Input FGL)
    (data : ProverData FGL)
    (h_localLength : component.circuit.localLength component.rowInputVar = 0)
    (h_input : Eval.eval env component.rowInputVar = row)
    (h_data : env.data = data)
    (h_assumptions :
      component.circuit.ProverAssumptions row data (ProverHint.empty FGL)) :
    component.operations.ConstraintsHold env := by
  let proverEnv := proverEnvFromEnvironment env
  have h_env : proverEnv.UsesLocalWitnesses component.rowOffset component.rowOperations := by
    apply usesLocalWitnesses_of_localLength_zero
    change ((component.circuit.main component.rowInputVar).localLength component.rowOffset) = 0
    rw [component.circuit.localLength_eq]
    exact h_localLength
  have h_input' : Eval.eval proverEnv component.rowInputVar = row := by
    unfold Component.rowInputVar at h_input ⊢
    rw [ProvableType.eval_varFromOffset_prover]
    rw [← h_input]
    rw [ProvableType.eval_varFromOffset]
    congr
  have h_assumptions' :
      component.circuit.ProverAssumptions (Eval.eval proverEnv component.rowInputVar)
        proverEnv.data proverEnv.hint := by
    rw [h_input']
    simpa [proverEnv, proverEnvFromEnvironment, h_data] using h_assumptions
  have h_full :=
    component.circuit.original_full_completeness component.rowOffset proverEnv component.rowInputVar
      h_env h_assumptions'
  have h_row : component.rowOperations.ConstraintsHold (proverEnv : Environment FGL) := by
    simpa [Component.rowOperations, Component.rowInputVar, Component.rowOffset] using h_full.1
  simpa [proverEnv, proverEnvFromEnvironment] using
    (Component.constraintsHold_iff (component := component)
      (env := (proverEnv : Environment FGL))).mpr h_row

@[reducible] def mainRowArray (row : MainRowWithRom FGL) : Array FGL :=
  mainRawRow row

def mainSingleRowTable
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    Table FGL where
  component := componentWithRomMemAndOpBus length program
  rawRows := [mainRowArray row]
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    simp [mainRowArray] at h_arr
    subst arr
    simpa [mainRowArray, componentWithRomMemAndOpBus] using mainRawRow_size row
  fixed_domain := by
    intro columns h_columns
    have h_columns' : columns = mainFixedColumns := by
      simpa [componentWithRomMemAndOpBus] using h_columns.symm
    subst columns
    norm_num [mainFixedColumns, mainFixedCapacity]

private theorem mainSingleRowTable_effectiveRows
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    (mainSingleRowTable length program row).table =
      [mainFixedColumns.materialize 0 (mainRawRow row)] := by
  simp [mainSingleRowTable, Table.table, mainRowArray, componentWithRomMemAndOpBus]

def mainSingleRowTableEnvironment
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) : Environment FGL :=
  Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData

theorem mainSingleRowTable_rowInput
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0) :
    (componentWithRomMemAndOpBus length program).rowInput
        (mainSingleRowTableEnvironment length program row) =
      row := by
  change (componentWithRomMemAndOpBus length program).rowInput
      (Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData) = row
  exact componentWithRomMemAndOpBus_rowInput_materialize
    length program 0 emptyData row h_segment_l1 h_main_step

theorem mainSingleRowTable_eval_rowInputVar
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0) :
    Eval.eval (mainSingleRowTableEnvironment length program row)
        (componentWithRomMemAndOpBus length program).rowInputVar =
      row := by
  change Eval.eval
      (Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData)
      (varFromOffset MainRowWithRom 0) = row
  exact eval_mainRawRow_materialize 0 emptyData row h_segment_l1 h_main_step

def mainOpBusInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := OpBusChannel.toRaw
  mult := -row.core.is_external_op
  msg := (toElements (opBusMessage row.core)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

private def mainRowInputVar : Var MainRowWithRom FGL :=
  varFromOffset MainRowWithRom 0

theorem toElements_eval_toArray
    {M : TypeMap} [ProvableType M]
    (env : Environment FGL) (x : M (Expression FGL)) :
    Array.map (fun e => Expression.eval env e) (toElements x).toArray =
      (toElements (eval env x)).toArray := by
  rw [← Vector.toArray_map]
  rw [← ProvableType.toElements_eval]

private theorem eval_mainRowInputVar_fromInput
    (row : MainRowWithRom FGL) :
    eval (Environment.fromInput row emptyData) mainRowInputVar = row := by
  exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData

private theorem eval_mainRowInputVar_core_fromInput
    (row : MainRowWithRom FGL) :
    eval (Environment.fromInput row emptyData) mainRowInputVar.core = row.core := by
  rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
  rw [eval_mainRowInputVar_fromInput]

private theorem eval_mainRowInputVar_is_external_op_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.core.is_external_op =
      row.core.is_external_op := by
  rw [ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op]
  rw [eval_mainRowInputVar_core_fromInput]

theorem mainRowWithRom_eval_rom
    (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    eval env row.rom = (eval env row).rom := by
  cases row
  simp [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go]

theorem mainRomRow_eval_a_src_reg
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.a_src_reg = (eval env row).a_src_reg := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env a_src_reg).symm

theorem mainRomRow_eval_a_src_mem
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.a_src_mem = (eval env row).a_src_mem := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env a_src_mem).symm

theorem mainRomRow_eval_b_src_reg
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.b_src_reg = (eval env row).b_src_reg := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env b_src_reg).symm

theorem mainRomRow_eval_b_src_mem
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.b_src_mem = (eval env row).b_src_mem := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env b_src_mem).symm

theorem mainRomRow_eval_b_src_ind
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.b_src_ind = (eval env row).b_src_ind := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env b_src_ind).symm

theorem mainRomRow_eval_store_reg
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.store_reg = (eval env row).store_reg := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env store_reg).symm

theorem mainRomRow_eval_store_mem
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.store_mem = (eval env row).store_mem := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env store_mem).symm

theorem mainRomRow_eval_store_ind
    (env : Environment FGL) (row : Var MainRomRow FGL) :
    Expression.eval env row.store_ind = (eval env row).store_ind := by
  cases row with
  | mk a_offset_imm0 a_imm1 b_offset_imm0 b_imm1 store_offset a_src_imm a_src_mem
      is_precompiled b_src_imm b_src_mem store_mem store_ind b_src_ind a_src_reg b_src_reg
      store_reg addr0 addr1 addr2 main_step a_reg_prev_mem_step b_reg_prev_mem_step
      store_reg_prev_mem_step store_reg_prev_value_0 store_reg_prev_value_1 =>
      simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
        ProvableStruct.fromComponents, ProvableStruct.components,
        ProvableStruct.toComponents, ProvableStruct.eval.go] using
          (CircuitType.eval_expr env store_ind).symm

private theorem eval_mainRowInputVar_rom_fromInput
    (row : MainRowWithRom FGL) :
    eval (Environment.fromInput row emptyData) mainRowInputVar.rom = row.rom := by
  rw [mainRowWithRom_eval_rom]
  rw [eval_mainRowInputVar_fromInput]

private theorem eval_mainRowInputVar_a_src_reg_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.a_src_reg =
      row.rom.a_src_reg := by
  rw [mainRomRow_eval_a_src_reg]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_a_src_mem_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.a_src_mem =
      row.rom.a_src_mem := by
  rw [mainRomRow_eval_a_src_mem]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_b_src_reg_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.b_src_reg =
      row.rom.b_src_reg := by
  rw [mainRomRow_eval_b_src_reg]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_b_src_mem_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.b_src_mem =
      row.rom.b_src_mem := by
  rw [mainRomRow_eval_b_src_mem]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_b_src_ind_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.b_src_ind =
      row.rom.b_src_ind := by
  rw [mainRomRow_eval_b_src_ind]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_store_reg_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.store_reg =
      row.rom.store_reg := by
  rw [mainRomRow_eval_store_reg]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_store_mem_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.store_mem =
      row.rom.store_mem := by
  rw [mainRomRow_eval_store_mem]
  rw [eval_mainRowInputVar_rom_fromInput]

private theorem eval_mainRowInputVar_store_ind_fromInput
    (row : MainRowWithRom FGL) :
    Expression.eval (Environment.fromInput row emptyData) mainRowInputVar.rom.store_ind =
      row.rom.store_ind := by
  rw [mainRomRow_eval_store_ind]
  rw [eval_mainRowInputVar_rom_fromInput]

def mainOpBusAbstractInteraction : AbstractInteraction FGL :=
  (OpBusChannel.emitted
    (-mainRowInputVar.core.is_external_op)
    (opBusMessageExpr mainRowInputVar.core)).toRaw

theorem mainOpBusAbstractInteraction_eval
    (row : MainRowWithRom FGL) :
    mainOpBusAbstractInteraction.eval (Environment.fromInput row emptyData) =
      mainOpBusInteraction row := by
  simp [mainOpBusAbstractInteraction, mainOpBusInteraction,
    AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · have h_ext :
        Expression.eval (Environment.fromInput row emptyData)
            mainRowInputVar.core.is_external_op =
          row.core.is_external_op := by
      exact eval_mainRowInputVar_is_external_op_fromInput row
    change Expression.eval (Environment.fromInput row emptyData)
        (-mainRowInputVar.core.is_external_op) =
      -row.core.is_external_op
    simp [Expression.eval, h_ext]
  constructor
  · have h_msg_eval :
        eval (Environment.fromInput row emptyData)
            (opBusMessageExpr mainRowInputVar.core) =
          opBusMessage row.core := by
      rw [eval_opBusMessageExpr]
      have h_core :
          (eval (Environment.fromInput row emptyData)
              mainRowInputVar.core : MainRow FGL) =
            row.core := by
        exact eval_mainRowInputVar_core_fromInput row
      rw [h_core]
    simpa [ProvableType.toElements_eval] using
      congrArg (fun msg => (toElements msg).toArray) h_msg_eval
  · rfl

theorem mainComponentOpBusInteraction_eval
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0) :
    (((OpBusChannel.emitted
        (-(componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)
        (opBusMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar.core)).toRaw).eval
      (mainSingleRowTableEnvironment length program row)) =
      mainOpBusInteraction row := by
  let env := mainSingleRowTableEnvironment length program row
  let rowVar := (componentWithRomMemAndOpBus length program).rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact mainSingleRowTable_eval_rowInputVar length program row h_segment_l1 h_main_step
  have h_core : eval env rowVar.core = row.core := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_core]
    exact congrArg MainRowWithRom.core h_input
  have h_field := ZiskFv.AirsClean.FullEnsemble.mainRow_eval_is_external_op env rowVar.core
  simp [mainOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env (-rowVar.core.is_external_op) = -row.core.is_external_op
    simp [Expression.eval, h_field, h_core]
  constructor
  · have h_msg_eval :
        eval env (opBusMessageExpr rowVar.core) = opBusMessage row.core := by
      rw [eval_opBusMessageExpr]
      rw [h_core]
    rw [toElements_eval_toArray]
    change (toElements (eval env (opBusMessageExpr rowVar.core))).toArray =
      (toElements (opBusMessage row.core)).toArray
    rw [h_msg_eval]
  · rfl

theorem mainSingleRowTable_interactionsWith_opBus
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0) :
    (mainSingleRowTable length program row).interactionsWith OpBusChannel.toRaw =
      [mainOpBusInteraction row] := by
  rw [Table.interactionsWith, mainSingleRowTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        OpBusChannel.toRaw (mainSingleRowTableEnvironment length program row) =
      [mainOpBusInteraction row]
  rw [Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  exact congrArg (fun interaction => [interaction])
    (mainComponentOpBusInteraction_eval length program row h_segment_l1 h_main_step)

def mainARegPreInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := row.rom.a_src_reg
  msg := (toElements (aRegPreMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def mainAMemInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := -(row.rom.a_src_mem + row.rom.a_src_reg)
  msg := (toElements (aMemMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def mainBRegPreInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := row.rom.b_src_reg
  msg := (toElements (bRegPreMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def mainBMemInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := -(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg)
  msg := (toElements (bMemMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def mainCRegPreInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := row.rom.store_reg
  msg := (toElements (cRegPreMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def mainCMemInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := -(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg)
  msg := (toElements (cMemMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def mainMemBusInteractions
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    List (Interaction FGL) :=
  let env := mainSingleRowTableEnvironment length program row
  let rowVar := (componentWithRomMemAndOpBus length program).rowInputVar
  [ ((MemBusChannel.emitted rowVar.rom.a_src_reg (aRegPreMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted (-(rowVar.rom.a_src_mem + rowVar.rom.a_src_reg))
      (aMemMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted rowVar.rom.b_src_reg (bRegPreMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted
      (-(rowVar.rom.b_src_mem + rowVar.rom.b_src_ind + rowVar.rom.b_src_reg))
      (bMemMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted rowVar.rom.store_reg (cRegPreMessageExpr rowVar)).toRaw).eval env
  , ((MemBusChannel.emitted
      (-(rowVar.rom.store_mem + rowVar.rom.store_ind + rowVar.rom.store_reg))
      (cMemMessageExpr rowVar)).toRaw).eval env ]

theorem mainSingleRowTable_interactionsWith_memBus
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    (mainSingleRowTable length program row).interactionsWith MemBusChannel.toRaw =
      mainMemBusInteractions length program row := by
  rw [Table.interactionsWith, mainSingleRowTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        MemBusChannel.toRaw (mainSingleRowTableEnvironment length program row) =
      mainMemBusInteractions length program row
  simp [mainMemBusInteractions, Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_memBus]

/-- Evaluating a bus-102 emission: the multiplicity and the carried distance evaluate
    independently, so one lemma serves all three register slots (and every witness). -/
theorem registerStepRange_emitted_eval
    (env : Environment FGL) (multExpr distExpr : Expression FGL) (multVal distVal : FGL)
    (h_mult : Expression.eval env multExpr = multVal)
    (h_dist : Expression.eval env distExpr = distVal) :
    ((ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.emitted multExpr
        (ZiskFv.Channels.SpecifiedRanges.registerStepMessage distExpr)).toRaw).eval env =
      { channel := ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
        mult := multVal
        msg := (toElements
          (ZiskFv.Channels.SpecifiedRanges.registerStepMessage distVal)).toArray
        same_size := by simp [Channel.toRaw]
        assumeGuarantees := false } := by
  simp [AbstractInteraction.eval, ChannelInteraction.toRaw,
    ZiskFv.Channels.SpecifiedRanges.registerStepMessage, toElements_eval_toArray,
    circuit_norm, h_mult, h_dist]

/-- The a-side register-step distance at the value level (`main.pil:333`), with
    `a_mem_step = 1 + main_step * 4`. -/
def aRegStepDistance (row : MainRowWithRom FGL) : FGL :=
  (1 + row.rom.main_step * 4) - row.rom.a_reg_prev_mem_step - 1

/-- The b-side register-step distance (`main.pil:334`). -/
def bRegStepDistance (row : MainRowWithRom FGL) : FGL :=
  (2 + row.rom.main_step * 4) - row.rom.b_reg_prev_mem_step - 1

/-- The store-side register-step distance (`main.pil:335`). -/
def cRegStepDistance (row : MainRowWithRom FGL) : FGL :=
  (3 + row.rom.main_step * 4) - row.rom.store_reg_prev_mem_step - 1

/-- Main's a-side bus-102 pull. The multiplicity is the negated selector, so an inactive
    register slot emits at `0` and contributes nothing to the balance. -/
def mainARegStepInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
  mult := -row.rom.a_src_reg
  msg := (toElements
    (ZiskFv.Channels.SpecifiedRanges.registerStepMessage (aRegStepDistance row))).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

/-- Main's b-side bus-102 pull. -/
def mainBRegStepInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
  mult := -row.rom.b_src_reg
  msg := (toElements
    (ZiskFv.Channels.SpecifiedRanges.registerStepMessage (bRegStepDistance row))).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

/-- Main's store-side bus-102 pull. -/
def mainCRegStepInteraction (row : MainRowWithRom FGL) : Interaction FGL where
  channel := ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
  mult := -row.rom.store_reg
  msg := (toElements
    (ZiskFv.Channels.SpecifiedRanges.registerStepMessage (cRegStepDistance row))).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

/-- Main's three bus-102 pulls under any environment where the row variable evaluates to `row`.
    Row-generic, so the multi-row spin witnesses reuse it per row exactly as they reuse their
    `main*OpBusInteractionsAt` helpers. -/
theorem mainRegisterStepInteractionsAt
    (length : ℕ) (program : Program length) (env : Environment FGL) (row : MainRowWithRom FGL)
    (h_input : eval env (componentWithRomMemAndOpBus length program).rowInputVar = row) :
    (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw env =
      [mainARegStepInteraction row, mainBRegStepInteraction row,
        mainCRegStepInteraction row] := by
  have h_rom :
      eval env (componentWithRomMemAndOpBus length program).rowInputVar.rom = row.rom := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainRowWithRom_eval_rom]
    exact congrArg MainRowWithRom.rom h_input
  obtain ⟨h_a, h_b, h_c, h_step, h_ap, h_bp, h_cp⟩ :=
    ZiskFv.AirsClean.FullEnsemble.mainRomRow_eval_registerStep_fields env
      (componentWithRomMemAndOpBus length program).rowInputVar.rom
  rw [h_rom] at h_a h_b h_c h_step h_ap h_bp h_cp
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_registerStepRange]
  simp only [List.map_cons, List.map_nil]
  have h_ma : Expression.eval env
      (-(componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg)
        = -row.rom.a_src_reg := by
    simp [Expression.eval, h_a]
  have h_mb : Expression.eval env
      (-(componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg)
        = -row.rom.b_src_reg := by
    simp [Expression.eval, h_b]
  have h_mc : Expression.eval env
      (-(componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg)
        = -row.rom.store_reg := by
    simp [Expression.eval, h_c]
  have h_da : Expression.eval env
      (ZiskFv.AirsClean.Main.aRegStepDistanceExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)
        = aRegStepDistance row := by
    simp [aRegStepDistance, circuit_norm, h_step, h_ap]
    ring
  have h_db : Expression.eval env
      (ZiskFv.AirsClean.Main.bRegStepDistanceExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)
        = bRegStepDistance row := by
    simp [bRegStepDistance, circuit_norm, h_step, h_bp]
    ring
  have h_dc : Expression.eval env
      (ZiskFv.AirsClean.Main.cRegStepDistanceExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)
        = cRegStepDistance row := by
    simp [cRegStepDistance, circuit_norm, h_step, h_cp]
    ring
  rw [registerStepRange_emitted_eval (h_mult := h_ma) (h_dist := h_da),
    registerStepRange_emitted_eval (h_mult := h_mb) (h_dist := h_db),
    registerStepRange_emitted_eval (h_mult := h_mc) (h_dist := h_dc)]
  rfl

/-- Main's three bus-102 pulls at a single row, in exposed-channel order. Mirrors
    `mainSingleRowTable_interactionsWith_opBus`: the two fixed-column side conditions are what let
    the row variable evaluate to the concrete row. -/
theorem mainSingleRowTable_interactionsWith_registerStepRange
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0) :
    (mainSingleRowTable length program row).interactionsWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
      [mainARegStepInteraction row, mainBRegStepInteraction row,
        mainCRegStepInteraction row] := by
  rw [Table.interactionsWith, mainSingleRowTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    (componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
        (mainSingleRowTableEnvironment length program row) =
      [mainARegStepInteraction row, mainBRegStepInteraction row, mainCRegStepInteraction row]
  exact mainRegisterStepInteractionsAt length program _ row
    (mainSingleRowTable_eval_rowInputVar length program row h_segment_l1 h_main_step)

theorem mainSingleRowTable_constraints_of_proverAssumptions
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
    (h_segment_l1 : row.core.segment_l1 = mainFixedColumns.fixedAt 0 0)
    (h_main_step : row.rom.main_step = mainFixedColumns.fixedAt 1 0)
    (h_assumptions :
      (componentWithRomMemAndOpBus length program).circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (mainSingleRowTable length program row).Constraints := by
  have h_localLength :
      (componentWithRomMemAndOpBus length program).circuit.localLength
        (componentWithRomMemAndOpBus length program).rowInputVar = 0 := by
    change (mainWithRomMemAndOpBusElaborated length program).localLength
        (componentWithRomMemAndOpBus length program).rowInputVar = 0
    rfl
  have h_component :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold
        (Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData) :=
    component_constraintsHold_of_proverAssumptions_at
      (componentWithRomMemAndOpBus length program)
      (Environment.fromArray (mainFixedColumns.materialize 0 (mainRawRow row)) emptyData)
      row h_localLength (eval_mainRawRow_materialize 0 emptyData row h_segment_l1 h_main_step)
      rfl h_assumptions
  rw [Table.Constraints, mainSingleRowTable_effectiveRows]
  intro arr h_arr
  simp only [List.mem_singleton] at h_arr
  subst arr
  simpa [mainSingleRowTable, Table.environment] using h_component

private def mainSpikeProgram : Program 0 := nofun

private def mainSpikeRow : MainRowWithRom FGL :=
  { core :=
      { a_0 := 11, a_1 := 12, b_0 := 13, b_1 := 14, c_0 := 17, c_1 := 19,
        flag := 1, pc := 100, is_external_op := 1, op := 7, m32 := 1,
        ind_width := 8, set_pc := 0, jmp_offset1 := 4, jmp_offset2 := 4,
        store_pc := 0, im_high_degree_2 := 0, segment_l1 := 1 }
    rom :=
      { a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0, b_imm1 := 0,
        store_offset := 0, a_src_imm := 0, a_src_mem := 0, is_precompiled := 0,
        b_src_imm := 0, b_src_mem := 0, store_mem := 0, store_ind := 0,
        b_src_ind := 0, a_src_reg := 0, b_src_reg := 0, store_reg := 0,
        addr0 := 0, addr1 := 0, addr2 := 0, main_step := 0,
        a_reg_prev_mem_step := 0, b_reg_prev_mem_step := 0,
        store_reg_prev_mem_step := 0, store_reg_prev_value_0 := 0,
        store_reg_prev_value_1 := 0 } }

example :
    ((mainSingleRowTable 0 mainSpikeProgram mainSpikeRow).interactionsWith
        OpBusChannel.toRaw).map (fun i => (i.mult, i.msg)) =
      [((-1 : FGL), #[7, 11, 0, 13, 0, 17, 19, 1, 0, 0, 0])] := by
  rw [mainSingleRowTable_interactionsWith_opBus
    (length := 0) (program := mainSpikeProgram) (row := mainSpikeRow) (by rfl) (by rfl)]
  decide

def binaryAddRowArray (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) : Array FGL :=
  (toElements row).toArray

private theorem registerStepRangeSlice_component_rawWidth :
    ZiskFv.AirsClean.RegisterStepRangeSlice.component.rawWidth = 1 := by
  change ZiskFv.AirsClean.RegisterStepRangeSlice.circuit.size = 1
  rw [GeneralFormalCircuit.size_eq]
  rfl

/-- A bus-102 register-step provider table over concrete distance values.

    Every active Main register slot emits one consumer interaction on bus 102, so a witness whose
    Main rows use register sources must supply one provider row per active slot, carrying that
    slot's `<slot>_mem_step - <slot>_reg_prev_mem_step - 1`. This is the descent data
    `main.pil:333-335` range-checks; before #330 Phase 3 no witness had to exhibit it. -/
def registerStepRangeRowArray (v : FGL) : Array FGL :=
  (toElements (M := field) v).toArray

def registerStepRangeRowsTable (values : List FGL) : Table FGL where
  component := ZiskFv.AirsClean.RegisterStepRangeSlice.component
  rawRows := values.map registerStepRangeRowArray
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    rcases List.mem_map.mp h_arr with ⟨v, _, rfl⟩
    rw [registerStepRangeSlice_component_rawWidth]
    simp [registerStepRangeRowArray, show size field = 1 from rfl]
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.RegisterStepRangeSlice.component] at h_columns

private theorem binaryAdd_component_rawWidth :
    ZiskFv.AirsClean.BinaryAdd.component.rawWidth =
      size ZiskFv.AirsClean.BinaryAdd.BinaryAddRow := by
  change ZiskFv.AirsClean.BinaryAdd.circuit.size = size ZiskFv.AirsClean.BinaryAdd.BinaryAddRow
  rw [GeneralFormalCircuit.size_eq]
  rfl

def binaryAddRowsTable
    (rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)) : Table FGL where
  component := ZiskFv.AirsClean.BinaryAdd.component
  rawRows := rows.map binaryAddRowArray
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    rcases List.mem_map.mp h_arr with ⟨row, _, rfl⟩
    rw [binaryAdd_component_rawWidth]
    simp [binaryAddRowArray]
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.BinaryAdd.component] at h_columns

theorem binaryAddRowsTable_rowInput
    (rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL))
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    ZiskFv.AirsClean.BinaryAdd.component.rowInput
        ((binaryAddRowsTable rows).environment (binaryAddRowArray row)) =
      row := by
  change ZiskFv.AirsClean.BinaryAdd.component.rowInput
      (Environment.fromInput row emptyData) = row
  simp [Air.Flat.Component.rowInput, ProvableType.valueFromOffset_zero_fromInput_eq]

def binaryAddOpBusInteraction (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    Interaction FGL where
  channel := OpBusChannel.toRaw
  mult := 1
  msg := (toElements (ZiskFv.AirsClean.BinaryAdd.opBusMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

theorem binaryAddComponentOpBusInteraction_eval
    (rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL))
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    (((OpBusChannel.pushed
        (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
          ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
      ((binaryAddRowsTable rows).environment (binaryAddRowArray row))) =
      binaryAddOpBusInteraction row := by
  let env := (binaryAddRowsTable rows).environment (binaryAddRowArray row)
  let rowVar := ZiskFv.AirsClean.BinaryAdd.component.rowInputVar
  have h_input : eval env rowVar = row := by
    change eval (Environment.fromInput row emptyData)
        (varFromOffset ZiskFv.AirsClean.BinaryAdd.BinaryAddRow 0) = row
    exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr rowVar) =
        ZiskFv.AirsClean.BinaryAdd.opBusMessage row := by
    rw [ZiskFv.AirsClean.BinaryAdd.eval_opBusMessageExpr]
    rw [h_input]
  simp [binaryAddOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · rfl
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr rowVar))).toArray =
      (toElements (ZiskFv.AirsClean.BinaryAdd.opBusMessage row)).toArray
    rw [h_msg_eval]
  · rfl

theorem binaryAddRowsTable_opBus_row
    (rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL))
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    ZiskFv.AirsClean.BinaryAdd.component.operations.interactionValuesWith
        OpBusChannel.toRaw
        ((binaryAddRowsTable rows).environment (binaryAddRowArray row)) =
      [binaryAddOpBusInteraction row] := by
  simp [binaryAddRowsTable,
    Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus]
  exact binaryAddComponentOpBusInteraction_eval rows row

private theorem binaryAddRowsTable_interactionsWith_opBus_go
    (allRows rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)) :
    (rows.map binaryAddRowArray).flatMap (fun arr =>
        ZiskFv.AirsClean.BinaryAdd.component.operations.interactionValuesWith
          OpBusChannel.toRaw ((binaryAddRowsTable allRows).environment arr)) =
      rows.flatMap fun row => [binaryAddOpBusInteraction row] := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [binaryAddRowsTable_opBus_row, ih]

theorem binaryAddRowsTable_interactionsWith_opBus
    (rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)) :
    (binaryAddRowsTable rows).interactionsWith OpBusChannel.toRaw =
      rows.flatMap fun row => [binaryAddOpBusInteraction row] := by
  change (rows.map binaryAddRowArray).flatMap (fun arr =>
        ZiskFv.AirsClean.BinaryAdd.component.operations.interactionValuesWith
          OpBusChannel.toRaw ((binaryAddRowsTable rows).environment arr)) =
      rows.flatMap fun row => [binaryAddOpBusInteraction row]
  exact binaryAddRowsTable_interactionsWith_opBus_go rows rows

theorem binaryAddRowsTable_constraints_of_proverAssumptions
    (rows : List (ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL))
    (h_assumptions :
      ∀ row ∈ rows,
        ZiskFv.AirsClean.BinaryAdd.component.circuit.ProverAssumptions
          row emptyData (ProverHint.empty FGL)) :
    (binaryAddRowsTable rows).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.BinaryAdd.component.circuit.localLength
        ZiskFv.AirsClean.BinaryAdd.component.rowInputVar = 0 := by
    rfl
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ rows.map binaryAddRowArray at h_arr
  rcases List.mem_map.mp h_arr with ⟨row, h_row, rfl⟩
  have h_component :
      ZiskFv.AirsClean.BinaryAdd.component.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.BinaryAdd.component row h_localLength (h_assumptions row h_row)
  simpa [binaryAddRowsTable, binaryAddRowArray, Table.table, Environment.fromInput]
    using h_component

/-- The bus-102 provider table satisfies its constraints exactly when every supplied distance is
    inside the 24-bit range. The provider owns the static lookup, so this is the only obligation —
    and it is the honest one: a witness cannot invent register-step distances it cannot range-check.

    `ProverAssumptions` for the slice is `rangeTable24.Spec value`, so the hypothesis is stated in
    the same terms the caller can discharge by `decide` on concrete values.

    Stated for an arbitrary `ProverData`: the slice's constraints never read `data`, and the
    witnesses that carry real prover data (SdLd) need exactly that generality. -/
theorem registerStepRangeRowsTableWithData_constraints
    (values : List FGL) (data : ProverData FGL)
    (h_range : ∀ v ∈ values, ZiskFv.AirsClean.RangeTables.rangeTable24.Spec v) :
    { registerStepRangeRowsTable values with data := data }.Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.RegisterStepRangeSlice.component.circuit.localLength
        ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar = 0 := by
    rfl
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ values.map registerStepRangeRowArray at h_arr
  rcases List.mem_map.mp h_arr with ⟨v, h_v, rfl⟩
  refine component_constraintsHold_of_proverAssumptions_at_data
    ZiskFv.AirsClean.RegisterStepRangeSlice.component _ v data h_localLength ?_ ?_
    (h_range v h_v)
  · show eval (Environment.fromArray (registerStepRangeRowArray v) data)
        ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar = v
    exact ProvableType.eval_fromInput_varFromOffset_zero (Input := field) v data
  · rfl

theorem registerStepRangeRowsTable_constraints
    (values : List FGL)
    (h_range : ∀ v ∈ values, ZiskFv.AirsClean.RangeTables.rangeTable24.Spec v) :
    (registerStepRangeRowsTable values).Constraints :=
  registerStepRangeRowsTableWithData_constraints values emptyData h_range

/-- The bus-102 provider table carries interactions on its own channel and nothing else. -/
theorem registerStepRangeRowsTable_interactionsWith_of_ne
    (values : List FGL) (channel : RawChannel FGL)
    (h_ne : channel ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw) :
    (registerStepRangeRowsTable values).interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change channel ∉ [ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw]
  simpa using h_ne

/-- The value-level bus-102 provider push for one distance. -/
def registerStepRangeInteraction (v : FGL) : Interaction FGL where
  channel := ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
  mult := 1
  msg := (toElements (ZiskFv.Channels.SpecifiedRanges.registerStepMessage v)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

/-- Evaluating the provider's abstract push under a row's environment gives that row's concrete
    push. Mirrors `binaryAddComponentOpBusInteraction_eval`; the named `registerStepRangeRowArray`
    wrapper is what lets the `change` below see the environment in `Environment.fromInput` form. -/
theorem registerStepRangeComponentInteraction_eval
    (values : List FGL) (data : ProverData FGL) (v : FGL) :
    (((ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.pushed
        (ZiskFv.Channels.SpecifiedRanges.registerStepMessage
          ZiskFv.AirsClean.RegisterStepRangeSlice.component.rowInputVar)).toRaw).eval
      ({ registerStepRangeRowsTable values with data := data }.environment
        (registerStepRangeRowArray v))) =
      registerStepRangeInteraction v := by
  simp [registerStepRangeInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw,
    ZiskFv.Channels.SpecifiedRanges.registerStepMessage, toElements_eval_toArray,
    circuit_norm, Table.environment, registerStepRangeRowsTable, registerStepRangeRowArray,
    Component.rowInputVar, Component.rowOffset,
    ZiskFv.AirsClean.RegisterStepRangeSlice.component]

/-- The bus-102 provider emits exactly one push per row, carrying that row's value. -/
theorem registerStepRangeRowsTable_row
    (values : List FGL) (data : ProverData FGL) (v : FGL) :
    ZiskFv.AirsClean.RegisterStepRangeSlice.component.operations.interactionValuesWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
        ({ registerStepRangeRowsTable values with data := data }.environment
          (registerStepRangeRowArray v)) =
      [registerStepRangeInteraction v] := by
  simp [registerStepRangeRowsTable, Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.RegisterStepRangeSlice.component_interactionsWith_rangeChannel]
  exact registerStepRangeComponentInteraction_eval values data v

private theorem registerStepRangeRowsTable_interactionsWith_go
    (allValues values : List FGL) (data : ProverData FGL) :
    (values.map registerStepRangeRowArray).flatMap (fun arr =>
        ZiskFv.AirsClean.RegisterStepRangeSlice.component.operations.interactionValuesWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw
          ({ registerStepRangeRowsTable allValues with data := data }.environment arr)) =
      values.map registerStepRangeInteraction := by
  induction values with
  | nil => rfl
  | cons v rest ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      rw [registerStepRangeRowsTable_row allValues data v]
      rfl

/-- The bus-102 provider table's interaction list: one push per supplied distance. -/
theorem registerStepRangeRowsTableWithData_interactionsWith
    (values : List FGL) (data : ProverData FGL) :
    { registerStepRangeRowsTable values with data := data }.interactionsWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
      values.map registerStepRangeInteraction := by
  rw [Table.interactionsWith]
  simpa [registerStepRangeRowsTable, Table.table] using
    registerStepRangeRowsTable_interactionsWith_go values values data

theorem registerStepRangeRowsTable_interactionsWith
    (values : List FGL) :
    (registerStepRangeRowsTable values).interactionsWith
        ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw =
      values.map registerStepRangeInteraction :=
  registerStepRangeRowsTableWithData_interactionsWith values emptyData


/-- Any channel whose name is not the bus-102 slice's is a different channel. The five
    corollaries below are what every witness needs to show the provider table is silent on the
    other buses; they live here rather than per-witness so the seven witnesses share one copy. -/
theorem registerStepRange_ne (c : RawChannel FGL)
    (h_name : c.name ≠ "SpecifiedRangesSlice102") :
    c ≠ ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
  intro h
  exact h_name (by rw [h]; rfl)

theorem registerStepRangeRowsTable_interactionsWith_rangeChannel_nil (values : List FGL) :
    (registerStepRangeRowsTable values).interactionsWith
      ZiskFv.Channels.SpecifiedRanges.SpecifiedRangesSliceChannel.toRaw = [] :=
  registerStepRangeRowsTable_interactionsWith_of_ne values _
    (registerStepRange_ne _ (by decide))

theorem registerStepRangeRowsTable_interactionsWith_memAlignRangeChannel_nil
    (values : List FGL) :
    (registerStepRangeRowsTable values).interactionsWith
      ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw = [] :=
  registerStepRangeRowsTable_interactionsWith_of_ne values _
    (registerStepRange_ne _ (by decide))

theorem registerStepRangeRowsTable_interactionsWith_memBus_nil (values : List FGL) :
    (registerStepRangeRowsTable values).interactionsWith MemBusChannel.toRaw = [] :=
  registerStepRangeRowsTable_interactionsWith_of_ne values _
    (registerStepRange_ne _ (by decide))

theorem registerStepRangeRowsTable_interactionsWith_memAlignRomChannel_nil
    (values : List FGL) :
    (registerStepRangeRowsTable values).interactionsWith
      ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.toRaw = [] :=
  registerStepRangeRowsTable_interactionsWith_of_ne values _
    (registerStepRange_ne _ (by decide))

theorem registerStepRangeRowsTable_interactionsWith_opBus_nil (values : List FGL) :
    (registerStepRangeRowsTable values).interactionsWith OpBusChannel.toRaw = [] :=
  registerStepRangeRowsTable_interactionsWith_of_ne values _
    (registerStepRange_ne _ (by decide))

def binaryExtensionRowArray
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL) : Array FGL :=
  (toElements row).toArray

private theorem binaryExtensionShiftStatic_component_rawWidth :
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rawWidth =
      size ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow := by
  change ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupCircuit.size =
    size ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow
  rw [GeneralFormalCircuit.size_eq]
  rfl

def binaryExtensionShiftStaticRowsTable
    (rows : List (ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)) : Table FGL where
  component := ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent
  rawRows := rows.map binaryExtensionRowArray
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    rcases List.mem_map.mp h_arr with ⟨row, _, rfl⟩
    rw [binaryExtensionShiftStatic_component_rawWidth]
    simp [binaryExtensionRowArray]
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent] at h_columns

theorem binaryExtensionShiftStaticRowsTable_constraints_of_proverAssumptions
    (rows : List (ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL))
    (h_assumptions :
      ∀ row ∈ rows,
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.circuit.ProverAssumptions
          row emptyData (ProverHint.empty FGL)) :
    (binaryExtensionShiftStaticRowsTable rows).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.circuit.localLength
        ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInputVar = 0 := by
    rfl
  rw [Table.Constraints]
  intro arr h_arr
  change arr ∈ rows.map binaryExtensionRowArray at h_arr
  rcases List.mem_map.mp h_arr with ⟨row, h_row, rfl⟩
  have h_component :
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent row h_localLength
      (h_assumptions row h_row)
  simpa [binaryExtensionShiftStaticRowsTable, binaryExtensionRowArray, Table.table,
    Environment.fromInput] using h_component

def binaryRowArray (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) : Array FGL :=
  (toElements row).toArray

private theorem binaryStaticLookup_component_rawWidth :
    ZiskFv.AirsClean.Binary.staticLookupComponent.rawWidth =
      size ZiskFv.AirsClean.Binary.BinaryRow := by
  change ZiskFv.AirsClean.Binary.staticLookupCircuit.size =
    size ZiskFv.AirsClean.Binary.BinaryRow
  rw [GeneralFormalCircuit.size_eq]
  rfl

def binarySingleRowTable (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) : Table FGL where
  component := ZiskFv.AirsClean.Binary.staticLookupComponent
  rawRows := [binaryRowArray row]
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    simp [binaryRowArray] at h_arr
    subst arr
    rw [binaryStaticLookup_component_rawWidth]
    simp [binaryRowArray]
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.Binary.staticLookupComponent] at h_columns

private theorem binarySingleRowTable_effectiveRows
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) :
    (binarySingleRowTable row).table = [binaryRowArray row] := by
  simp [binarySingleRowTable, Table.table, binaryRowArray,
    ZiskFv.AirsClean.Binary.staticLookupComponent]

theorem binarySingleRowTable_rowInput
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) :
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        ((binarySingleRowTable row).environment (binaryRowArray row)) =
      row := by
  change ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (Environment.fromInput row emptyData) = row
  simp [Air.Flat.Component.rowInput, ProvableType.valueFromOffset_zero_fromInput_eq]

def binaryOpBusInteraction (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) :
    Interaction FGL where
  channel := OpBusChannel.toRaw
  mult := 1
  msg := (toElements (ZiskFv.AirsClean.Binary.opBusMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

theorem binaryComponentOpBusInteraction_eval
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) :
    (((OpBusChannel.pushed
        (ZiskFv.AirsClean.Binary.opBusMessageExpr
          ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
      ((binarySingleRowTable row).environment (binaryRowArray row))) =
      binaryOpBusInteraction row := by
  let env := (binarySingleRowTable row).environment (binaryRowArray row)
  let rowVar := ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar
  have h_input : eval env rowVar = row := by
    change eval (Environment.fromInput row emptyData)
        (varFromOffset ZiskFv.AirsClean.Binary.BinaryRow 0) = row
    exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.Binary.opBusMessageExpr rowVar) =
        ZiskFv.AirsClean.Binary.opBusMessage row := by
    rw [ZiskFv.AirsClean.Binary.eval_opBusMessageExpr]
    rw [h_input]
  simp [binaryOpBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · rfl
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.Binary.opBusMessageExpr rowVar))).toArray =
      (toElements (ZiskFv.AirsClean.Binary.opBusMessage row)).toArray
    rw [h_msg_eval]
  · rfl

theorem binarySingleRowTable_interactionsWith_opBus
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) :
    (binarySingleRowTable row).interactionsWith OpBusChannel.toRaw =
      [binaryOpBusInteraction row] := by
  rw [Table.interactionsWith, binarySingleRowTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    ZiskFv.AirsClean.Binary.staticLookupComponent.operations.interactionValuesWith
        OpBusChannel.toRaw
        ((binarySingleRowTable row).environment (binaryRowArray row)) =
      [binaryOpBusInteraction row]
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Binary.staticLookupComponent_interactionsWith_opBus]
  exact congrArg (fun interaction => [interaction]) (binaryComponentOpBusInteraction_eval row)

theorem binarySingleRowTable_constraints_of_proverAssumptions
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_assumptions :
      ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (binarySingleRowTable row).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.localLength
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar = 0 := by
    rfl
  have h_component :
      ZiskFv.AirsClean.Binary.staticLookupComponent.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.Binary.staticLookupComponent row h_localLength h_assumptions
  rw [Table.Constraints, binarySingleRowTable_effectiveRows]
  intro arr h_arr
  simp only [List.mem_singleton] at h_arr
  subst arr
  simpa [binarySingleRowTable, binaryRowArray, Table.environment, Environment.fromInput]
    using h_component

private def binarySpikeRow : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  { aBytes :=
      { free_in_a_0 := 2, free_in_a_1 := 0, free_in_a_2 := 0, free_in_a_3 := 0,
        free_in_a_4 := 0, free_in_a_5 := 0, free_in_a_6 := 0, free_in_a_7 := 0 }
    bBytes :=
      { free_in_b_0 := 3, free_in_b_1 := 0, free_in_b_2 := 0, free_in_b_3 := 0,
        free_in_b_4 := 0, free_in_b_5 := 0, free_in_b_6 := 0, free_in_b_7 := 0 }
    cBytes :=
      { free_in_c_0 := 5, free_in_c_1 := 0, free_in_c_2 := 0, free_in_c_3 := 0,
        free_in_c_4 := 0, free_in_c_5 := 0, free_in_c_6 := 0, free_in_c_7 := 0 }
    chain :=
      { carry_0 := 0, carry_1 := 0, carry_2 := 0, carry_3 := 0,
        carry_4 := 0, carry_5 := 0, carry_6 := 0, carry_7 := 1,
        b_op := 7, b_op_or_sext := 7 }
    mode :=
      { mode32 := 1, result_is_a := 0, use_first_byte := 0, c_is_signed := 0,
        mode32_and_c_is_signed := 0 } }

example :
    ((binarySingleRowTable binarySpikeRow).interactionsWith OpBusChannel.toRaw).map
        (fun i => (i.mult, i.msg)) =
      [((1 : FGL), #[23, 2, 0, 3, 0, 6, 0, 1, 0, 0, 0])] := by
  rw [binarySingleRowTable_interactionsWith_opBus]
  decide

private theorem memRow_eval_sel
    (env : Environment FGL) (row : Var ZiskFv.AirsClean.Mem.MemRow FGL) :
    Expression.eval env row.sel = (eval env row).sel := by
  cases row with
  | mk addr step sel addr_changes step_dual sel_dual value_0 value_1 wr previous_step
      increment_0 increment_1 read_same_addr =>
    simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go] using
      (CircuitType.eval_expr env sel).symm

private theorem memRow_eval_sel_dual
    (env : Environment FGL) (row : Var ZiskFv.AirsClean.Mem.MemRow FGL) :
    Expression.eval env row.sel_dual = (eval env row).sel_dual := by
  cases row with
  | mk addr step sel addr_changes step_dual sel_dual value_0 value_1 wr previous_step
      increment_0 increment_1 read_same_addr =>
    simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go] using
      (CircuitType.eval_expr env sel_dual).symm

@[reducible] def memRowArray (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Array FGL :=
  ZiskFv.AirsClean.Mem.memRawRow row

def memSingleRowTable (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Table FGL where
  component := ZiskFv.AirsClean.Mem.componentWithDualMemBus
  rawRows := [memRowArray row]
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    simp [memRowArray] at h_arr
    subst arr
    simpa [memRowArray, ZiskFv.AirsClean.Mem.componentWithDualMemBus] using
      ZiskFv.AirsClean.Mem.memRawRow_size row
  fixed_domain := by
    intro columns h_columns
    have h_columns' : columns = ZiskFv.AirsClean.Mem.memFixedColumns := by
      simpa [ZiskFv.AirsClean.Mem.componentWithDualMemBus] using h_columns.symm
    subst columns
    norm_num [ZiskFv.AirsClean.Mem.memFixedColumns, ZiskFv.AirsClean.Mem.memFixedCapacity]

/-- A bounded sequence of concrete Mem rows with the component's canonical
    prover-data-backed range cells materialized into every raw row. -/
def memRowsTable
    (data : ProverData FGL) (rows : List (ZiskFv.AirsClean.Mem.MemRow FGL))
    (h_capacity : rows.length ≤ ZiskFv.AirsClean.Mem.memFixedCapacity) : Table FGL where
  component := ZiskFv.AirsClean.Mem.componentWithDualMemBus
  rawRows := rows.map (ZiskFv.AirsClean.Mem.memRawRowWithProverData data)
  data := data
  raw_uniform_width := by
    intro raw h_raw
    simp only [List.mem_map] at h_raw
    obtain ⟨row, _, rfl⟩ := h_raw
    simp [ZiskFv.AirsClean.Mem.componentWithDualMemBus,
      ZiskFv.AirsClean.Mem.memRawRowWithProverData]
  fixed_domain := by
    intro columns h_columns
    have h_columns' : columns = ZiskFv.AirsClean.Mem.memFixedColumns := by
      simpa [ZiskFv.AirsClean.Mem.componentWithDualMemBus] using h_columns.symm
    subst columns
    change (rows.map (ZiskFv.AirsClean.Mem.memRawRowWithProverData data)).length ≤
      ZiskFv.AirsClean.Mem.memFixedCapacity
    simpa using h_capacity

/-- The named Mem input decoded from a prover-data-materialized raw row is its
    original thirteen-field witness row. -/
theorem memRowsTable_rowInput
    (index : Nat) (data : ProverData FGL) (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInput
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize index
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData data row)) data) = row := by
  simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar,
    eval_varFromOffset_valueFromOffset] using
    ZiskFv.AirsClean.Mem.eval_memRawRowWithProverData_materialize index data row

/-- Row-local Mem constraints for a bounded concrete table follow from each
    row's honest completeness witness, using the same shared prover data as
    the table's source-linked range cells. -/
theorem memRowsTable_constraints_of_proverAssumptions
    (data : ProverData FGL) (rows : List (ZiskFv.AirsClean.Mem.MemRow FGL))
    (h_capacity : rows.length ≤ ZiskFv.AirsClean.Mem.memFixedCapacity)
    (h_assumptions : ∀ index : Fin rows.length,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.ProverAssumptions
        (rows.get index) data (ProverHint.empty FGL)) :
    (memRowsTable data rows h_capacity).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.localLength
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar = 0 := by
    change ZiskFv.AirsClean.Mem.memWithDualMemBusElaborated.localLength
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar = 0
    rfl
  rw [Table.Constraints]
  change ∀ arr ∈ List.mapIdx (fun index raw =>
      ZiskFv.AirsClean.Mem.memFixedColumns.materialize index raw)
      (rows.map (ZiskFv.AirsClean.Mem.memRawRowWithProverData data)),
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.ConstraintsHold
      (Environment.fromArray arr data)
  intro arr h_arr
  obtain ⟨index, h_arr⟩ := List.mem_iff_get.mp h_arr
  let rowsIndex : Fin rows.length := ⟨index.val, by simpa using index.isLt⟩
  have h_effective :
      (List.mapIdx (fun index raw =>
        ZiskFv.AirsClean.Mem.memFixedColumns.materialize index raw)
        (rows.map (ZiskFv.AirsClean.Mem.memRawRowWithProverData data))).get index =
        ZiskFv.AirsClean.Mem.memFixedColumns.materialize rowsIndex.val
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData data (rows.get rowsIndex)) := by
    simpa [List.mapIdx_eq_ofFn, rowsIndex]
  rw [h_effective] at h_arr
  subst arr
  exact component_constraintsHold_of_proverAssumptions_at_data
    ZiskFv.AirsClean.Mem.componentWithDualMemBus
    (Environment.fromArray
      (ZiskFv.AirsClean.Mem.memFixedColumns.materialize rowsIndex.val
        (ZiskFv.AirsClean.Mem.memRawRowWithProverData data (rows.get rowsIndex))) data)
    (rows.get rowsIndex) data h_localLength
    (ZiskFv.AirsClean.Mem.eval_memRawRowWithProverData_materialize rowsIndex.val data
      (rows.get rowsIndex)) rfl (h_assumptions rowsIndex)

private theorem memSingleRowTable_effectiveRows
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (memSingleRowTable row).table =
      [ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
        (ZiskFv.AirsClean.Mem.memRawRow row)] := by
  simp [memSingleRowTable, Table.table, memRowArray,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus]

def memSingleRowTableEnvironment
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Environment FGL :=
  Environment.fromArray
    (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
      (ZiskFv.AirsClean.Mem.memRawRow row)) emptyData

theorem memSingleRowTable_rowInput
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInput
        (memSingleRowTableEnvironment row) =
      row := by
  change ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInput
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
          (ZiskFv.AirsClean.Mem.memRawRow row)) emptyData) = row
  exact ZiskFv.AirsClean.Mem.componentWithDualMemBus_rowInput_materialize 0 emptyData row

def memBusInteraction (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := row.sel
  msg := (toElements (ZiskFv.AirsClean.Mem.memBusMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def memBusDualInteraction (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := row.sel_dual
  msg := (toElements (ZiskFv.AirsClean.Mem.memBusDualMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

private theorem memComponentMemBusInteraction_eval_at
    (index : Nat) (data : ProverData FGL) (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (((MemBusChannel.emitted
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
        (ZiskFv.AirsClean.Mem.memBusMessageExpr
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize index
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData data row)) data)) =
      memBusInteraction row := by
  let env := Environment.fromArray
    (ZiskFv.AirsClean.Mem.memFixedColumns.materialize index
      (ZiskFv.AirsClean.Mem.memRawRowWithProverData data row)) data
  let rowVar := ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ZiskFv.AirsClean.Mem.eval_memRawRowWithProverData_materialize index data row
  have h_field := memRow_eval_sel env rowVar
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.Mem.memBusMessageExpr rowVar) =
        ZiskFv.AirsClean.Mem.memBusMessage row := by
    rw [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr]
    rw [h_input]
  simp [memBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env rowVar.sel = row.sel
    rw [h_field, h_input]
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.Mem.memBusMessageExpr rowVar))).toArray =
      (toElements (ZiskFv.AirsClean.Mem.memBusMessage row)).toArray
    rw [h_msg_eval]
  · rfl

private theorem memComponentMemBusDualInteraction_eval_at
    (index : Nat) (data : ProverData FGL) (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (((MemBusChannel.emitted
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
        (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize index
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData data row)) data)) =
      memBusDualInteraction row := by
  let env := Environment.fromArray
    (ZiskFv.AirsClean.Mem.memFixedColumns.materialize index
      (ZiskFv.AirsClean.Mem.memRawRowWithProverData data row)) data
  let rowVar := ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ZiskFv.AirsClean.Mem.eval_memRawRowWithProverData_materialize index data row
  have h_field := memRow_eval_sel_dual env rowVar
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.Mem.memBusDualMessageExpr rowVar) =
        ZiskFv.AirsClean.Mem.memBusDualMessage row := by
    rw [ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr]
    rw [h_input]
  simp [memBusDualInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env rowVar.sel_dual = row.sel_dual
    rw [h_field, h_input]
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.Mem.memBusDualMessageExpr rowVar))).toArray =
      (toElements (ZiskFv.AirsClean.Mem.memBusDualMessage row)).toArray
    rw [h_msg_eval]
  · rfl

private theorem memRowsTable_memBus_row
    (index : Nat) (data : ProverData FGL) (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.interactionValuesWith
        MemBusChannel.toRaw
        (Environment.fromArray
          (ZiskFv.AirsClean.Mem.memFixedColumns.materialize index
            (ZiskFv.AirsClean.Mem.memRawRowWithProverData data row)) data) =
      [memBusInteraction row, memBusDualInteraction row] := by
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus]
  simp only [List.map_cons, List.map_nil]
  exact congrArg₂ (fun primary dual => [primary, dual])
    (memComponentMemBusInteraction_eval_at index data row)
    (memComponentMemBusDualInteraction_eval_at index data row)

private theorem memRowsTable_interactionsWith_memBus_go
    (data : ProverData FGL) :
    ∀ (offset : Nat) (rows : List (ZiskFv.AirsClean.Mem.MemRow FGL)),
      (List.mapIdx (fun index raw =>
        ZiskFv.AirsClean.Mem.memFixedColumns.materialize (offset + index) raw)
        (rows.map (ZiskFv.AirsClean.Mem.memRawRowWithProverData data))).flatMap (fun arr =>
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.interactionValuesWith
            MemBusChannel.toRaw (Environment.fromArray arr data)) =
        rows.flatMap fun row => [memBusInteraction row, memBusDualInteraction row] := by
  intro offset rows
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.mapIdx_cons, List.flatMap_cons]
      rw [memRowsTable_memBus_row]
      have h_indexed :
          (fun index raw => ZiskFv.AirsClean.Mem.memFixedColumns.materialize
              (offset + (index + 1)) raw) =
            (fun index raw => ZiskFv.AirsClean.Mem.memFixedColumns.materialize
              ((offset + 1) + index) raw) := by
        funext index raw
        congr 1
        omega
      rw [h_indexed]
      exact congrArg (fun tail => [memBusInteraction row, memBusDualInteraction row] ++ tail)
        (ih (offset := offset + 1))

theorem memRowsTable_interactionsWith_memBus
    (data : ProverData FGL) (rows : List (ZiskFv.AirsClean.Mem.MemRow FGL))
    (h_capacity : rows.length ≤ ZiskFv.AirsClean.Mem.memFixedCapacity) :
    (memRowsTable data rows h_capacity).interactionsWith MemBusChannel.toRaw =
      rows.flatMap fun row => [memBusInteraction row, memBusDualInteraction row] := by
  change
    (List.mapIdx (fun index raw =>
      ZiskFv.AirsClean.Mem.memFixedColumns.materialize index raw)
      (rows.map (ZiskFv.AirsClean.Mem.memRawRowWithProverData data))).flatMap (fun arr =>
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.interactionValuesWith
          MemBusChannel.toRaw (Environment.fromArray arr data)) =
      rows.flatMap fun row => [memBusInteraction row, memBusDualInteraction row]
  simpa using memRowsTable_interactionsWith_memBus_go data 0 rows

theorem memComponentMemBusInteraction_eval
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (((MemBusChannel.emitted
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
        (ZiskFv.AirsClean.Mem.memBusMessageExpr
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
      (memSingleRowTableEnvironment row)) =
      memBusInteraction row := by
  let env := memSingleRowTableEnvironment row
  let rowVar := ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ZiskFv.AirsClean.Mem.eval_memRawRow_materialize 0 emptyData row
  have h_field := memRow_eval_sel env rowVar
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.Mem.memBusMessageExpr rowVar) =
        ZiskFv.AirsClean.Mem.memBusMessage row := by
    rw [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr]
    rw [h_input]
  simp [memBusInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env rowVar.sel = row.sel
    rw [h_field, h_input]
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.Mem.memBusMessageExpr rowVar))).toArray =
      (toElements (ZiskFv.AirsClean.Mem.memBusMessage row)).toArray
    rw [h_msg_eval]
  · rfl

theorem memComponentMemBusDualInteraction_eval
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (((MemBusChannel.emitted
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
        (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
      (memSingleRowTableEnvironment row)) =
      memBusDualInteraction row := by
  let env := memSingleRowTableEnvironment row
  let rowVar := ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ZiskFv.AirsClean.Mem.eval_memRawRow_materialize 0 emptyData row
  have h_field := memRow_eval_sel_dual env rowVar
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.Mem.memBusDualMessageExpr rowVar) =
        ZiskFv.AirsClean.Mem.memBusDualMessage row := by
    rw [ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr]
    rw [h_input]
  simp [memBusDualInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · change Expression.eval env rowVar.sel_dual = row.sel_dual
    rw [h_field, h_input]
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.Mem.memBusDualMessageExpr rowVar))).toArray =
      (toElements (ZiskFv.AirsClean.Mem.memBusDualMessage row)).toArray
    rw [h_msg_eval]
  · rfl

theorem memSingleRowTable_interactionsWith_memBus
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (memSingleRowTable row).interactionsWith MemBusChannel.toRaw =
      [memBusInteraction row, memBusDualInteraction row] := by
  rw [Table.interactionsWith, memSingleRowTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.interactionValuesWith
        MemBusChannel.toRaw (memSingleRowTableEnvironment row) =
      [memBusInteraction row, memBusDualInteraction row]
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus]
  simp only [List.map_cons, List.map_nil]
  exact congrArg₂ (fun primary dual => [primary, dual])
    (memComponentMemBusInteraction_eval row) (memComponentMemBusDualInteraction_eval row)

theorem memSingleRowTable_constraints_of_proverAssumptions
    (row : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_assumptions :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (memSingleRowTable row).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.localLength
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar = 0 := by
    change ZiskFv.AirsClean.Mem.memWithDualMemBusElaborated.localLength
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar = 0
    rfl
  have h_component :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.operations.ConstraintsHold
        (Environment.fromArray
          (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
            (ZiskFv.AirsClean.Mem.memRawRow row)) emptyData) :=
    component_constraintsHold_of_proverAssumptions_at
      ZiskFv.AirsClean.Mem.componentWithDualMemBus
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
          (ZiskFv.AirsClean.Mem.memRawRow row)) emptyData)
      row h_localLength (ZiskFv.AirsClean.Mem.eval_memRawRow_materialize 0 emptyData row)
      rfl h_assumptions
  rw [Table.Constraints, memSingleRowTable_effectiveRows]
  intro arr h_arr
  simp only [List.mem_singleton] at h_arr
  subst arr
  simpa [memSingleRowTable, memRowArray, Table.environment] using h_component

private def memSpikeRow : ZiskFv.AirsClean.Mem.MemRow FGL :=
  { addr := 4, step := 7, sel := 1, addr_changes := 0, step_dual := 8,
    sel_dual := 1, value_0 := 9, value_1 := 10, wr := 0,
    previous_step := 0, increment_0 := 0, increment_1 := 0, read_same_addr := 1 }

example :
    ((memSingleRowTable memSpikeRow).interactionsWith MemBusChannel.toRaw).map
        (fun i => (i.mult, i.msg)) =
      [ ((1 : FGL), #[1, 32, 7, 8, 9, 10])
      , ((1 : FGL), #[1, 32, 8, 8, 9, 10]) ] := by
  rw [memSingleRowTable_interactionsWith_memBus]
  decide

def registerBoundaryRowArray (row : RegisterBoundaryRow FGL) : Array FGL :=
  (toElements row).toArray

def registerBoundaryRowsTableOf (rows : List (RegisterBoundaryRow FGL)) : Table FGL where
  component := ZiskFv.AirsClean.RegisterBoundary.component
  rawRows := rows.map registerBoundaryRowArray
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    simp [registerBoundaryRowArray] at h_arr
    rcases h_arr with ⟨row, _h_row, rfl⟩
    change size RegisterBoundaryRow = ZiskFv.AirsClean.RegisterBoundary.circuit.size
    rw [GeneralFormalCircuit.size_eq]
    rfl
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.RegisterBoundary.component] at h_columns

private theorem registerBoundaryRowsTableOf_effectiveRows
    (rows : List (RegisterBoundaryRow FGL)) :
    (registerBoundaryRowsTableOf rows).table = rows.map registerBoundaryRowArray := by
  simp [registerBoundaryRowsTableOf, Table.table, registerBoundaryRowArray,
    ZiskFv.AirsClean.RegisterBoundary.component]

def registerBoundarySingleRowTable (row : RegisterBoundaryRow FGL) : Table FGL where
  component := ZiskFv.AirsClean.RegisterBoundary.component
  rawRows := [registerBoundaryRowArray row]
  data := emptyData
  raw_uniform_width := by
    intro arr h_arr
    simp [registerBoundaryRowArray] at h_arr
    subst arr
    change size RegisterBoundaryRow = ZiskFv.AirsClean.RegisterBoundary.circuit.size
    rw [GeneralFormalCircuit.size_eq]
    rfl
  fixed_domain := by
    intro columns h_columns
    simp [ZiskFv.AirsClean.RegisterBoundary.component] at h_columns

private theorem registerBoundarySingleRowTable_effectiveRows
    (row : RegisterBoundaryRow FGL) :
    (registerBoundarySingleRowTable row).table = [registerBoundaryRowArray row] := by
  simp [registerBoundarySingleRowTable, Table.table, registerBoundaryRowArray,
    ZiskFv.AirsClean.RegisterBoundary.component]

theorem registerBoundarySingleRowTable_rowInput
    (row : RegisterBoundaryRow FGL) :
    ZiskFv.AirsClean.RegisterBoundary.component.rowInput
        ((registerBoundarySingleRowTable row).environment (registerBoundaryRowArray row)) =
      row := by
  change ZiskFv.AirsClean.RegisterBoundary.component.rowInput
      (Environment.fromInput row emptyData) = row
  simp [Air.Flat.Component.rowInput, ProvableType.valueFromOffset_zero_fromInput_eq]

def registerBoundaryBootInteraction (row : RegisterBoundaryRow FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := -1
  msg := (toElements (bootMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def registerBoundaryReloadInteraction (row : RegisterBoundaryRow FGL) : Interaction FGL where
  channel := MemBusChannel.toRaw
  mult := 1
  msg := (toElements (reloadMessage row)).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

def registerBoundaryMemBusInteractions (row : RegisterBoundaryRow FGL) : List (Interaction FGL) :=
  [registerBoundaryBootInteraction row, registerBoundaryReloadInteraction row]

theorem registerBoundaryBootInteraction_eval_fromInput
    (row : RegisterBoundaryRow FGL) (data : ProverData FGL := emptyData) :
    (((MemBusChannel.emitted (-1)
        (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
      (Environment.fromInput row data)) =
      registerBoundaryBootInteraction row := by
  let env := Environment.fromInput row data
  let rowVar := ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ProvableType.eval_fromInput_varFromOffset_zero row data
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr rowVar) = bootMessage row := by
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_bootMessageExpr, h_input]
  simp [registerBoundaryBootInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · rfl
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr rowVar))).toArray =
      (toElements (bootMessage row)).toArray
    rw [h_msg_eval]
  · rfl

theorem registerBoundaryReloadInteraction_eval_fromInput
    (row : RegisterBoundaryRow FGL) (data : ProverData FGL := emptyData) :
    (((MemBusChannel.emitted 1
        (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
      (Environment.fromInput row data)) =
      registerBoundaryReloadInteraction row := by
  let env := Environment.fromInput row data
  let rowVar := ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ProvableType.eval_fromInput_varFromOffset_zero row data
  have h_msg_eval :
      eval env (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr rowVar) =
        reloadMessage row := by
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_reloadMessageExpr, h_input]
  simp [registerBoundaryReloadInteraction, AbstractInteraction.eval, ChannelInteraction.toRaw]
  constructor
  · rfl
  constructor
  · rw [toElements_eval_toArray]
    change (toElements
        (eval env (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr rowVar))).toArray =
      (toElements (reloadMessage row)).toArray
    rw [h_msg_eval]
  · rfl

theorem registerBoundaryComponentBootInteraction_eval
    (row : RegisterBoundaryRow FGL) :
    (((MemBusChannel.emitted (-1)
        (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
      ((registerBoundarySingleRowTable row).environment (registerBoundaryRowArray row))) =
      registerBoundaryBootInteraction row := by
  simpa [registerBoundarySingleRowTable, registerBoundaryRowArray, Table.environment,
    Environment.fromInput] using registerBoundaryBootInteraction_eval_fromInput row

theorem registerBoundaryComponentReloadInteraction_eval
    (row : RegisterBoundaryRow FGL) :
    (((MemBusChannel.emitted 1
        (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
      ((registerBoundarySingleRowTable row).environment (registerBoundaryRowArray row))) =
      registerBoundaryReloadInteraction row := by
  simpa [registerBoundarySingleRowTable, registerBoundaryRowArray, Table.environment,
    Environment.fromInput] using registerBoundaryReloadInteraction_eval_fromInput row

theorem registerBoundarySingleRowTable_interactionsWith_memBus
    (row : RegisterBoundaryRow FGL) :
    (registerBoundarySingleRowTable row).interactionsWith MemBusChannel.toRaw =
      registerBoundaryMemBusInteractions row := by
  rw [Table.interactionsWith, registerBoundarySingleRowTable_effectiveRows]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change
    ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
        MemBusChannel.toRaw
        ((registerBoundarySingleRowTable row).environment (registerBoundaryRowArray row)) =
      registerBoundaryMemBusInteractions row
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.RegisterBoundary.component_interactionsWith_memBus]
  simp only [registerBoundaryMemBusInteractions, List.map_cons, List.map_nil]
  exact congrArg₂ (fun boot reload => [boot, reload])
    (registerBoundaryComponentBootInteraction_eval row)
    (registerBoundaryComponentReloadInteraction_eval row)

private theorem registerBoundaryRowsTableOf_memBus_row
    (rows : List (RegisterBoundaryRow FGL)) (row : RegisterBoundaryRow FGL) :
    ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
        MemBusChannel.toRaw
        ((registerBoundaryRowsTableOf rows).environment (registerBoundaryRowArray row)) =
      registerBoundaryMemBusInteractions row := by
  rw [Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.RegisterBoundary.component_interactionsWith_memBus]
  simp only [registerBoundaryMemBusInteractions, List.map_cons, List.map_nil]
  apply congrArg₂ (fun boot reload => [boot, reload])
  · simpa [registerBoundaryRowsTableOf, registerBoundaryRowArray, Table.environment,
      Environment.fromInput] using registerBoundaryBootInteraction_eval_fromInput row
  · simpa [registerBoundaryRowsTableOf, registerBoundaryRowArray, Table.environment,
      Environment.fromInput] using registerBoundaryReloadInteraction_eval_fromInput row

private theorem registerBoundaryRowsTableOf_interactionsWith_memBus_go
    (allRows rows : List (RegisterBoundaryRow FGL)) :
    (rows.map registerBoundaryRowArray).flatMap (fun arr =>
      ZiskFv.AirsClean.RegisterBoundary.component.operations.interactionValuesWith
        MemBusChannel.toRaw ((registerBoundaryRowsTableOf allRows).environment arr)) =
      rows.flatMap registerBoundaryMemBusInteractions := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [registerBoundaryRowsTableOf_memBus_row, ih]

theorem registerBoundaryRowsTableOf_interactionsWith_memBus
    (rows : List (RegisterBoundaryRow FGL)) :
    (registerBoundaryRowsTableOf rows).interactionsWith MemBusChannel.toRaw =
      rows.flatMap registerBoundaryMemBusInteractions := by
  rw [Table.interactionsWith, registerBoundaryRowsTableOf_effectiveRows]
  exact registerBoundaryRowsTableOf_interactionsWith_memBus_go rows rows

theorem registerBoundarySingleRowTable_constraints
    (row : RegisterBoundaryRow FGL) :
    (registerBoundarySingleRowTable row).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.RegisterBoundary.component.circuit.localLength
        ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = 0 := by
    rfl
  have h_component :
      ZiskFv.AirsClean.RegisterBoundary.component.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.RegisterBoundary.component row h_localLength trivial
  rw [Table.Constraints, registerBoundarySingleRowTable_effectiveRows]
  intro arr h_arr
  simp only [List.mem_singleton] at h_arr
  subst arr
  simpa [registerBoundarySingleRowTable, registerBoundaryRowArray, Table.environment,
    Environment.fromInput] using h_component

theorem registerBoundaryRowsTableOf_constraints
    (rows : List (RegisterBoundaryRow FGL)) :
    (registerBoundaryRowsTableOf rows).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.RegisterBoundary.component.circuit.localLength
        ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = 0 := by
    rfl
  rw [Table.Constraints, registerBoundaryRowsTableOf_effectiveRows]
  intro arr h_arr
  rcases List.mem_map.mp h_arr with ⟨row, _h_row, rfl⟩
  have h_component :
      ZiskFv.AirsClean.RegisterBoundary.component.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.RegisterBoundary.component row h_localLength trivial
  simpa [registerBoundaryRowsTableOf, registerBoundaryRowArray, Table.environment,
    Environment.fromInput] using h_component

/-- **Every active register read in an accepted trace has a 24-bit-bounded step distance.**

This is the row-level form of the bus-102 descent: given a Main table row whose a-side register
selector is on, the distance `a_mem_step - a_reg_prev_mem_step - 1` that row pulls is forced into
`rangeTable24`. Nothing about the register columns is assumed -- the bound comes from the provider
table's own `Spec` via balance.

The b-side and store-side twins differ only in which selector and which distance they name. -/
theorem rangeTable24_spec_aRegStepDistance_of_active
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    (h_constraints : witness.Constraints)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {rowArray : Array FGL} (h_rowArray : rowArray ∈ mainTable.table)
    {row : MainRowWithRom FGL}
    (h_input :
      eval (mainTable.environment rowArray)
        (componentWithRomMemAndOpBus length program).rowInputVar = row)
    (h_component : mainTable.component = componentWithRomMemAndOpBus length program)
    (h_active : row.rom.a_src_reg = 1) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance row) := by
  have h_list :
      mainARegStepInteraction row ∈
        mainTable.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
    rw [Table.interactionsWith]
    refine List.mem_flatMap.mpr ⟨rowArray, h_rowArray, ?_⟩
    rw [h_component, mainRegisterStepInteractionsAt length program _ row h_input]
    simp
  refine ZiskFv.AirsClean.FullEnsemble.rangeTable24_spec_of_registerStepRange_pull
    h_balanced h_specs h_constraints h_mainTable h_list ?_ ?_
  · simp [mainARegStepInteraction, h_active]
  · rfl

/-- The b-side twin of `rangeTable24_spec_aRegStepDistance_of_active`. -/
theorem rangeTable24_spec_bRegStepDistance_of_active
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    (h_constraints : witness.Constraints)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {rowArray : Array FGL} (h_rowArray : rowArray ∈ mainTable.table)
    {row : MainRowWithRom FGL}
    (h_input :
      eval (mainTable.environment rowArray)
        (componentWithRomMemAndOpBus length program).rowInputVar = row)
    (h_component : mainTable.component = componentWithRomMemAndOpBus length program)
    (h_active : row.rom.b_src_reg = 1) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (bRegStepDistance row) := by
  have h_list :
      mainBRegStepInteraction row ∈
        mainTable.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
    rw [Table.interactionsWith]
    refine List.mem_flatMap.mpr ⟨rowArray, h_rowArray, ?_⟩
    rw [h_component, mainRegisterStepInteractionsAt length program _ row h_input]
    simp
  refine ZiskFv.AirsClean.FullEnsemble.rangeTable24_spec_of_registerStepRange_pull
    h_balanced h_specs h_constraints h_mainTable h_list ?_ ?_
  · simp [mainBRegStepInteraction, h_active]
  · rfl

/-- The store-side twin of `rangeTable24_spec_aRegStepDistance_of_active`. -/
theorem rangeTable24_spec_cRegStepDistance_of_active
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    (h_constraints : witness.Constraints)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {rowArray : Array FGL} (h_rowArray : rowArray ∈ mainTable.table)
    {row : MainRowWithRom FGL}
    (h_input :
      eval (mainTable.environment rowArray)
        (componentWithRomMemAndOpBus length program).rowInputVar = row)
    (h_component : mainTable.component = componentWithRomMemAndOpBus length program)
    (h_active : row.rom.store_reg = 1) :
    ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (cRegStepDistance row) := by
  have h_list :
      mainCRegStepInteraction row ∈
        mainTable.interactionsWith
          ZiskFv.Channels.SpecifiedRanges.RegisterStepRangeChannel.toRaw := by
    rw [Table.interactionsWith]
    refine List.mem_flatMap.mpr ⟨rowArray, h_rowArray, ?_⟩
    rw [h_component, mainRegisterStepInteractionsAt length program _ row h_input]
    simp
  refine ZiskFv.AirsClean.FullEnsemble.rangeTable24_spec_of_registerStepRange_pull
    h_balanced h_specs h_constraints h_mainTable h_list ?_ ?_
  · simp [mainCRegStepInteraction, h_active]
  · rfl

/-- **One counterpart step moves strictly later in the trace**, composed from the two lemmas that
supply its inputs rather than taking them as premises.

`selfMemProvider_registerPre_timestamp_of_mem_op_three` says the counterpart of a `mem_op = 3`
register read is a register-pre push carrying the consumer's read timestamp in the provider row's
`a_reg_prev_mem_step`; `rangeTable24_spec_aRegStepDistance_of_active` bounds that provider row's own
`a_mem_step - a_reg_prev_mem_step - 1`. Together the read happens strictly before the row that
supplied it accesses the register itself.

Only the a-side branch is discharged here — the collapse lemma returns a three-way disjunction and
the b/store twins need their own selector hypotheses. -/
theorem registerRead_timestamp_lt_provider_access
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    (h_constraints : witness.Constraints)
    {providerTable : Table FGL}
    (h_providerTable : providerTable ∈ witness.allTables)
    {providerRowArray : Array FGL} (h_providerRowArray : providerRowArray ∈ providerTable.table)
    {providerRow : MainRowWithRom FGL}
    (h_providerInput :
      eval (providerTable.environment providerRowArray)
        (componentWithRomMemAndOpBus length program).rowInputVar = providerRow)
    (h_providerComponent :
      providerTable.component = componentWithRomMemAndOpBus length program)
    (h_active : providerRow.rom.a_src_reg = 1)
    {mainTs : FGL}
    (h_link :
      (eval (providerTable.environment providerRowArray)
        (ZiskFv.AirsClean.Main.aRegPreMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).timestamp = mainTs)
    (h_bound : mainTs.val < 2 ^ 40) :
    mainTs.val < (1 + providerRow.rom.main_step * 4 : FGL).val := by
  have h_descent :
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance providerRow) :=
    rangeTable24_spec_aRegStepDistance_of_active h_balanced h_specs h_constraints
      h_providerTable h_providerRowArray h_providerInput h_providerComponent h_active
  have h_prev : providerRow.rom.a_reg_prev_mem_step = mainTs := by
    rw [ZiskFv.AirsClean.Main.eval_aRegPreMessageExpr, h_providerInput] at h_link
    simpa [ZiskFv.AirsClean.Main.aRegPreMessage] using h_link
  refine ZiskFv.AirsClean.FullEnsemble.prev_val_lt_of_registerStepSpec ?_ h_bound
  simpa [aRegStepDistance, h_prev] using h_descent

/-! ## The register walk, on concrete rows

`registerChain_nodup_of_descent` is the order-theoretic half: it assumes a chain relation on an
abstract list. What follows states the chain relation on *real Main rows* -- `r₂` supplies `r₁`'s
a-side register read exactly when `r₂`'s `a_reg_prev_mem_step` is `r₁`'s read timestamp -- and
derives the strict increase from the bus-102 descent rather than assuming it.
-/

/-- The a-side read timestamp of a Main row: `a_mem_step = 1 + main_step * 4`. -/
def aReadTimestamp (row : MainRowWithRom FGL) : FGL :=
  1 + row.rom.main_step * 4

/-- `provider` supplies `consumer`'s a-side register read: the provider row's register-pre push
carries the consumer's read timestamp, which is what
`selfMemProvider_registerPre_timestamp_of_mem_op_three` concludes from balance. -/
def ARegSupplies (consumer provider : MainRowWithRom FGL) : Prop :=
  provider.rom.a_reg_prev_mem_step = aReadTimestamp consumer

/-- **One supply step moves strictly later in time.** The provider's own bus-102 pull bounds
`a_mem_step - a_reg_prev_mem_step - 1`, and the link identifies that predecessor with the
consumer's read, so the consumer reads strictly before the provider accesses. -/
theorem aReadTimestamp_lt_of_supplies
    {consumer provider : MainRowWithRom FGL}
    (h_supplies : ARegSupplies consumer provider)
    (h_descent :
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance provider))
    (h_bound : (aReadTimestamp consumer).val < 2 ^ 40) :
    (aReadTimestamp consumer).val < (aReadTimestamp provider).val := by
  refine ZiskFv.AirsClean.FullEnsemble.prev_val_lt_of_registerStepSpec ?_ h_bound
  simpa [aRegStepDistance, aReadTimestamp, ARegSupplies] using
    (h_supplies ▸ h_descent : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec
      (aReadTimestamp provider - aReadTimestamp consumer - 1))

/-- **No row supplies its own register read.** The direct refutation of the shape #342 was opened
about, at its smallest: a self-loop would make a timestamp strictly precede itself. -/
theorem not_aRegSupplies_self
    {row : MainRowWithRom FGL}
    (h_descent : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance row))
    (h_bound : (aReadTimestamp row).val < 2 ^ 40) :
    ¬ ARegSupplies row row := by
  intro h_supplies
  exact absurd (aReadTimestamp_lt_of_supplies h_supplies h_descent h_bound) (lt_irrefl _)

/-- **No two-row cycle.** This is exactly the witness in #342's body: two rows on one register
pointing at each other's timestamps. Each supply step moves strictly later, so a two-cycle would
put a timestamp strictly before itself. -/
theorem not_aRegSupplies_two_cycle
    {r₁ r₂ : MainRowWithRom FGL}
    (h_descent₁ : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance r₁))
    (h_descent₂ : ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance r₂))
    (h_bound₁ : (aReadTimestamp r₁).val < 2 ^ 40)
    (h_bound₂ : (aReadTimestamp r₂).val < 2 ^ 40)
    (h₁₂ : ARegSupplies r₁ r₂) (h₂₁ : ARegSupplies r₂ r₁) : False := by
  have h_lt₁ := aReadTimestamp_lt_of_supplies h₁₂ h_descent₂ h_bound₁
  have h_lt₂ := aReadTimestamp_lt_of_supplies h₂₁ h_descent₁ h_bound₂
  exact absurd (h_lt₁.trans h_lt₂) (lt_irrefl _)

/-- **No cycle of any length.** A chain of supply steps visits no row timestamp twice, so the
register partition cannot close a loop. The chain relation here is the concrete one on Main rows,
and the strict increase at each step comes from that row's own bus-102 descent. -/
theorem aRegSupplies_chain_timestamps_nodup
    (rows : List (MainRowWithRom FGL))
    (h_descent : ∀ r ∈ rows,
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec (aRegStepDistance r))
    (h_bounds : ∀ r ∈ rows, (aReadTimestamp r).val < 2 ^ 40)
    (h_chain : List.IsChain ARegSupplies rows) :
    (rows.map aReadTimestamp).Nodup := by
  have h_mono : List.IsChain (fun a b => (aReadTimestamp a).val < (aReadTimestamp b).val) rows := by
    induction rows with
    | nil => simp
    | cons a rest ih =>
        cases rest with
        | nil => simp
        | cons b rest' =>
            rw [List.isChain_cons_cons] at h_chain
            rw [List.isChain_cons_cons]
            refine ⟨aReadTimestamp_lt_of_supplies h_chain.1 (h_descent b (by simp))
                (h_bounds a (by simp)), ?_⟩
            exact ih (fun r hr => h_descent r (by simp [hr]))
              (fun r hr => h_bounds r (by simp [hr])) h_chain.2
  haveI : Trans (fun a b : MainRowWithRom FGL => (aReadTimestamp a).val < (aReadTimestamp b).val)
      (fun a b : MainRowWithRom FGL => (aReadTimestamp a).val < (aReadTimestamp b).val)
      (fun a b : MainRowWithRom FGL => (aReadTimestamp a).val < (aReadTimestamp b).val) :=
    ⟨fun h1 h2 => Nat.lt_trans h1 h2⟩
  have h_pairwise := h_mono.pairwise
  rw [List.Nodup, List.pairwise_map]
  exact h_pairwise.imp (fun {a b} h h_eq => absurd (congrArg Fin.val h_eq) (Nat.ne_of_lt h))

end ZiskFv.Compliance.Instantiation
