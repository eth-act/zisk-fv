import ZiskFv.AirsClean.Main.Circuit
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.Mem.Bridge
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

def mainRowArray (row : MainRowWithRom FGL) : Array FGL :=
  (toElements row).toArray

def mainSingleRowTable
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    Table FGL where
  component := componentWithRomMemAndOpBus length program
  width := size MainRowWithRom
  table := [mainRowArray row]
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [mainRowArray] at h_arr
    subst arr
    simp

theorem mainSingleRowTable_rowInput
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    (componentWithRomMemAndOpBus length program).rowInput
        ((mainSingleRowTable length program row).environment (mainRowArray row)) =
      row := by
  change (componentWithRomMemAndOpBus length program).rowInput
      (Environment.fromInput row emptyData) = row
  simp [Air.Flat.Component.rowInput,
    ProvableType.valueFromOffset_zero_fromInput_eq]

theorem mainSingleRowTable_eval_rowInputVar
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    Eval.eval ((mainSingleRowTable length program row).environment (mainRowArray row))
        (componentWithRomMemAndOpBus length program).rowInputVar =
      row := by
  change Eval.eval (Environment.fromInput row emptyData) (varFromOffset MainRowWithRom 0) = row
  exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData

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
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    (((OpBusChannel.emitted
        (-(componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)
        (opBusMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar.core)).toRaw).eval
      ((mainSingleRowTable length program row).environment (mainRowArray row))) =
      mainOpBusInteraction row := by
  let env := (mainSingleRowTable length program row).environment (mainRowArray row)
  let rowVar := (componentWithRomMemAndOpBus length program).rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact mainSingleRowTable_eval_rowInputVar length program row
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
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL) :
    (mainSingleRowTable length program row).interactionsWith OpBusChannel.toRaw =
      [mainOpBusInteraction row] := by
  simp [Table.interactionsWith, mainSingleRowTable, mainRowArray,
    Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_opBus]
  exact mainComponentOpBusInteraction_eval length program row

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
  let env := (mainSingleRowTable length program row).environment (mainRowArray row)
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
  simp [Table.interactionsWith, mainSingleRowTable, mainRowArray, mainMemBusInteractions,
    Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_memBus]

theorem mainSingleRowTable_constraints_of_proverAssumptions
    (length : ℕ) (program : Program length) (row : MainRowWithRom FGL)
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
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      (componentWithRomMemAndOpBus length program) row h_localLength h_assumptions
  rw [Table.Constraints]
  intro arr h_arr
  simp [mainSingleRowTable, mainRowArray] at h_arr
  subst arr
  simpa [mainSingleRowTable, mainRowArray, Environment.fromInput] using h_component

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
  rw [mainSingleRowTable_interactionsWith_opBus]
  decide

def binaryAddRowArray (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) : Array FGL :=
  (toElements row).toArray

def binaryAddSingleRowTable (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    Table FGL where
  component := ZiskFv.AirsClean.BinaryAdd.component
  width := size ZiskFv.AirsClean.BinaryAdd.BinaryAddRow
  table := [binaryAddRowArray row]
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [binaryAddRowArray] at h_arr
    subst arr
    simp

theorem binaryAddSingleRowTable_rowInput
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    ZiskFv.AirsClean.BinaryAdd.component.rowInput
        ((binaryAddSingleRowTable row).environment (binaryAddRowArray row)) =
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
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    (((OpBusChannel.pushed
        (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
          ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
      ((binaryAddSingleRowTable row).environment (binaryAddRowArray row))) =
      binaryAddOpBusInteraction row := by
  let env := (binaryAddSingleRowTable row).environment (binaryAddRowArray row)
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

theorem binaryAddSingleRowTable_interactionsWith_opBus
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL) :
    (binaryAddSingleRowTable row).interactionsWith OpBusChannel.toRaw =
      [binaryAddOpBusInteraction row] := by
  simp [Table.interactionsWith, binaryAddSingleRowTable, binaryAddRowArray,
    Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus]
  exact binaryAddComponentOpBusInteraction_eval row

theorem binaryAddSingleRowTable_constraints_of_proverAssumptions
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (h_assumptions :
      ZiskFv.AirsClean.BinaryAdd.component.circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (binaryAddSingleRowTable row).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.BinaryAdd.component.circuit.localLength
        ZiskFv.AirsClean.BinaryAdd.component.rowInputVar = 0 := by
    change ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated.localLength
        ZiskFv.AirsClean.BinaryAdd.component.rowInputVar = 0
    rfl
  have h_component :
      ZiskFv.AirsClean.BinaryAdd.component.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.BinaryAdd.component row h_localLength h_assumptions
  rw [Table.Constraints]
  intro arr h_arr
  simp [binaryAddSingleRowTable, binaryAddRowArray] at h_arr
  subst arr
  simpa [binaryAddSingleRowTable, binaryAddRowArray, Environment.fromInput] using h_component

def binaryRowArray (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) : Array FGL :=
  (toElements row).toArray

def binarySingleRowTable (row : ZiskFv.AirsClean.Binary.BinaryRow FGL) : Table FGL where
  component := ZiskFv.AirsClean.Binary.staticLookupComponent
  width := size ZiskFv.AirsClean.Binary.BinaryRow
  table := [binaryRowArray row]
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [binaryRowArray] at h_arr
    subst arr
    simp

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
  simp [Table.interactionsWith, binarySingleRowTable, binaryRowArray,
    Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Binary.staticLookupComponent_interactionsWith_opBus]
  exact binaryComponentOpBusInteraction_eval row

theorem binarySingleRowTable_constraints_of_proverAssumptions
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_assumptions :
      ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.ProverAssumptions
        row emptyData (ProverHint.empty FGL)) :
    (binarySingleRowTable row).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.localLength
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar = 0 := by
    change ZiskFv.AirsClean.Binary.binaryWithStaticBinaryTableElaborated.localLength
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar = 0
    rfl
  have h_component :
      ZiskFv.AirsClean.Binary.staticLookupComponent.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.Binary.staticLookupComponent row h_localLength h_assumptions
  rw [Table.Constraints]
  intro arr h_arr
  simp [binarySingleRowTable, binaryRowArray] at h_arr
  subst arr
  simpa [binarySingleRowTable, binaryRowArray, Environment.fromInput] using h_component

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

def memRowArray (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Array FGL :=
  (toElements row).toArray

def memSingleRowTable (row : ZiskFv.AirsClean.Mem.MemRow FGL) : Table FGL where
  component := ZiskFv.AirsClean.Mem.componentWithDualMemBus
  width := size ZiskFv.AirsClean.Mem.MemRow
  table := [memRowArray row]
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [memRowArray] at h_arr
    subst arr
    simp

theorem memSingleRowTable_rowInput
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInput
        ((memSingleRowTable row).environment (memRowArray row)) =
      row := by
  change ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInput
      (Environment.fromInput row emptyData) = row
  simp [Air.Flat.Component.rowInput, ProvableType.valueFromOffset_zero_fromInput_eq]

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

theorem memComponentMemBusInteraction_eval
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    (((MemBusChannel.emitted
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
        (ZiskFv.AirsClean.Mem.memBusMessageExpr
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
      ((memSingleRowTable row).environment (memRowArray row))) =
      memBusInteraction row := by
  let env := (memSingleRowTable row).environment (memRowArray row)
  let rowVar := ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_input : eval env rowVar = row := by
    change eval (Environment.fromInput row emptyData)
        (varFromOffset ZiskFv.AirsClean.Mem.MemRow 0) = row
    exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData
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
      ((memSingleRowTable row).environment (memRowArray row))) =
      memBusDualInteraction row := by
  let env := (memSingleRowTable row).environment (memRowArray row)
  let rowVar := ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_input : eval env rowVar = row := by
    change eval (Environment.fromInput row emptyData)
        (varFromOffset ZiskFv.AirsClean.Mem.MemRow 0) = row
    exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData
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
  simp [Table.interactionsWith, memSingleRowTable, memRowArray,
    Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus]
  exact ⟨memComponentMemBusInteraction_eval row,
    memComponentMemBusDualInteraction_eval row⟩

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
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.Mem.componentWithDualMemBus row h_localLength h_assumptions
  rw [Table.Constraints]
  intro arr h_arr
  simp [memSingleRowTable, memRowArray] at h_arr
  subst arr
  simpa [memSingleRowTable, memRowArray, Environment.fromInput] using h_component

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
  width := size RegisterBoundaryRow
  table := rows.map registerBoundaryRowArray
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [registerBoundaryRowArray] at h_arr
    rcases h_arr with ⟨row, _h_row, rfl⟩
    simp

def registerBoundarySingleRowTable (row : RegisterBoundaryRow FGL) : Table FGL where
  component := ZiskFv.AirsClean.RegisterBoundary.component
  width := size RegisterBoundaryRow
  table := [registerBoundaryRowArray row]
  data := emptyData
  uniform_width := by
    intro arr h_arr
    simp [registerBoundaryRowArray] at h_arr
    subst arr
    simp

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
    (row : RegisterBoundaryRow FGL) :
    (((MemBusChannel.emitted (-1)
        (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
      (Environment.fromInput row emptyData)) =
      registerBoundaryBootInteraction row := by
  let env := Environment.fromInput row emptyData
  let rowVar := ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData
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
    (row : RegisterBoundaryRow FGL) :
    (((MemBusChannel.emitted 1
        (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
      (Environment.fromInput row emptyData)) =
      registerBoundaryReloadInteraction row := by
  let env := Environment.fromInput row emptyData
  let rowVar := ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar
  have h_input : eval env rowVar = row := by
    dsimp [env, rowVar]
    exact ProvableType.eval_fromInput_varFromOffset_zero row emptyData
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
  simp [Table.interactionsWith, registerBoundarySingleRowTable, registerBoundaryRowArray,
    registerBoundaryMemBusInteractions, Operations.interactionValuesWith_eq_map,
    ZiskFv.AirsClean.RegisterBoundary.component_interactionsWith_memBus]
  exact ⟨registerBoundaryComponentBootInteraction_eval row,
    registerBoundaryComponentReloadInteraction_eval row⟩

theorem registerBoundaryRowsTableOf_interactionsWith_memBus
    (rows : List (RegisterBoundaryRow FGL)) :
    (registerBoundaryRowsTableOf rows).interactionsWith MemBusChannel.toRaw =
      rows.flatMap registerBoundaryMemBusInteractions := by
  induction rows with
  | nil =>
      simp [Table.interactionsWith, registerBoundaryRowsTableOf]
  | cons row rows ih =>
      simp only [List.flatMap_cons]
      rw [← ih]
      simp [Table.interactionsWith, registerBoundaryRowsTableOf, registerBoundaryRowArray,
        registerBoundaryMemBusInteractions, Table.environment,
        Operations.interactionValuesWith_eq_map,
        ZiskFv.AirsClean.RegisterBoundary.component_interactionsWith_memBus,
        registerBoundaryBootInteraction_eval_fromInput,
        registerBoundaryReloadInteraction_eval_fromInput]

theorem registerBoundarySingleRowTable_constraints
    (row : RegisterBoundaryRow FGL) :
    (registerBoundarySingleRowTable row).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.RegisterBoundary.component.circuit.localLength
        ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = 0 := by
    change ZiskFv.AirsClean.RegisterBoundary.registerBoundaryElaborated.localLength
        ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = 0
    rfl
  have h_component :
      ZiskFv.AirsClean.RegisterBoundary.component.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.RegisterBoundary.component row h_localLength trivial
  rw [Table.Constraints]
  intro arr h_arr
  simp [registerBoundarySingleRowTable, registerBoundaryRowArray] at h_arr
  subst arr
  simpa [registerBoundarySingleRowTable, registerBoundaryRowArray, Environment.fromInput]
    using h_component

theorem registerBoundaryRowsTableOf_constraints
    (rows : List (RegisterBoundaryRow FGL)) :
    (registerBoundaryRowsTableOf rows).Constraints := by
  have h_localLength :
      ZiskFv.AirsClean.RegisterBoundary.component.circuit.localLength
        ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = 0 := by
    change ZiskFv.AirsClean.RegisterBoundary.registerBoundaryElaborated.localLength
        ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar = 0
    rfl
  rw [Table.Constraints]
  intro arr h_arr
  simp [registerBoundaryRowsTableOf, registerBoundaryRowArray] at h_arr
  rcases h_arr with ⟨row, _h_row, rfl⟩
  have h_component :
      ZiskFv.AirsClean.RegisterBoundary.component.operations.ConstraintsHold
        (Environment.fromInput row emptyData) :=
    component_constraintsHold_of_proverAssumptions
      ZiskFv.AirsClean.RegisterBoundary.component row h_localLength trivial
  simpa [registerBoundaryRowsTableOf, registerBoundaryRowArray, Environment.fromInput]
    using h_component

end ZiskFv.Compliance.Instantiation
