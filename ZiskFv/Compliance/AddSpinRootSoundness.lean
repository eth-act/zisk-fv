import ZiskFv.Compliance.AddSpinWitness
import ZiskFv.Soundness

set_option maxRecDepth 10000

/-!
# Concrete `stepSound_of_programDecodes` instantiation for the ADD + spin-loop trace (#220)

This file applies the public `stepSound_of_programDecodes` theorem to the concrete
`addSpinAcceptedTrace` witness from `AddSpinWitness.lean`.
-/

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.Compliance.SingleAddWitness
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.AddSpinRootSoundness

def x0 : regidx := regidx.Regidx (0#5)

def x1 : regidx := regidx.Regidx (1#5)

def addSpinAddIndex : Fin 2 := ⟨0, by decide⟩

def addSpinJalIndex : Fin 2 := ⟨1, by decide⟩

def addSpinAddClaim : Claim_add addSpinAcceptedTrace addSpinAddIndex where
  r1 := x1
  r2 := x1
  rd := x1

def addSpinJalClaim : Claim_jal addSpinAcceptedTrace addSpinJalIndex where
  imm := 0#21
  rd := x0

def addSpinZiskStep : ∀ i : Fin 2, ZiskStep addSpinAcceptedTrace i
  | ⟨0, _⟩ => .add addSpinAddClaim
  | ⟨1, _⟩ => .jal addSpinJalClaim

def addSpinMisa : RegisterType Register.misa := 0#64

def addSpinRegs (pc : BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.misa addSpinMisa
  regs2.insert (reg_of_fin (regidx_to_fin x1)) (0#64)

def addSpinState (pc : BitVec 64) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := addSpinRegs pc
    mem := {} }

def addSpinSailTrace : SailTrace 2
  | ⟨0, _⟩ => addSpinState (0#64)
  | ⟨1, _⟩ => addSpinState (4#64)

theorem addSpinRowsOf_empty_readSound :
    MemoryBusRowsPrefixReadSound
      ({} : Std.ExtHashMap Nat (BitVec 8))
      ((List.range addSpinAcceptedTrace.numInstructions).flatMap (fun _ => [])) := by
  change MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8)) []
  intro priorRows entry laterRows h_split h_selected
  simp at h_split

def addSpinBootSeed :
    BootSegmentMemorySeed addSpinAcceptedTrace addSpinSailTrace addSpinZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by
    intro h
    rfl
  step := by
    intro j h
    change j + 1 < 2 at h
    have hj : j = 0 := by omega
    subst j
    simp [addSpinSailTrace, addSpinState, replayMemoryAfterBusRows]
  readSoundInputs := fun h => absurd h addSpinWitness_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_nonempty
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_nonempty
  placement := by
    intro i
    fin_cases i <;> simp [MemoryOpPlacement, addSpinZiskStep]

private theorem addSpinAcceptedTrace_program :
    addSpinAcceptedTrace.program = addSpinProgram := rfl

private theorem addSpinMainRowAt_zero :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addSpinProgram
      addSpinMainTable 0 = addSpinAddRow := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows])]
  exact addSpinMainTable_eval_rowInputVar_zero
    (by norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows])

private theorem addSpinMainRowAt_one :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addSpinProgram
      addSpinMainTable 1 = addSpinJalRow 1 := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows])]
  exact addSpinMainTable_eval_rowInputVar_one
    (by norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows])

private theorem addSpinMainPc_add :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinAcceptedTrace.program
        addSpinAcceptedTrace.mainTable).pc addSpinAddIndex.val = 0 := by
  rw [addSpinAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable).pc 0 = 0
  simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row]

private theorem addSpinMainPc_jal :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinAcceptedTrace.program
        addSpinAcceptedTrace.mainTable).pc addSpinJalIndex.val = 4 := by
  rw [addSpinAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable).pc 1 = 4
  simp [addSpinMainRowAt_one, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
    ZiskFv.AirsClean.Main.mainRomRowOf]

private theorem addSpinReadX1_add :
    read_xreg (regidx_to_fin x1) (addSpinSailTrace addSpinAddIndex) =
      EStateM.Result.ok (0#64) (addSpinSailTrace addSpinAddIndex) := by
  simp [addSpinSailTrace, addSpinAddIndex, addSpinState, addSpinRegs, x1,
    regidx_to_fin, read_xreg, reg_of_fin]

def addSpinAddInput : PureSpec.AddInput where
  r1_val := 0#64
  r2_val := 0#64
  rd := regidx_to_fin x1
  PC := 0#64

def addSpinJalInput : PureSpec.JalInput where
  imm := 0#21
  rd := regidx_to_fin x0
  PC := 4#64

def addSpinAddProgramDecode :
    ProgramDecode_add addSpinAcceptedTrace addSpinAddIndex addSpinAddClaim where
  h_idx := by
    rw [addSpinAcceptedTrace_mainTable_eq]
    norm_num [addSpinAddIndex, mainRowsTable, addSpinMainRows]
  bits := addSpinAddBits
  h_bits_ieo := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_m32 := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_set_pc := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_store_pc := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_store_ind := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_store_reg := by
    simp [addSpinAddBits, addX1RomFlagBits, addSpinAddClaim, x1, regidx_to_fin]
  aFacts := by
    refine { h_src_reg := ?_, h_src_imm := ?_, h_program := ?_ }
    · simp [addSpinAddBits, addX1RomFlagBits, addSpinAddClaim, x1, regidx_to_fin]
    · simp [addSpinAddBits, addX1RomFlagBits, addSpinAddClaim, x1, regidx_to_fin]
    · intro j hline
      fin_cases j
      · simp only [addSpinAcceptedTrace, addSpinProgram]
        norm_num [addSpinAddProgramRow, addX1ProgramRow,
          addSpinAddBits, addX1RomFlagBits,
          addSpinAddClaim, x1, regidx_to_fin, Transpiler.ind, ZiskFv.AirsClean.Main.packFlags,
          ZiskFv.AirsClean.boolF]
      · rw [addSpinMainPc_add, addSpinAcceptedTrace_program] at hline
        exfalso
        have hval := congrArg (fun x : FGL => x.val) hline
        norm_num [addSpinAcceptedTrace, addSpinProgram, addSpinJalProgramRow] at hval
  bFacts := by
    refine { h_src_reg := ?_, h_src_imm := ?_, h_program := ?_ }
    · simp [addSpinAddBits, addX1RomFlagBits, addSpinAddClaim, x1, regidx_to_fin]
    · simp [addSpinAddBits, addX1RomFlagBits, addSpinAddClaim, x1, regidx_to_fin]
    · intro j hline
      fin_cases j
      · simp only [addSpinAcceptedTrace, addSpinProgram]
        norm_num [addSpinAddProgramRow, addX1ProgramRow,
          addSpinAddBits, addX1RomFlagBits,
          addSpinAddClaim, x1, regidx_to_fin, Transpiler.ind, ZiskFv.AirsClean.Main.packFlags,
          ZiskFv.AirsClean.boolF]
      · rw [addSpinMainPc_add, addSpinAcceptedTrace_program] at hline
        exfalso
        have hval := congrArg (fun x : FGL => x.val) hline
        norm_num [addSpinAcceptedTrace, addSpinProgram, addSpinJalProgramRow] at hval
  h_prog := by
    intro j hline
    change Fin 2 at j
    fin_cases j
    · simp only [addSpinAcceptedTrace, addSpinProgram]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · simp [addSpinAddProgramRow, addX1ProgramRow, addSpinAddClaim, x1,
          Transpiler.ind, regidx_to_fin]
      · norm_num [addSpinAddProgramRow, addX1ProgramRow, ZiskFv.AirsClean.Main.packFlags,
          addSpinAddBits, addX1RomFlagBits, ZiskFv.AirsClean.boolF]
    · rw [addSpinMainPc_add] at hline
      rw [addSpinAcceptedTrace_program] at hline
      norm_num [addSpinAcceptedTrace, addSpinProgram, addSpinJalProgramRow] at hline
      exfalso
      have hval := congrArg (fun x : FGL => x.val) hline
      norm_num at hval

def addSpinJalProgramDecode :
    ProgramDecode_jal addSpinAcceptedTrace addSpinJalIndex addSpinJalClaim where
  h_idx := by
    rw [addSpinAcceptedTrace_mainTable_eq]
    change 1 + 1 < addSpinMainTable.table.length
    norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows]
  bits := addSpinJalBits
  h_bits_ieo := by rfl
  h_bits_m32 := by rfl
  h_bits_set_pc := by rfl
  h_bits_store_pc := by rfl
  h_bits_store_ind := by rfl
  h_bits_store_reg := by
    simp [addSpinJalBits, addSpinJalClaim, x0, regidx_to_fin]
  h_prog := by
    intro j hline
    change Fin 2 at j
    fin_cases j
    · rw [addSpinMainPc_jal] at hline
      rw [addSpinAcceptedTrace_program] at hline
      norm_num [addSpinAcceptedTrace, addSpinProgram, addSpinAddProgramRow, addX1ProgramRow]
        at hline
      exfalso
      have hval := congrArg (fun x : FGL => x.val) hline
      norm_num at hval
    · simp only [addSpinAcceptedTrace, addSpinProgram]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · simp [addSpinJalProgramRow, addSpinJalClaim, x0, Transpiler.ind, regidx_to_fin]
      · norm_num [addSpinJalProgramRow, ZiskFv.AirsClean.Main.packFlags,
          addSpinJalBits, ZiskFv.AirsClean.boolF]

private theorem addSpinAddLaneLo
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      (field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable) 0) = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinAcceptedTrace.program
        addSpinAcceptedTrace.mainTable) addSpinAddIndex.val =
      lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addSpinSailTrace addSpinAddIndex)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addSpinSailTrace addSpinAddIndex) (regidx_to_fin x1) (0#64) addSpinReadX1_add]
  rw [addSpinAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable) 0 = _
  rw [h_field]
  simp [lane_lo]

private theorem addSpinAddLaneHi
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      (field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable) 0) = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinAcceptedTrace.program
        addSpinAcceptedTrace.mainTable) addSpinAddIndex.val =
      lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addSpinSailTrace addSpinAddIndex)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addSpinSailTrace addSpinAddIndex) (regidx_to_fin x1) (0#64) addSpinReadX1_add]
  rw [addSpinAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable) 0 = _
  rw [h_field]
  simp [lane_hi]

def addSpinAddInputs :
    Inputs_add addSpinAcceptedTrace addSpinSailTrace addSpinAddIndex addSpinAddClaim where
  add_input := addSpinAddInput
  h_input_r1 := by
    simpa [addSpinAddInput, addSpinAddClaim] using addSpinReadX1_add
  h_input_r2 := by
    simpa [addSpinAddInput, addSpinAddClaim] using addSpinReadX1_add
  h_input_pc := by
    simp [addSpinAddInput, addSpinSailTrace, addSpinAddIndex, addSpinState, addSpinRegs, x1,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := by
    rfl
  h_pc_bridge := by
    rw [addSpinAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable).pc 0).val = _
    simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row, addSpinAddInput]

def addSpinJalInputs :
    Inputs_jal addSpinAcceptedTrace addSpinSailTrace addSpinJalIndex addSpinJalClaim where
  jal_input := addSpinJalInput
  misa_val := addSpinMisa
  h_pc_bridge := by
    rw [addSpinAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable).pc 1).val = _
    simp [addSpinMainRowAt_one, addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
      ZiskFv.AirsClean.Main.mainRomRowOf, addSpinJalInput]
  h_input_rd := by
    rfl
  h_input_pc := by
    simp [addSpinJalInput, addSpinSailTrace, addSpinJalIndex, addSpinState, addSpinRegs, x1,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_misa := by
    simp [addSpinSailTrace, addSpinJalIndex, addSpinState, addSpinRegs, x1,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_misa_c := by
    simp [addSpinMisa]
  h_success := by
    simp [addSpinJalInput, PureSpec.execute_JAL_pure]
  h_input_imm := by
    rfl

def addSpinProgramDecodes :
    ∀ i : Fin 2, ProgramDecode addSpinAcceptedTrace i (addSpinZiskStep i)
  | ⟨0, _⟩ => addSpinAddProgramDecode
  | ⟨1, _⟩ => addSpinJalProgramDecode

def addSpinInputsAgree :
    ∀ i : Fin 2, InputsAgree addSpinAcceptedTrace addSpinSailTrace i (addSpinZiskStep i)
  | ⟨0, _⟩ => addSpinAddInputs
  | ⟨1, _⟩ => addSpinJalInputs

/-- The two root PC premises for this witness, from the per-row family above
    (`pcSeed_of_inputsAgree` / `inputsAgreeCore_of_inputsAgree`). -/
def addSpinPcSeed : SegmentPcSeed addSpinAcceptedTrace addSpinSailTrace :=
  pcSeed_of_inputsAgree addSpinInputsAgree

def addSpinInputsAgreeCore :
    ∀ i : Fin 2, InputsAgreeCore addSpinAcceptedTrace addSpinSailTrace i (addSpinZiskStep i) :=
  fun i => inputsAgreeCore_of_inputsAgree i (addSpinZiskStep i) (addSpinInputsAgree i)

def addSpinAddOutsideDefectRegion :
    RowOutsideDefectRegion addSpinAcceptedTrace addSpinAddIndex
      (addSpinZiskStep addSpinAddIndex) := by
  unfold RowOutsideDefectRegion addSpinZiskStep MainSequentialPcDomain mainPcVal
  rw [addSpinMainPc_add]
  change 0 < GL_prime - 4
  norm_num

def addSpinJalOutsideDefectRegion :
    RowOutsideDefectRegion addSpinAcceptedTrace addSpinJalIndex
      (addSpinZiskStep addSpinJalIndex) where
  h_target_nonneg := by
    unfold mainPcVal
    rw [addSpinMainPc_jal]
    change 0 ≤ (4 : Int) + (BitVec.signExtend 64 (0#21)).toInt
    simp
  h_target_lt := by
    unfold mainPcVal
    rw [addSpinMainPc_jal]
    change (4 : Int) + (BitVec.signExtend 64 (0#21)).toInt < GL_prime
    simp
  h_pc_bound := by
    unfold MainSequentialPcDomain mainPcVal
    rw [addSpinMainPc_jal]
    change 4 < GL_prime - 4
    norm_num
  h_pc_offset_lt_2_32 := by
    intro pc hpc
    unfold mainPcVal at hpc
    rw [addSpinMainPc_jal] at hpc
    rw [BitVec.toNat_add]
    rw [← hpc]
    norm_num

def addSpinOutsideDefectRegion :
    ∀ i : Fin 2, RowOutsideDefectRegion addSpinAcceptedTrace i (addSpinZiskStep i)
  | ⟨0, _⟩ => addSpinAddOutsideDefectRegion
  | ⟨1, _⟩ => addSpinJalOutsideDefectRegion

/-- #330 Phase 7: each executed step's producer entry is its own row's successor `pc`. Only a
    two-row unaligned JALR lowering can break this, and only at a step that has a successor. -/
def addSpinRowsAligned :
    StepRowsAligned addSpinAcceptedTrace addSpinZiskStep
      (fun i => rowDecode_of_programDecode addSpinAcceptedTrace i (addSpinProgramDecodes i)) := by
  intro j h
  have h' : j + 1 < 2 := h
  have hj : j < 2 - 1 := by omega
  interval_cases j ; rfl

set_option maxHeartbeats 4000000 in
def addSpinLaneBridge : ∀ i : Fin 2,
    LaneBridge addSpinAcceptedTrace (addSpinSailTrace i) i.val := by
  intro i
  fin_cases i
  · constructor
    · intro r _ _ hoff
      have hre : r = regidx_to_fin x1 := by
        rw [addSpinAcceptedTrace_mainTable_eq, addSpinAcceptedTrace_program] at hoff
        rw [addSpinMainRowAt_zero] at hoff
        fin_cases r <;> simp [addSpinAddRow, addX1Row,
          Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
      rw [hre]
      simpa [addSpinAddIndex] using addSpinAddLaneLo (fun m i => m.a_0 i)
        (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
    · intro r _ _ hoff
      have hre : r = regidx_to_fin x1 := by
        rw [addSpinAcceptedTrace_mainTable_eq, addSpinAcceptedTrace_program] at hoff
        rw [addSpinMainRowAt_zero] at hoff
        fin_cases r <;> simp [addSpinAddRow, addX1Row,
          Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
      rw [hre]
      simpa [addSpinAddIndex] using addSpinAddLaneHi (fun m i => m.a_1 i)
        (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
    · intro r _ _ hoff
      have hre : r = regidx_to_fin x1 := by
        rw [addSpinAcceptedTrace_mainTable_eq, addSpinAcceptedTrace_program] at hoff
        rw [addSpinMainRowAt_zero] at hoff
        fin_cases r <;> simp [addSpinAddRow, addX1Row,
          Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
      rw [hre]
      simpa [addSpinAddIndex] using addSpinAddLaneLo (fun m i => m.b_0 i)
        (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
    · intro r _ _ hoff
      have hre : r = regidx_to_fin x1 := by
        rw [addSpinAcceptedTrace_mainTable_eq, addSpinAcceptedTrace_program] at hoff
        rw [addSpinMainRowAt_zero] at hoff
        fin_cases r <;> simp [addSpinAddRow, addX1Row,
          Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
      rw [hre]
      simpa [addSpinAddIndex] using addSpinAddLaneHi (fun m i => m.b_1 i)
        (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
  · constructor <;> intro r hr hsrc hoff <;> exfalso
    all_goals
      rw [addSpinAcceptedTrace_mainTable_eq, addSpinAcceptedTrace_program] at hsrc
      rw [addSpinMainRowAt_one] at hsrc
      simp [addSpinJalRow, addSpinJalProgramRow, addSpinJalBits,
        ZiskFv.AirsClean.Main.mainRomRowOf] at hsrc

/-- The two root PC premises for this witness: boot agreement, and the Sail-internal retire law.
    `sailRetireChain_of_inputsAgree` builds the latter from the per-row `InputsAgree` family this
    witness already proves — no new content, and no hand-evaluated Sail execution. -/
def addSpinPcChain : SegmentPcChain addSpinAcceptedTrace addSpinSailTrace addSpinZiskStep where
  toSailRetireChain :=
    sailRetireChain_of_inputsAgree
      (fun i => rowDecode_of_programDecode addSpinAcceptedTrace i (addSpinProgramDecodes i))
      addSpinInputsAgree addSpinBootSeed addSpinOutsideDefectRegion addSpinLaneBridge addSpinRowsAligned
  boot := (pcSeed_of_inputsAgree addSpinInputsAgree).boot

theorem addSpinRootSoundness :
    ∀ i : Fin 2, StepSound addSpinAcceptedTrace addSpinSailTrace i
      (addSpinZiskStep i)
      (rowDecode_of_programDecode addSpinAcceptedTrace i (addSpinProgramDecodes i)) :=
  stepSound_of_programDecodes 2 addSpinAcceptedTrace addSpinSailTrace addSpinZiskStep
    addSpinProgramDecodes addSpinInputsAgreeCore addSpinPcChain addSpinRowsAligned
    addSpinBootSeed addSpinOutsideDefectRegion addSpinLaneBridge

theorem addSpinAddStepSound :
    StepSound addSpinAcceptedTrace addSpinSailTrace addSpinAddIndex
      (addSpinZiskStep addSpinAddIndex)
      (rowDecode_of_programDecode addSpinAcceptedTrace addSpinAddIndex
        (addSpinProgramDecodes addSpinAddIndex)) :=
  addSpinRootSoundness addSpinAddIndex

def addPaddedAddIndex : Fin 1 := ⟨0, by decide⟩

def addPaddedAddClaim : Claim_add addPaddedAcceptedTrace addPaddedAddIndex where
  r1 := x1
  r2 := x1
  rd := x1

def addPaddedZiskStep : ∀ i : Fin 1, ZiskStep addPaddedAcceptedTrace i
  | ⟨0, _⟩ => .add addPaddedAddClaim

def addPaddedSailTrace : SailTrace 1
  | ⟨0, _⟩ => addSpinState (0#64)

theorem addPaddedRowsOf_empty_readSound :
    MemoryBusRowsPrefixReadSound
      ({} : Std.ExtHashMap Nat (BitVec 8))
      ((List.range addPaddedAcceptedTrace.numInstructions).flatMap (fun _ => [])) := by
  change MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8)) []
  intro priorRows entry laterRows h_split h_selected
  simp at h_split

def addPaddedBootSeed :
    BootSegmentMemorySeed addPaddedAcceptedTrace addPaddedSailTrace addPaddedZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by
    intro h
    rfl
  step := by
    intro j h
    change j + 1 < 1 at h
    omega
  readSoundInputs := fun h => absurd h addSpinWitness_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_nonempty
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_nonempty
  placement := by
    intro i
    fin_cases i
    simp [MemoryOpPlacement, addPaddedZiskStep]

private theorem addPaddedAcceptedTrace_program :
    addPaddedAcceptedTrace.program = addSpinProgram := rfl

private theorem addPaddedMainPc_add :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addPaddedAcceptedTrace.program
        addPaddedAcceptedTrace.mainTable).pc addPaddedAddIndex.val = 0 := by
  rw [addPaddedAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable).pc 0 = 0
  simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row]

private theorem addPaddedReadX1 :
    read_xreg (regidx_to_fin x1) (addPaddedSailTrace addPaddedAddIndex) =
      EStateM.Result.ok (0#64) (addPaddedSailTrace addPaddedAddIndex) := by
  simp [addPaddedSailTrace, addPaddedAddIndex, addSpinState, addSpinRegs, x1,
    regidx_to_fin, read_xreg, reg_of_fin]

def addPaddedAddProgramDecode :
    ProgramDecode_add addPaddedAcceptedTrace addPaddedAddIndex addPaddedAddClaim where
  h_idx := by
    rw [addPaddedAcceptedTrace_mainTable_eq]
    change 0 + 1 < addSpinMainTable.table.length
    norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows]
  bits := addSpinAddBits
  h_bits_ieo := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_m32 := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_set_pc := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_store_pc := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_store_ind := by simp [addSpinAddBits, addX1RomFlagBits]
  h_bits_store_reg := by
    simp [addSpinAddBits, addX1RomFlagBits, addPaddedAddClaim, x1, regidx_to_fin]
  aFacts := by
    refine { h_src_reg := ?_, h_src_imm := ?_, h_program := ?_ }
    · simp [addSpinAddBits, addX1RomFlagBits, addPaddedAddClaim, x1, regidx_to_fin]
    · simp [addSpinAddBits, addX1RomFlagBits, addPaddedAddClaim, x1, regidx_to_fin]
    · intro j hline
      fin_cases j
      · simp only [addPaddedAcceptedTrace, addSpinProgram]
        norm_num [addSpinAddProgramRow, addX1ProgramRow,
          addSpinAddBits, addX1RomFlagBits,
          addPaddedAddClaim, x1, regidx_to_fin, Transpiler.ind, ZiskFv.AirsClean.Main.packFlags,
          ZiskFv.AirsClean.boolF]
      · rw [addPaddedMainPc_add, addPaddedAcceptedTrace_program] at hline
        exfalso
        have hval := congrArg (fun x : FGL => x.val) hline
        norm_num [addPaddedAcceptedTrace, addSpinProgram, addSpinJalProgramRow] at hval
  bFacts := by
    refine { h_src_reg := ?_, h_src_imm := ?_, h_program := ?_ }
    · simp [addSpinAddBits, addX1RomFlagBits, addPaddedAddClaim, x1, regidx_to_fin]
    · simp [addSpinAddBits, addX1RomFlagBits, addPaddedAddClaim, x1, regidx_to_fin]
    · intro j hline
      fin_cases j
      · simp only [addPaddedAcceptedTrace, addSpinProgram]
        norm_num [addSpinAddProgramRow, addX1ProgramRow,
          addSpinAddBits, addX1RomFlagBits,
          addPaddedAddClaim, x1, regidx_to_fin, Transpiler.ind, ZiskFv.AirsClean.Main.packFlags,
          ZiskFv.AirsClean.boolF]
      · rw [addPaddedMainPc_add, addPaddedAcceptedTrace_program] at hline
        exfalso
        have hval := congrArg (fun x : FGL => x.val) hline
        norm_num [addPaddedAcceptedTrace, addSpinProgram, addSpinJalProgramRow] at hval
  h_prog := by
    intro j hline
    change Fin 2 at j
    fin_cases j
    · simp only [addPaddedAcceptedTrace, addSpinProgram]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · simp [addSpinAddProgramRow, addX1ProgramRow, addPaddedAddClaim, x1,
          Transpiler.ind, regidx_to_fin]
      · norm_num [addSpinAddProgramRow, addX1ProgramRow, ZiskFv.AirsClean.Main.packFlags,
          addSpinAddBits, addX1RomFlagBits, ZiskFv.AirsClean.boolF]
    · rw [addPaddedMainPc_add] at hline
      rw [addPaddedAcceptedTrace_program] at hline
      norm_num [addPaddedAcceptedTrace, addSpinProgram, addSpinJalProgramRow] at hline
      exfalso
      have hval := congrArg (fun x : FGL => x.val) hline
      norm_num at hval

theorem addPaddedSuccessorRow_hasCommittedLookup :
    ∃ j : Fin addPaddedAcceptedTrace.programLength,
      ZiskFv.AirsClean.Main.romMessage
        (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          addPaddedAcceptedTrace.program addPaddedAcceptedTrace.mainTable 1) =
        addPaddedAcceptedTrace.program j := by
  exact mainRomMessage_at_eq_program addPaddedAcceptedTrace
    ⟨1, by
      rw [addPaddedAcceptedTrace_mainTable_eq]
      norm_num [addSpinMainTable, mainRowsTable, addSpinMainRows]⟩

theorem addPaddedSuccessorRow_isCommittedJal :
    ZiskFv.AirsClean.Main.romMessage
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
        addPaddedAcceptedTrace.program addPaddedAcceptedTrace.mainTable 1) =
      addPaddedAcceptedTrace.program ⟨1, by decide⟩ := by
  rw [addPaddedAcceptedTrace_program, addPaddedAcceptedTrace_mainTable_eq]
  rw [addSpinMainRowAt_one]
  rfl

private theorem addPaddedAddLaneLo
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      (field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable) 0) = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addPaddedAcceptedTrace.program
        addPaddedAcceptedTrace.mainTable) addPaddedAddIndex.val =
      lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addPaddedSailTrace addPaddedAddIndex)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addPaddedSailTrace addPaddedAddIndex) (regidx_to_fin x1) (0#64) addPaddedReadX1]
  rw [addPaddedAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable) 0 = _
  rw [h_field]
  simp [lane_lo]

private theorem addPaddedAddLaneHi
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      (field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable) 0) = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addPaddedAcceptedTrace.program
        addPaddedAcceptedTrace.mainTable) addPaddedAddIndex.val =
      lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addPaddedSailTrace addPaddedAddIndex)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addPaddedSailTrace addPaddedAddIndex) (regidx_to_fin x1) (0#64) addPaddedReadX1]
  rw [addPaddedAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
      addSpinMainTable) 0 = _
  rw [h_field]
  simp [lane_hi]

def addPaddedAddInputs :
    Inputs_add addPaddedAcceptedTrace addPaddedSailTrace addPaddedAddIndex addPaddedAddClaim where
  add_input := addSpinAddInput
  h_input_r1 := by
    simpa [addSpinAddInput, addPaddedAddClaim] using addPaddedReadX1
  h_input_r2 := by
    simpa [addSpinAddInput, addPaddedAddClaim] using addPaddedReadX1
  h_input_pc := by
    simp [addSpinAddInput, addPaddedSailTrace, addPaddedAddIndex, addSpinState, addSpinRegs, x1,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := by
    rfl
  h_pc_bridge := by
    rw [addPaddedAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addSpinProgram
          addSpinMainTable).pc 0).val = _
    simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row, addSpinAddInput]

def addPaddedProgramDecodes :
    ∀ i : Fin 1, ProgramDecode addPaddedAcceptedTrace i (addPaddedZiskStep i)
  | ⟨0, _⟩ => addPaddedAddProgramDecode

def addPaddedInputsAgree :
    ∀ i : Fin 1, InputsAgree addPaddedAcceptedTrace addPaddedSailTrace i (addPaddedZiskStep i)
  | ⟨0, _⟩ => addPaddedAddInputs

/-- The two root PC premises for this witness, from the per-row family above
    (`pcSeed_of_inputsAgree` / `inputsAgreeCore_of_inputsAgree`). -/
def addPaddedPcSeed : SegmentPcSeed addPaddedAcceptedTrace addPaddedSailTrace :=
  pcSeed_of_inputsAgree addPaddedInputsAgree

def addPaddedInputsAgreeCore :
    ∀ i : Fin 1, InputsAgreeCore addPaddedAcceptedTrace addPaddedSailTrace i (addPaddedZiskStep i) :=
  fun i => inputsAgreeCore_of_inputsAgree i (addPaddedZiskStep i) (addPaddedInputsAgree i)

def addPaddedAddOutsideDefectRegion :
    RowOutsideDefectRegion addPaddedAcceptedTrace addPaddedAddIndex
      (addPaddedZiskStep addPaddedAddIndex) := by
  unfold RowOutsideDefectRegion addPaddedZiskStep MainSequentialPcDomain mainPcVal
  rw [addPaddedMainPc_add]
  change 0 < GL_prime - 4
  norm_num

def addPaddedOutsideDefectRegion :
    ∀ i : Fin 1, RowOutsideDefectRegion addPaddedAcceptedTrace i (addPaddedZiskStep i)
  | ⟨0, _⟩ => addPaddedAddOutsideDefectRegion

/-- #330 Phase 7: each executed step's producer entry is its own row's successor `pc`. Only a
    two-row unaligned JALR lowering can break this, and only at a step that has a successor. -/
def addPaddedRowsAligned :
    StepRowsAligned addPaddedAcceptedTrace addPaddedZiskStep
      (fun i => rowDecode_of_programDecode addPaddedAcceptedTrace i (addPaddedProgramDecodes i)) := by
  intro j h
  have h' : j + 1 < 1 := h
  have hj : j < 1 - 1 := by omega
  interval_cases j <;> rfl

set_option maxHeartbeats 4000000 in
def addPaddedLaneBridge : ∀ i : Fin 1,
    LaneBridge addPaddedAcceptedTrace (addPaddedSailTrace i) i.val := by
  intro i
  fin_cases i
  constructor
  · intro r _ _ hoff
    have hre : r = regidx_to_fin x1 := by
      rw [addPaddedAcceptedTrace_mainTable_eq, addPaddedAcceptedTrace_program] at hoff
      rw [addSpinMainRowAt_zero] at hoff
      fin_cases r <;> simp [addSpinAddRow, addX1Row,
        Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
    rw [hre]
    simpa [addPaddedAddIndex] using addPaddedAddLaneLo (fun m i => m.a_0 i)
      (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
  · intro r _ _ hoff
    have hre : r = regidx_to_fin x1 := by
      rw [addPaddedAcceptedTrace_mainTable_eq, addPaddedAcceptedTrace_program] at hoff
      rw [addSpinMainRowAt_zero] at hoff
      fin_cases r <;> simp [addSpinAddRow, addX1Row,
        Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
    rw [hre]
    simpa [addPaddedAddIndex] using addPaddedAddLaneHi (fun m i => m.a_1 i)
      (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
  · intro r _ _ hoff
    have hre : r = regidx_to_fin x1 := by
      rw [addPaddedAcceptedTrace_mainTable_eq, addPaddedAcceptedTrace_program] at hoff
      rw [addSpinMainRowAt_zero] at hoff
      fin_cases r <;> simp [addSpinAddRow, addX1Row,
        Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
    rw [hre]
    simpa [addPaddedAddIndex] using addPaddedAddLaneLo (fun m i => m.b_0 i)
      (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])
  · intro r _ _ hoff
    have hre : r = regidx_to_fin x1 := by
      rw [addPaddedAcceptedTrace_mainTable_eq, addPaddedAcceptedTrace_program] at hoff
      rw [addSpinMainRowAt_zero] at hoff
      fin_cases r <;> simp [addSpinAddRow, addX1Row,
        Transpiler.wrap_to_regidx, x1, regidx_to_fin] at hoff ⊢
    rw [hre]
    simpa [addPaddedAddIndex] using addPaddedAddLaneHi (fun m i => m.b_1 i)
      (by simp [addSpinMainRowAt_zero, addSpinAddRow, addX1Row])

/-- The two root PC premises for this witness: boot agreement, and the Sail-internal retire law.
    `sailRetireChain_of_inputsAgree` builds the latter from the per-row `InputsAgree` family this
    witness already proves — no new content, and no hand-evaluated Sail execution. -/
def addPaddedPcChain : SegmentPcChain addPaddedAcceptedTrace addPaddedSailTrace addPaddedZiskStep where
  toSailRetireChain :=
    sailRetireChain_of_inputsAgree
      (fun i => rowDecode_of_programDecode addPaddedAcceptedTrace i (addPaddedProgramDecodes i))
      addPaddedInputsAgree addPaddedBootSeed addPaddedOutsideDefectRegion addPaddedLaneBridge addPaddedRowsAligned
  boot := (pcSeed_of_inputsAgree addPaddedInputsAgree).boot

theorem addPaddedRootSoundness :
    ∀ i : Fin 1, StepSound addPaddedAcceptedTrace addPaddedSailTrace i
      (addPaddedZiskStep i)
      (rowDecode_of_programDecode addPaddedAcceptedTrace i (addPaddedProgramDecodes i)) :=
  stepSound_of_programDecodes 1 addPaddedAcceptedTrace addPaddedSailTrace addPaddedZiskStep
    addPaddedProgramDecodes addPaddedInputsAgreeCore addPaddedPcChain addPaddedRowsAligned
    addPaddedBootSeed addPaddedOutsideDefectRegion addPaddedLaneBridge

theorem addPaddedAddStepSound :
    StepSound addPaddedAcceptedTrace addPaddedSailTrace addPaddedAddIndex
      (addPaddedZiskStep addPaddedAddIndex)
      (rowDecode_of_programDecode addPaddedAcceptedTrace addPaddedAddIndex
        (addPaddedProgramDecodes addPaddedAddIndex)) :=
  addPaddedRootSoundness addPaddedAddIndex

end ZiskFv.Compliance.AddSpinRootSoundness
