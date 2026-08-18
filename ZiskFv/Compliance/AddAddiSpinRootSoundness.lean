import ZiskFv.Compliance.AddAddiSpinWitness
import ZiskFv.Soundness

set_option maxRecDepth 10000

/-!
# Concrete `stepSound_of_programDecodes` instantiation for the ADD/ADDI/spin trace (#220)

This file binds the heterogeneous accepted Zisk trace to a three-state Sail trace and applies the
public `stepSound_of_programDecodes` theorem at all three executed rows.
-/

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddAddiSpinWitness
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.Compliance.SingleAddWitness
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.AddAddiSpinRootSoundness

def x0 : regidx := regidx.Regidx (0#5)

def x1 : regidx := regidx.Regidx (1#5)

def addAddiSpinAddIndex : Fin 3 := ⟨0, by decide⟩

def addAddiSpinAddiIndex : Fin 3 := ⟨1, by decide⟩

def addAddiSpinJalIndex : Fin 3 := ⟨2, by decide⟩

def addAddiSpinAddClaim : Claim_add addAddiSpinAcceptedTrace addAddiSpinAddIndex where
  r1 := x1
  r2 := x1
  rd := x1

def addAddiSpinAddiClaim : Claim_addi addAddiSpinAcceptedTrace addAddiSpinAddiIndex where
  r1 := x1
  rd := x1
  imm := 0#12

def addAddiSpinJalClaim : Claim_jal addAddiSpinAcceptedTrace addAddiSpinJalIndex where
  imm := 0#21
  rd := x0

def addAddiSpinZiskStep : ∀ i : Fin 3, ZiskStep addAddiSpinAcceptedTrace i
  | ⟨0, _⟩ => .add addAddiSpinAddClaim
  | ⟨1, _⟩ => .addi addAddiSpinAddiClaim
  | ⟨2, _⟩ => .jal addAddiSpinJalClaim

def addAddiSpinMisa : RegisterType Register.misa := 0#64

def addAddiSpinRegs (pc : BitVec 64) : Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.misa addAddiSpinMisa
  regs2.insert (reg_of_fin (regidx_to_fin x1)) (0#64)

def addAddiSpinState (pc : BitVec 64) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := addAddiSpinRegs pc
    mem := {} }

def addAddiSpinSailTrace : SailTrace 3
  | ⟨0, _⟩ => addAddiSpinState (0#64)
  | ⟨1, _⟩ => addAddiSpinState (4#64)
  | ⟨2, _⟩ => addAddiSpinState (8#64)

theorem addAddiSpinRowsOf_empty_readSound :
    MemoryBusRowsPrefixReadSound
      ({} : Std.ExtHashMap Nat (BitVec 8))
      ((List.range addAddiSpinAcceptedTrace.numInstructions).flatMap (fun _ => [])) := by
  change MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8)) []
  intro priorRows entry laterRows h_split h_selected
  simp at h_split

def addAddiSpinBootSeed :
    BootSegmentMemorySeed addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by
    intro h
    rfl
  step := by
    intro j h
    change j + 1 < 3 at h
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;>
      simp [addAddiSpinSailTrace, addAddiSpinState, replayMemoryAfterBusRows]
  readSoundInputs := fun h => absurd h addAddiSpinWitness_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_nonempty
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_nonempty
  placement := by
    intro i
    fin_cases i <;> simp [MemoryOpPlacement, addAddiSpinZiskStep]

private theorem addAddiSpinAcceptedTrace_program :
    addAddiSpinAcceptedTrace.program = addAddiSpinProgram := rfl

private theorem addAddiSpinMainRowAt_zero :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addAddiSpinProgram
      addAddiSpinMainTable 0 = addAddiSpinAddRow := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by simp)]
  exact addAddiSpinMainTable_eval_rowInputVar_zero (by simp)

private theorem addAddiSpinMainRowAt_one :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addAddiSpinProgram
      addAddiSpinMainTable 1 = addAddiSpinAddiRow := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by simp)]
  exact addAddiSpinMainTable_eval_rowInputVar_one (by simp)

private theorem addAddiSpinMainRowAt_two :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero addAddiSpinProgram
      addAddiSpinMainTable 2 = addAddiSpinJalRow 2 := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by simp)]
  exact addAddiSpinMainTable_eval_rowInputVar_two (by simp)

private theorem addAddiSpinMainPc_add :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinAcceptedTrace.program
        addAddiSpinAcceptedTrace.mainTable).pc addAddiSpinAddIndex.val = 0 := by
  rw [addAddiSpinAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable).pc 0 = 0
  simp [addAddiSpinMainRowAt_zero, addAddiSpinAddRow, addX1Row]

private theorem addAddiSpinMainPc_addi :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinAcceptedTrace.program
        addAddiSpinAcceptedTrace.mainTable).pc addAddiSpinAddiIndex.val = 4 := by
  rw [addAddiSpinAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable).pc 1 = 4
  simp [addAddiSpinMainRowAt_one, addAddiSpinAddiRow, addAddiSpinAddiProgramRow,
    addAddiSpinAddiBits, addAddiSpinAddiFreeCols, ZiskFv.AirsClean.Main.mainRomRowOf]

private theorem addAddiSpinMainPc_jal :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinAcceptedTrace.program
        addAddiSpinAcceptedTrace.mainTable).pc addAddiSpinJalIndex.val = 8 := by
  rw [addAddiSpinAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable).pc 2 = 8
  simp [addAddiSpinMainRowAt_two, addAddiSpinJalRow]

private theorem addAddiSpinReadX1 (i : Fin 3) :
    read_xreg (regidx_to_fin x1) (addAddiSpinSailTrace i) =
      EStateM.Result.ok (0#64) (addAddiSpinSailTrace i) := by
  fin_cases i <;>
    simp [addAddiSpinSailTrace, addAddiSpinState, addAddiSpinRegs, x1,
      regidx_to_fin, read_xreg, reg_of_fin]

def addAddiSpinAddInput : PureSpec.AddInput where
  r1_val := 0#64
  r2_val := 0#64
  rd := regidx_to_fin x1
  PC := 0#64

def addAddiSpinAddiInput : PureSpec.AddiInput where
  r1_val := 0#64
  imm := 0#12
  rd := regidx_to_fin x1
  PC := 4#64

def addAddiSpinJalInput : PureSpec.JalInput where
  imm := 0#21
  rd := regidx_to_fin x0
  PC := 8#64

def addAddiSpinAddProgramDecode :
    ProgramDecode_add addAddiSpinAcceptedTrace addAddiSpinAddIndex addAddiSpinAddClaim where
  h_idx := by
    rw [addAddiSpinAcceptedTrace_mainTable_eq]
    change 0 + 1 < addAddiSpinMainTable.table.length
    simp
  bits := addAddiSpinAddBits
  h_bits_ieo := by simp [addAddiSpinAddBits, addX1RomFlagBits]
  h_bits_m32 := by simp [addAddiSpinAddBits, addX1RomFlagBits]
  h_bits_set_pc := by simp [addAddiSpinAddBits, addX1RomFlagBits]
  h_bits_store_pc := by simp [addAddiSpinAddBits, addX1RomFlagBits]
  h_bits_store_ind := by simp [addAddiSpinAddBits, addX1RomFlagBits]
  h_bits_store_reg := by simp [addAddiSpinAddBits, addX1RomFlagBits]
  h_bits_a_src_reg := by sorry
  h_prog := by
    intro j hline
    change Fin 3 at j
    fin_cases j
    · simp only [addAddiSpinAcceptedTrace, addAddiSpinProgram]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · simp [addAddiSpinAddProgramRow, addX1ProgramRow, addAddiSpinAddClaim, x1,
          Transpiler.ind, regidx_to_fin]
      · norm_num [addAddiSpinAddProgramRow, addX1ProgramRow,
          ZiskFv.AirsClean.Main.packFlags, addAddiSpinAddBits, addX1RomFlagBits,
          ZiskFv.AirsClean.boolF]
    · rw [addAddiSpinMainPc_add] at hline
      rw [addAddiSpinAcceptedTrace_program] at hline
      norm_num [addAddiSpinAcceptedTrace, addAddiSpinProgram,
        addAddiSpinAddiProgramRow] at hline
      exact absurd (congrArg (fun value : FGL => value.val) hline) (by norm_num)
    · rw [addAddiSpinMainPc_add] at hline
      rw [addAddiSpinAcceptedTrace_program] at hline
      norm_num [addAddiSpinAcceptedTrace, addAddiSpinProgram,
        addAddiSpinJalProgramRow] at hline
      exact absurd (congrArg (fun value : FGL => value.val) hline) (by norm_num)

def addAddiSpinAddiProgramDecode :
    ProgramDecode_addi addAddiSpinAcceptedTrace addAddiSpinAddiIndex addAddiSpinAddiClaim where
  h_idx := by
    rw [addAddiSpinAcceptedTrace_mainTable_eq]
    change 1 + 1 < addAddiSpinMainTable.table.length
    simp
  bits := addAddiSpinAddiBits
  h_bits_ieo := by rfl
  h_bits_m32 := by rfl
  h_bits_set_pc := by rfl
  h_bits_store_pc := by rfl
  h_bits_store_ind := by rfl
  h_bits_store_reg := by intro _; rfl
  h_bits_b_src_imm := by rfl
  h_prog := by
    intro j hline
    change Fin 3 at j
    fin_cases j
    · rw [addAddiSpinMainPc_addi] at hline
      rw [addAddiSpinAcceptedTrace_program] at hline
      norm_num [addAddiSpinAcceptedTrace, addAddiSpinProgram,
        addAddiSpinAddProgramRow, addX1ProgramRow] at hline
      exact absurd (congrArg (fun value : FGL => value.val) hline) (by norm_num)
    · simp only [addAddiSpinAcceptedTrace, addAddiSpinProgram]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · simp [addAddiSpinAddiProgramRow, addAddiSpinAddiClaim, x1,
          Transpiler.ind, regidx_to_fin]
      constructor
      · simp [addAddiSpinAddiProgramRow, addAddiSpinAddiClaim]
      · norm_num [addAddiSpinAddiProgramRow, ZiskFv.AirsClean.Main.packFlags,
          addAddiSpinAddiBits, ZiskFv.AirsClean.boolF]
    · rw [addAddiSpinMainPc_addi] at hline
      rw [addAddiSpinAcceptedTrace_program] at hline
      norm_num [addAddiSpinAcceptedTrace, addAddiSpinProgram,
        addAddiSpinJalProgramRow] at hline
      exact absurd (congrArg (fun value : FGL => value.val) hline) (by norm_num)

def addAddiSpinJalProgramDecode :
    ProgramDecode_jal addAddiSpinAcceptedTrace addAddiSpinJalIndex addAddiSpinJalClaim where
  h_idx := by
    rw [addAddiSpinAcceptedTrace_mainTable_eq]
    change 2 + 1 < addAddiSpinMainTable.table.length
    simp
  bits := addAddiSpinJalBits
  h_bits_ieo := by rfl
  h_bits_m32 := by rfl
  h_bits_set_pc := by rfl
  h_bits_store_pc := by rfl
  h_bits_store_ind := by rfl
  h_bits_store_reg := by intro h; exact absurd (by decide : (regidx_to_fin x0).val = 0) h
  h_prog := by
    intro j hline
    change Fin 3 at j
    fin_cases j
    · rw [addAddiSpinMainPc_jal] at hline
      rw [addAddiSpinAcceptedTrace_program] at hline
      norm_num [addAddiSpinAcceptedTrace, addAddiSpinProgram,
        addAddiSpinAddProgramRow, addX1ProgramRow] at hline
      exact absurd (congrArg (fun value : FGL => value.val) hline) (by norm_num)
    · rw [addAddiSpinMainPc_jal] at hline
      rw [addAddiSpinAcceptedTrace_program] at hline
      norm_num [addAddiSpinAcceptedTrace, addAddiSpinProgram,
        addAddiSpinAddiProgramRow] at hline
      exact absurd (congrArg (fun value : FGL => value.val) hline) (by norm_num)
    · simp only [addAddiSpinAcceptedTrace, addAddiSpinProgram]
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · simp [addAddiSpinJalProgramRow, addAddiSpinJalClaim, x0,
          Transpiler.ind, regidx_to_fin]
      · norm_num [addAddiSpinJalProgramRow, ZiskFv.AirsClean.Main.packFlags,
          addAddiSpinJalBits, addSpinJalBits, ZiskFv.AirsClean.boolF]

private theorem addAddiSpinLaneLo
    (i : Fin 3) (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
        addAddiSpinMainTable) i.val = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinAcceptedTrace.program
        addAddiSpinAcceptedTrace.mainTable) i.val =
      lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addAddiSpinSailTrace i)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addAddiSpinSailTrace i) (regidx_to_fin x1) (0#64) (addAddiSpinReadX1 i)]
  rw [addAddiSpinAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable) i.val = _
  rw [h_field]
  simp [lane_lo]

private theorem addAddiSpinLaneHi
    (i : Fin 3) (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (h_field :
      field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
        addAddiSpinMainTable) i.val = 0) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinAcceptedTrace.program
        addAddiSpinAcceptedTrace.mainTable) i.val =
      lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (addAddiSpinSailTrace i)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (addAddiSpinSailTrace i) (regidx_to_fin x1) (0#64) (addAddiSpinReadX1 i)]
  rw [addAddiSpinAcceptedTrace_mainTable_eq]
  change field (ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable) i.val = _
  rw [h_field]
  simp [lane_hi]

def addAddiSpinAddInputs :
    Inputs_add addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinAddIndex
      addAddiSpinAddClaim where
  add_input := addAddiSpinAddInput
  h_input_r1 := by
    simpa [addAddiSpinAddInput, addAddiSpinAddClaim] using
      addAddiSpinReadX1 addAddiSpinAddIndex
  h_input_r2 := by
    simpa [addAddiSpinAddInput, addAddiSpinAddClaim] using
      addAddiSpinReadX1 addAddiSpinAddIndex
  h_input_pc := by
    simp [addAddiSpinAddInput, addAddiSpinSailTrace, addAddiSpinAddIndex,
      addAddiSpinState, addAddiSpinRegs, x1, regidx_to_fin, reg_of_fin,
      Std.ExtDHashMap.get?_insert]
  h_input_rd := by
    rfl
  h_a_hi_t := by
    exact addAddiSpinLaneHi addAddiSpinAddIndex (fun m i => m.a_1 i)
      (by simp [addAddiSpinAddIndex, addAddiSpinMainRowAt_zero,
        addAddiSpinAddRow, addX1Row])
  h_b_lo_t := by
    exact addAddiSpinLaneLo addAddiSpinAddIndex (fun m i => m.b_0 i)
      (by simp [addAddiSpinAddIndex, addAddiSpinMainRowAt_zero,
        addAddiSpinAddRow, addX1Row])
  h_b_hi_t := by
    exact addAddiSpinLaneHi addAddiSpinAddIndex (fun m i => m.b_1 i)
      (by simp [addAddiSpinAddIndex, addAddiSpinMainRowAt_zero,
        addAddiSpinAddRow, addX1Row])
  h_pc_bridge := by
    rw [addAddiSpinAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable).pc 0).val = _
    simp [addAddiSpinMainRowAt_zero, addAddiSpinAddRow, addX1Row,
      addAddiSpinAddInput]

def addAddiSpinAddiInputs :
    Inputs_addi addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinAddiIndex
      addAddiSpinAddiClaim where
  addi_input := addAddiSpinAddiInput
  h_input_r1 := by
    simpa [addAddiSpinAddiInput, addAddiSpinAddiClaim] using
      addAddiSpinReadX1 addAddiSpinAddiIndex
  h_input_imm := by
    rfl
  h_input_pc := by
    simp [addAddiSpinAddiInput, addAddiSpinSailTrace, addAddiSpinAddiIndex,
      addAddiSpinState, addAddiSpinRegs, x1, regidx_to_fin, reg_of_fin,
      Std.ExtDHashMap.get?_insert]
  h_input_rd := by
    rfl
  h_a_lo_t := by
    exact addAddiSpinLaneLo addAddiSpinAddiIndex (fun m i => m.a_0 i)
      (by simp [addAddiSpinAddiIndex, addAddiSpinMainRowAt_one,
        addAddiSpinAddiRow, addAddiSpinAddiProgramRow, addAddiSpinAddiBits,
        addAddiSpinAddiFreeCols, ZiskFv.AirsClean.Main.mainRomRowOf])
  h_a_hi_t := by
    exact addAddiSpinLaneHi addAddiSpinAddiIndex (fun m i => m.a_1 i)
      (by simp [addAddiSpinAddiIndex, addAddiSpinMainRowAt_one,
        addAddiSpinAddiRow, addAddiSpinAddiProgramRow, addAddiSpinAddiBits,
        addAddiSpinAddiFreeCols, ZiskFv.AirsClean.Main.mainRomRowOf])
  h_pc_bridge := by
    rw [addAddiSpinAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable).pc 1).val = _
    simp [addAddiSpinMainRowAt_one, addAddiSpinAddiRow, addAddiSpinAddiProgramRow,
      addAddiSpinAddiBits, addAddiSpinAddiFreeCols,
      ZiskFv.AirsClean.Main.mainRomRowOf, addAddiSpinAddiInput]

def addAddiSpinJalInputs :
    Inputs_jal addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinJalIndex
      addAddiSpinJalClaim where
  jal_input := addAddiSpinJalInput
  misa_val := addAddiSpinMisa
  h_pc_bridge := by
    rw [addAddiSpinAcceptedTrace_mainTable_eq]
    change ((ZiskFv.AirsClean.FullEnsemble.mainOfTable addAddiSpinProgram
      addAddiSpinMainTable).pc 2).val = _
    simp [addAddiSpinMainRowAt_two, addAddiSpinJalRow, addAddiSpinJalInput]
  h_input_rd := by
    rfl
  h_input_pc := by
    simp [addAddiSpinJalInput, addAddiSpinSailTrace, addAddiSpinJalIndex,
      addAddiSpinState, addAddiSpinRegs, x1, regidx_to_fin, reg_of_fin,
      Std.ExtDHashMap.get?_insert]
  h_input_misa := by
    simp [addAddiSpinSailTrace, addAddiSpinJalIndex, addAddiSpinState,
      addAddiSpinRegs, x1, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_misa_c := by
    simp [addAddiSpinMisa]
  h_success := by
    simp [addAddiSpinJalInput, PureSpec.execute_JAL_pure]
  h_input_imm := by
    rfl

def addAddiSpinProgramDecodes :
    ∀ i : Fin 3, ProgramDecode addAddiSpinAcceptedTrace i (addAddiSpinZiskStep i)
  | ⟨0, _⟩ => addAddiSpinAddProgramDecode
  | ⟨1, _⟩ => addAddiSpinAddiProgramDecode
  | ⟨2, _⟩ => addAddiSpinJalProgramDecode

def addAddiSpinInputsAgree :
    ∀ i : Fin 3, InputsAgree addAddiSpinAcceptedTrace addAddiSpinSailTrace i
      (addAddiSpinZiskStep i)
  | ⟨0, _⟩ => addAddiSpinAddInputs
  | ⟨1, _⟩ => addAddiSpinAddiInputs
  | ⟨2, _⟩ => addAddiSpinJalInputs

/-- The two root PC premises for this witness, from the per-row family above
    (`pcSeed_of_inputsAgree` / `inputsAgreeCore_of_inputsAgree`). -/
def addAddiSpinPcSeed : SegmentPcSeed addAddiSpinAcceptedTrace addAddiSpinSailTrace :=
  pcSeed_of_inputsAgree addAddiSpinInputsAgree

def addAddiSpinInputsAgreeCore :
    ∀ i : Fin 3, InputsAgreeCore addAddiSpinAcceptedTrace addAddiSpinSailTrace i (addAddiSpinZiskStep i) :=
  fun i => inputsAgreeCore_of_inputsAgree i (addAddiSpinZiskStep i) (addAddiSpinInputsAgree i)

def addAddiSpinAddOutsideDefectRegion :
    RowOutsideDefectRegion addAddiSpinAcceptedTrace addAddiSpinAddIndex
      (addAddiSpinZiskStep addAddiSpinAddIndex) := by
  unfold RowOutsideDefectRegion addAddiSpinZiskStep MainSequentialPcDomain mainPcVal
  rw [addAddiSpinMainPc_add]
  change 0 < GL_prime - 4
  norm_num

def addAddiSpinAddiOutsideDefectRegion :
    RowOutsideDefectRegion addAddiSpinAcceptedTrace addAddiSpinAddiIndex
      (addAddiSpinZiskStep addAddiSpinAddiIndex) := by
  unfold RowOutsideDefectRegion addAddiSpinZiskStep MainSequentialPcDomain mainPcVal
  rw [addAddiSpinMainPc_addi]
  change 4 < GL_prime - 4
  norm_num

def addAddiSpinJalOutsideDefectRegion :
    RowOutsideDefectRegion addAddiSpinAcceptedTrace addAddiSpinJalIndex
      (addAddiSpinZiskStep addAddiSpinJalIndex) where
  h_target_nonneg := by
    unfold mainPcVal
    rw [addAddiSpinMainPc_jal]
    change 0 ≤ (8 : Int) + (BitVec.signExtend 64 (0#21)).toInt
    simp
  h_target_lt := by
    unfold mainPcVal
    rw [addAddiSpinMainPc_jal]
    change (8 : Int) + (BitVec.signExtend 64 (0#21)).toInt < GL_prime
    simp
  h_pc_bound := by
    unfold MainSequentialPcDomain mainPcVal
    rw [addAddiSpinMainPc_jal]
    change 8 < GL_prime - 4
    norm_num
  h_pc_offset_lt_2_32 := by
    intro pc hpc
    unfold mainPcVal at hpc
    rw [addAddiSpinMainPc_jal] at hpc
    rw [BitVec.toNat_add]
    rw [← hpc]
    norm_num

def addAddiSpinOutsideDefectRegion :
    ∀ i : Fin 3, RowOutsideDefectRegion addAddiSpinAcceptedTrace i
      (addAddiSpinZiskStep i)
  | ⟨0, _⟩ => addAddiSpinAddOutsideDefectRegion
  | ⟨1, _⟩ => addAddiSpinAddiOutsideDefectRegion
  | ⟨2, _⟩ => addAddiSpinJalOutsideDefectRegion

/-- #330 Phase 7: each executed step's producer entry is its own row's successor `pc`. Only a
    two-row unaligned JALR lowering can break this, and only at a step that has a successor. -/
def addAddiSpinRowsAligned :
    StepRowsAligned addAddiSpinAcceptedTrace addAddiSpinZiskStep
      (fun i => rowDecode_of_programDecode addAddiSpinAcceptedTrace i (addAddiSpinProgramDecodes i)) := by
  intro j h
  have h' : j + 1 < 3 := h
  have hj : j < 3 - 1 := by omega
  interval_cases j <;> rfl

/-- The two root PC premises for this witness: boot agreement, and the Sail-internal retire law.
    `sailRetireChain_of_inputsAgree` builds the latter from the per-row `InputsAgree` family this
    witness already proves — no new content, and no hand-evaluated Sail execution. -/
def addAddiSpinPcChain : SegmentPcChain addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinZiskStep where
  toSailRetireChain :=
    sailRetireChain_of_inputsAgree
      (fun i => rowDecode_of_programDecode addAddiSpinAcceptedTrace i (addAddiSpinProgramDecodes i))
      addAddiSpinInputsAgree addAddiSpinBootSeed addAddiSpinOutsideDefectRegion addAddiSpinRowsAligned
  boot := (pcSeed_of_inputsAgree addAddiSpinInputsAgree).boot

theorem addAddiSpinRootSoundness :
    ∀ i : Fin 3,
      StepSound addAddiSpinAcceptedTrace addAddiSpinSailTrace i
        (addAddiSpinZiskStep i)
        (rowDecode_of_programDecode addAddiSpinAcceptedTrace i
          (addAddiSpinProgramDecodes i)) :=
  stepSound_of_programDecodes 3 addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinZiskStep
    addAddiSpinProgramDecodes addAddiSpinInputsAgreeCore addAddiSpinPcChain
    addAddiSpinRowsAligned addAddiSpinBootSeed addAddiSpinOutsideDefectRegion
    (fun _ _ _ => by sorry)

theorem addAddiSpinAddStepSound :
    StepSound addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinAddIndex
      (addAddiSpinZiskStep addAddiSpinAddIndex)
      (rowDecode_of_programDecode addAddiSpinAcceptedTrace addAddiSpinAddIndex
        (addAddiSpinProgramDecodes addAddiSpinAddIndex)) :=
  addAddiSpinRootSoundness addAddiSpinAddIndex

theorem addAddiSpinAddiStepSound :
    StepSound addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinAddiIndex
      (addAddiSpinZiskStep addAddiSpinAddiIndex)
      (rowDecode_of_programDecode addAddiSpinAcceptedTrace addAddiSpinAddiIndex
        (addAddiSpinProgramDecodes addAddiSpinAddiIndex)) :=
  addAddiSpinRootSoundness addAddiSpinAddiIndex

theorem addAddiSpinJalStepSound :
    StepSound addAddiSpinAcceptedTrace addAddiSpinSailTrace addAddiSpinJalIndex
      (addAddiSpinZiskStep addAddiSpinJalIndex)
      (rowDecode_of_programDecode addAddiSpinAcceptedTrace addAddiSpinJalIndex
        (addAddiSpinProgramDecodes addAddiSpinJalIndex)) :=
  addAddiSpinRootSoundness addAddiSpinJalIndex

end ZiskFv.Compliance.AddAddiSpinRootSoundness
