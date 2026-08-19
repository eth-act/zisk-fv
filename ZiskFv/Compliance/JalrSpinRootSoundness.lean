import ZiskFv.Compliance.JalrSpinWitness
import ZiskFv.Soundness

set_option maxRecDepth 10000

/-!
# Concrete `stepSound_of_programDecodes` instantiation for unaligned JALR lowering

The architectural trace executes `ADDI x1,x0,2`, then `JALR x2,2(x1)`.
The JALR is represented by adjacent physical Main rows `ADD; AND`; the
terminal AND jumps back to the physical successor at architectural PC 4.
-/

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.JalrSpinWitness
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.JalrSpinRootSoundness

def x0 : regidx := regidx.Regidx (0#5)
def x1 : regidx := regidx.Regidx (1#5)
def x2 : regidx := regidx.Regidx (2#5)

def setupIndex : Fin 2 := ⟨0, by decide⟩
def jalrIndex : Fin 2 := ⟨1, by decide⟩

def setupClaim : Claim_addi jalrAcceptedTrace setupIndex where
  r1 := x0
  rd := x1
  imm := 2#12

def jalrClaim : Claim_jalr jalrAcceptedTrace jalrIndex where
  imm := 2#12
  rs1 := x1
  rd := x2
  offset_bv := 0#64

def jalrSpinZiskStep : ∀ i : Fin 2, ZiskStep jalrAcceptedTrace i
  | ⟨0, _⟩ => .addi setupClaim
  | ⟨1, _⟩ => .jalr jalrClaim

def misa : RegisterType Register.misa := 0#64
def mseccfg : RegisterType Register.mseccfg := 0#64

def regs (pc x1Value x2Value : BitVec 64) :
    Std.ExtDHashMap Register RegisterType :=
  let regs0 :=
    (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.cur_privilege Privilege.Machine
  let regs3 := regs2.insert Register.misa misa
  let regs4 := regs3.insert Register.mseccfg mseccfg
  let regs5 := regs4.insert (reg_of_fin (regidx_to_fin x1)) x1Value
  regs5.insert (reg_of_fin (regidx_to_fin x2)) x2Value

def state (pc x1Value x2Value : BitVec 64) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := regs pc x1Value x2Value
    mem := {} }

def sailTrace : SailTrace 2
  | ⟨0, _⟩ => state (0#64) (0#64) (0#64)
  | ⟨1, _⟩ => state (4#64) (2#64) (0#64)

def bootSeed :
    BootSegmentMemorySeed jalrAcceptedTrace sailTrace jalrSpinZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := by
    intro h
    rfl
  step := by
    intro j h
    change j + 1 < 2 at h
    have : j = 0 := by omega
    subst j
    simp [sailTrace, state, replayMemoryAfterBusRows]
  readSoundInputs := fun h => absurd h jalrWitness_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_nonempty
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_nonempty
  placement := by
    intro i
    fin_cases i <;> simp [MemoryOpPlacement, jalrSpinZiskStep]

def setupMainIndex : Fin jalrAcceptedTrace.mainTable.table.length :=
  Fin.cast
    (congrArg (fun table : Air.Flat.Table FGL => table.table.length)
      jalrAcceptedTrace_mainTable_eq).symm
    (⟨0, by decide⟩ : Fin jalrMainTable.table.length)

def startMainIndex : Fin jalrAcceptedTrace.mainTable.table.length :=
  Fin.cast
    (congrArg (fun table : Air.Flat.Table FGL => table.table.length)
      jalrAcceptedTrace_mainTable_eq).symm
    (⟨1, by decide⟩ : Fin jalrMainTable.table.length)

def finishMainIndex : Fin jalrAcceptedTrace.mainTable.table.length :=
  Fin.cast
    (congrArg (fun table : Air.Flat.Table FGL => table.table.length)
      jalrAcceptedTrace_mainTable_eq).symm
    (⟨2, by decide⟩ : Fin jalrMainTable.table.length)

@[simp] theorem setupMainIndex_val : setupMainIndex.val = 0 := by
  simp [setupMainIndex]

@[simp] theorem startMainIndex_val : startMainIndex.val = 1 := by
  simp [startMainIndex]

@[simp] theorem finishMainIndex_val : finishMainIndex.val = 2 := by
  simp [finishMainIndex]

private theorem setupMainGet :
    jalrAcceptedTrace.mainTable.table.get setupMainIndex =
      jalrMainTable.table.get (⟨0, by decide⟩ : Fin jalrMainTable.table.length) := by
  simp [setupMainIndex, jalrAcceptedTrace_mainTable_eq]

private theorem startMainGet :
    jalrAcceptedTrace.mainTable.table.get startMainIndex =
      jalrMainTable.table.get (⟨1, by decide⟩ : Fin jalrMainTable.table.length) := by
  simp [startMainIndex, jalrAcceptedTrace_mainTable_eq]

private theorem finishMainGet :
    jalrAcceptedTrace.mainTable.table.get finishMainIndex =
      jalrMainTable.table.get (⟨2, by decide⟩ : Fin jalrMainTable.table.length) := by
  simp [finishMainIndex, jalrAcceptedTrace_mainTable_eq]

private theorem mainAt_setup :
    ZiskFv.Compliance.mainRowWithRomAt jalrAcceptedTrace setupMainIndex =
      jalrSetupRow := by
  unfold ZiskFv.Compliance.mainRowWithRomAt
  rw [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get]
  rw [setupMainGet]
  rw [jalrAcceptedTrace_mainTable_eq]
  convert jalrMainTable_evalAt (⟨0, by decide⟩ : Fin jalrMainTable.length) using 1 <;>
    simp [jalrMainRows]

private theorem mainAt_start :
    ZiskFv.Compliance.mainRowWithRomAt jalrAcceptedTrace startMainIndex =
      jalrAddRow := by
  unfold ZiskFv.Compliance.mainRowWithRomAt
  rw [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get]
  rw [startMainGet]
  rw [jalrAcceptedTrace_mainTable_eq]
  convert jalrMainTable_evalAt (⟨1, by decide⟩ : Fin jalrMainTable.length) using 1 <;>
    simp [jalrMainRows]

private theorem mainAt_finish :
    ZiskFv.Compliance.mainRowWithRomAt jalrAcceptedTrace finishMainIndex =
      jalrAndRow := by
  unfold ZiskFv.Compliance.mainRowWithRomAt
  rw [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get]
  rw [finishMainGet]
  rw [jalrAcceptedTrace_mainTable_eq]
  convert jalrMainTable_evalAt (⟨2, by decide⟩ : Fin jalrMainTable.length) using 1 <;>
    simp [jalrMainRows]

@[simp] private theorem mainRawAt_setup :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 0 = jalrSetupRow := by
  simpa [ZiskFv.Compliance.mainRowWithRomAt, setupMainIndex] using mainAt_setup

@[simp] private theorem mainRawAt_start :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 1 = jalrAddRow := by
  simpa [ZiskFv.Compliance.mainRowWithRomAt, startMainIndex] using mainAt_start

@[simp] private theorem mainRawAt_finish :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 2 = jalrAndRow := by
  simpa [ZiskFv.Compliance.mainRowWithRomAt, finishMainIndex] using mainAt_finish

@[simp] private theorem jalrAcceptedTrace_numInstructions :
    jalrAcceptedTrace.numInstructions = 2 := rfl

private theorem setupMainPc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable jalrAcceptedTrace.program
      jalrAcceptedTrace.mainTable).pc 0 = 0 := by
  change
    (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 0).core.pc = 0
  rw [mainRawAt_setup]
  simp [jalrSetupRow, jalrSetupRowWithLast, jalrSetupRowTemplate,
    jalrSetupProgramRow, jalrSetupBits, ZiskFv.AirsClean.Main.mainRomRowOf]

private theorem jalrMainPc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable jalrAcceptedTrace.program
      jalrAcceptedTrace.mainTable).pc 1 = 4 := by
  change
    (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 1).core.pc = 4
  rw [mainRawAt_start]
  simp [jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
    jalrAddProgramRow, jalrAddBits, ZiskFv.AirsClean.Main.mainRomRowOf]

private theorem jalrAndMainPc :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable jalrAcceptedTrace.program
      jalrAcceptedTrace.mainTable).pc 2 = 5 := by
  change
    (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 2).core.pc = 5
  rw [mainRawAt_finish]
  simp [jalrAndRow, jalrAndRowTemplate,
    jalrAndProgramRow, jalrAndBits, ZiskFv.AirsClean.Main.mainRomRowOf]

/-- Committed-program decode evidence for the unaligned JALR lowering.

Both committed lines are supplied — the `OP_ADD` at `pc 4` (the architectural
row) and its `OP_AND` successor at `pc 5` — and `rowDecode_of_programDecode`
DERIVES `Decode_jalr` from them via `Decode_jalr_unaligned_of_program`. The
concrete `Decode_jalr` is no longer built by hand here: only the Main-core pins
that are not ROM-message slots (`flag`, the `a`-lane mask, `c_1`, the
`jmp_offset1` bridge and its bounds) remain stated against the witness rows. -/
def jalrProgramDecode :
    ProgramDecode_jalr jalrAcceptedTrace jalrIndex jalrClaim :=
  .unaligned
    { h_offset_zero := rfl
      h_idx2 := by
        simp [jalrIndex, jalrAcceptedTrace_mainTable_eq, jalrMainTable,
          ZiskFv.Compliance.AddSpinWitness.mainRowsTable, jalrMainRows]
      h_flag_add := by
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 1).core.flag = 0
        rw [mainRawAt_start]
        rfl
      h_flag := by
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 2).core.flag = 0
        rw [mainRawAt_finish]
        rfl
      h_a_mask_lo := by
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 2).core.a_0
            = 4294967294
        rw [mainRawAt_finish]
        rfl
      h_a_mask_hi := by
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 2).core.a_1
            = 4294967295
        rw [mainRawAt_finish]
        rfl
      h_c1_zero := by
        change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
          jalrAcceptedTrace.program jalrAcceptedTrace.mainTable 2).core.c_1 = 0
        rw [mainRawAt_finish]
        rfl
      h_offset_even := by simp [jalrClaim]
      h_target_nonneg := by
        norm_num [jalrIndex, jalrClaim, jalrAndProgramRow, jalrAndBits,
          ZiskFv.AirsClean.FullEnsemble.mainOfTable, jalrAndRow,
          jalrAndRowWithLast, jalrAndRowTemplate,
          ZiskFv.AirsClean.Main.mainRomRowOf]
      h_target_lt := by
        norm_num [jalrIndex, jalrClaim, jalrAndProgramRow, jalrAndBits,
          ZiskFv.AirsClean.FullEnsemble.mainOfTable, jalrAndRow,
          jalrAndRowWithLast, jalrAndRowTemplate,
          ZiskFv.AirsClean.Main.mainRomRowOf]
      addBits := jalrAddBits
      h_add_ieo := rfl
      h_add_m32 := rfl
      h_add_set_pc := rfl
      h_add_a_src_imm := rfl
      h_add_b_src_imm := rfl
      h_add_b_src_reg := rfl
      andBits := jalrAndBits
      h_and_ieo := rfl
      h_and_m32 := rfl
      h_and_set_pc := rfl
      h_and_store_pc := rfl
      h_and_store_ind := rfl
      h_and_b_src_imm := rfl
      h_and_b_src_mem := rfl
      h_and_b_src_ind := rfl
      h_and_b_src_reg := rfl
      h_prog_add := by
        intro j hline
        have hpc : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
            jalrAcceptedTrace.program jalrAcceptedTrace.mainTable).pc
              jalrIndex.val = 4 := jalrMainPc
        rw [hpc] at hline
        fin_cases j
        · exfalso
          have hfalse : (0 : FGL) = 4 := by
            simpa [jalrAcceptedTrace, jalrProgram, jalrSetupProgramRow] using hline
          have := congrArg Fin.val hfalse
          norm_num at this
        · simp [jalrAcceptedTrace, jalrProgram, jalrAddProgramRow, jalrClaim]
        · exfalso
          have hfalse : (5 : FGL) = 4 := by
            simpa [jalrAcceptedTrace, jalrProgram, jalrAndProgramRow] using hline
          have := congrArg Fin.val hfalse
          norm_num at this
      h_prog_and := by
        intro j hline
        have hpc : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
            jalrAcceptedTrace.program jalrAcceptedTrace.mainTable).pc
              (jalrIndex.val + 1) = 5 := jalrAndMainPc
        rw [hpc] at hline
        fin_cases j
        · exfalso
          have hfalse : (0 : FGL) = 5 := by
            simpa [jalrAcceptedTrace, jalrProgram, jalrSetupProgramRow] using hline
          have := congrArg Fin.val hfalse
          norm_num at this
        · exfalso
          have hfalse : (4 : FGL) = 5 := by
            simpa [jalrAcceptedTrace, jalrProgram, jalrAddProgramRow] using hline
          have := congrArg Fin.val hfalse
          norm_num at this
        · simp [jalrAcceptedTrace, jalrProgram, jalrAndProgramRow, jalrClaim,
            x2, Transpiler.ind, regidx_to_fin] }

-- The setup decode and both input-agreement bundles follow the established
-- concrete ADDI/JALR constructors; they are stated separately so compilation
-- checks every remaining field rather than hiding it behind a helper.

def setupInput : PureSpec.AddiInput where
  r1_val := 0#64
  imm := 2#12
  rd := regidx_to_fin x1
  PC := 0#64

def jalrInput : PureSpec.JalrInput where
  imm := 2#12
  rs1_val := 2#64
  rd := regidx_to_fin x2
  PC := 4#64

def setupProgramDecode :
    ProgramDecode_addi jalrAcceptedTrace setupIndex setupClaim where
  h_idx := by
    rw [jalrAcceptedTrace_mainTable_eq]
    simp [setupIndex, jalrMainTable,
      ZiskFv.Compliance.AddSpinWitness.mainRowsTable, jalrMainRows]
  bits := jalrSetupBits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_b_src_imm := rfl
  h_prog := by
    intro j hline
    fin_cases j
    · simp [jalrAcceptedTrace, jalrProgram, jalrSetupProgramRow, setupClaim,
        x0, x1, Transpiler.ind, regidx_to_fin,
        ZiskFv.AirsClean.Main.packFlags, jalrSetupBits,
        ZiskFv.AirsClean.boolF]
    · change (jalrAcceptedTrace.program
          (⟨1, by norm_num [jalrAcceptedTrace]⟩ :
            Fin jalrAcceptedTrace.programLength)).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable jalrAcceptedTrace.program
          jalrAcceptedTrace.mainTable).pc 0 at hline
      rw [setupMainPc] at hline
      exfalso
      have hfalse : (4 : FGL) = 0 := by
        simpa [jalrAcceptedTrace, jalrProgram, jalrAddProgramRow] using hline
      have := congrArg Fin.val hfalse
      norm_num at this
    · change (jalrAcceptedTrace.program
          (⟨2, by norm_num [jalrAcceptedTrace]⟩ :
            Fin jalrAcceptedTrace.programLength)).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable jalrAcceptedTrace.program
          jalrAcceptedTrace.mainTable).pc 0 at hline
      rw [setupMainPc] at hline
      exfalso
      have hfalse : (5 : FGL) = 0 := by
        simpa [jalrAcceptedTrace, jalrProgram, jalrAndProgramRow] using hline
      have := congrArg Fin.val hfalse
      norm_num at this

private theorem readX0_setup :
    read_xreg (regidx_to_fin x0) (sailTrace setupIndex) =
      EStateM.Result.ok (0#64) (sailTrace setupIndex) := by
  simp [sailTrace, setupIndex, state, regs, x0, regidx_to_fin, read_xreg,
    reg_of_fin]

private theorem readX1_jalr :
    read_xreg (regidx_to_fin x1) (sailTrace jalrIndex) =
      EStateM.Result.ok (2#64) (sailTrace jalrIndex) := by
  simp [sailTrace, jalrIndex, state, regs, x1, x2, regidx_to_fin, read_xreg,
    reg_of_fin, Sail.readReg, Std.ExtDHashMap.get?_insert]

def setupInputs :
    Inputs_addi jalrAcceptedTrace sailTrace setupIndex setupClaim where
  addi_input := setupInput
  h_input_r1 := by simpa [setupInput, setupClaim] using readX0_setup
  h_input_imm := rfl
  h_input_pc := by
    simp [setupInput, sailTrace, setupIndex, state, regs, x1, x2,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := rfl
  h_pc_bridge := by
    norm_num [setupIndex, setupMainPc, setupInput]

def jalrInputs :
    Inputs_jalr jalrAcceptedTrace sailTrace jalrIndex jalrClaim where
  jalr_input := jalrInput
  misa_val := misa
  mseccfg := mseccfg
  h_rs1_start := by
    norm_num [jalrIndex, jalrInput,
      ZiskFv.AirsClean.FullEnsemble.mainOfTable, mainAt_start,
      jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate, jalrAddProgramRow,
      jalrAddBits, ZiskFv.AirsClean.Main.mainRomRowOf]
  h_input_rd := rfl
  h_input_pc := by
    simp [jalrInput, sailTrace, jalrIndex, state, regs, x1, x2,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_pc_bridge := by
    norm_num [jalrIndex, jalrMainPc, jalrInput]
  h_input_misa := by
    simp [sailTrace, jalrIndex, state, regs, x1, x2,
      regidx_to_fin, reg_of_fin, misa, Std.ExtDHashMap.get?_insert]
  h_misa_c := by simp [misa]
  h_success := by simp [jalrInput, PureSpec.execute_JALR_pure]
  h_input_imm := rfl
  h_input_rs1 := by simpa [jalrInput, jalrClaim] using readX1_jalr
  h_cur_privilege := by
    simp [sailTrace, jalrIndex, state, regs, x1, x2,
      regidx_to_fin, reg_of_fin, Sail.readReg, Std.ExtDHashMap.get?_insert]
  h_mseccfg := by
    simp [sailTrace, jalrIndex, state, regs, x1, x2, mseccfg,
      regidx_to_fin, reg_of_fin, Sail.readReg, Std.ExtDHashMap.get?_insert]

def programDecodes :
    ∀ i : Fin 2, ProgramDecode jalrAcceptedTrace i (jalrSpinZiskStep i)
  | ⟨0, _⟩ => setupProgramDecode
  | ⟨1, _⟩ => jalrProgramDecode

def inputsAgree :
    ∀ i : Fin 2, InputsAgree jalrAcceptedTrace sailTrace i
      (jalrSpinZiskStep i)
  | ⟨0, _⟩ => setupInputs
  | ⟨1, _⟩ => jalrInputs

/-- The two root PC premises for this witness, from the per-row family above
    (`pcSeed_of_inputsAgree` / `inputsAgreeCore_of_inputsAgree`). -/
def pcSeed : SegmentPcSeed jalrAcceptedTrace sailTrace :=
  pcSeed_of_inputsAgree inputsAgree

def inputsAgreeCore :
    ∀ i : Fin 2, InputsAgreeCore jalrAcceptedTrace sailTrace i (jalrSpinZiskStep i) :=
  fun i => inputsAgreeCore_of_inputsAgree i (jalrSpinZiskStep i) (inputsAgree i)

def setupOutsideDefectRegion :
    RowOutsideDefectRegion jalrAcceptedTrace setupIndex
      (jalrSpinZiskStep setupIndex) := by
  simp [RowOutsideDefectRegion, jalrSpinZiskStep, setupIndex,
    MainSequentialPcDomain, mainPcVal, setupMainPc]

def jalrOutsideDefectRegion :
    RowOutsideDefectRegion jalrAcceptedTrace jalrIndex
      (jalrSpinZiskStep jalrIndex) where
  h_pc_bound := by
    unfold MainSequentialPcDomain mainPcVal
    norm_num [jalrIndex, jalrMainPc, ZiskFv.AirsClean.FullEnsemble.mainOfTable,
      mainAt_start, jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
      jalrAddProgramRow, jalrAddBits, ZiskFv.AirsClean.Main.mainRomRowOf]
  h_pc_offset_lt_2_32 := by
    intro pc hpc
    unfold mainPcVal at hpc
    norm_num [jalrIndex, jalrMainPc, ZiskFv.AirsClean.FullEnsemble.mainOfTable,
      mainAt_start, jalrAddRow, jalrAddRowWithLast, jalrAddRowTemplate,
      jalrAddProgramRow, jalrAddBits, ZiskFv.AirsClean.Main.mainRomRowOf] at hpc
    have hpc_eq : pc = 4#64 := BitVec.eq_of_toNat_eq hpc.symm
    subst pc
    norm_num

def outsideDefectRegion :
    ∀ i : Fin 2, RowOutsideDefectRegion jalrAcceptedTrace i
      (jalrSpinZiskStep i)
  | ⟨0, _⟩ => setupOutsideDefectRegion
  | ⟨1, _⟩ => jalrOutsideDefectRegion

/-- #330 Phase 7: each executed step's producer entry is its own row's successor `pc`. Only a
    two-row unaligned JALR lowering can break this, and only at a step that has a successor. -/
def jalrRowsAligned :
    StepRowsAligned jalrAcceptedTrace jalrSpinZiskStep
      (fun i => rowDecode_of_programDecode jalrAcceptedTrace i (programDecodes i)) := by
  intro j h
  have h' : j + 1 < 2 := h
  have hj : j < 2 - 1 := by omega
  interval_cases j <;> rfl

/-- The two root PC premises for this witness: boot agreement, and the Sail-internal retire law.
    `sailRetireChain_of_inputsAgree` builds the latter from the per-row `InputsAgree` family this
    witness already proves — no new content, and no hand-evaluated Sail execution. -/
def jalrPcChain : SegmentPcChain jalrAcceptedTrace sailTrace jalrSpinZiskStep where
  toSailRetireChain :=
    sailRetireChain_of_inputsAgree
      (fun i => rowDecode_of_programDecode jalrAcceptedTrace i (programDecodes i))
      inputsAgree bootSeed outsideDefectRegion jalrRowsAligned
  boot := (pcSeed_of_inputsAgree inputsAgree).boot

theorem jalrSpinRootSoundness :
    ∀ i : Fin 2,
      StepSound jalrAcceptedTrace sailTrace i (jalrSpinZiskStep i)
        (rowDecode_of_programDecode jalrAcceptedTrace i (programDecodes i)) :=
  stepSound_of_programDecodes 2 jalrAcceptedTrace sailTrace jalrSpinZiskStep
    programDecodes inputsAgreeCore jalrPcChain jalrRowsAligned bootSeed outsideDefectRegion

theorem jalrStepSound :
    StepSound jalrAcceptedTrace sailTrace jalrIndex
      (jalrSpinZiskStep jalrIndex)
      (rowDecode_of_programDecode jalrAcceptedTrace jalrIndex
        (programDecodes jalrIndex)) :=
  jalrSpinRootSoundness jalrIndex

end ZiskFv.Compliance.JalrSpinRootSoundness
