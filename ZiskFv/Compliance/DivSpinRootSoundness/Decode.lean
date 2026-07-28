import ZiskFv.Compliance.DivSpinRootSoundness.State

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.AirsClean.Main
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.DivSpinRootSoundness

attribute [local simp] mainFixedColumns_segment_l1_first
  mainFixedColumns_segment_l1_nonfirst mainFixedColumns_main_step_eq_index
  mainFixedCapacity

private theorem divSpinAcceptedTrace_program :
    divSpinAcceptedTrace.program = divSpinProgram := rfl

theorem divSpinMainRowAt (i : Fin 4) :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinProgram
      divSpinMainTable i.val =
      divSpinMainRows[i.val]'(by change i.val < 5; omega) := by
  fin_cases i
  · change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 0 (mainRawRow divSpinAddiX1Row)) emptyData)
      (varFromOffset MainRowWithRom 0) = divSpinAddiX1Row
    exact eval_mainRawRow_materialize 0 emptyData divSpinAddiX1Row (by rfl) (by rfl)
  · change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 1 (mainRawRow divSpinAddiX2Row)) emptyData)
      (varFromOffset MainRowWithRom 0) = divSpinAddiX2Row
    exact eval_mainRawRow_materialize 1 emptyData divSpinAddiX2Row (by rfl) (by rfl)
  · change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 2 (mainRawRow divSpinDivRow)) emptyData)
      (varFromOffset MainRowWithRom 0) = divSpinDivRow
    exact eval_mainRawRow_materialize 2 emptyData divSpinDivRow (by rfl) (by rfl)
  · change Eval.eval
      (Environment.fromArray
        (mainFixedColumns.materialize 3 (mainRawRow (divSpinJalRow 3))) emptyData)
      (varFromOffset MainRowWithRom 0) = divSpinJalRow 3
    exact eval_mainRawRow_materialize 3 emptyData (divSpinJalRow 3) (by rfl) (by rfl)

theorem divSpinAcceptedMainRowAt (i : Fin 4) :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable i.val =
      divSpinMainRows[i.val]'(by change i.val < 5; omega) := by
  rw [divSpinAcceptedTrace_program, divSpinAcceptedTrace_mainTable_eq]
  exact divSpinMainRowAt i

theorem divSpinMainPc (i : Fin 4) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable).pc i.val = (4 * i.val : Nat) := by
  rw [divSpinAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinProgram
      divSpinMainTable).pc i.val = _
  rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_pc]
  change
    (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero divSpinProgram
      divSpinMainTable i.val).core.pc = _
  rw [congrArg (fun row => row.core.pc) (divSpinMainRowAt i)]
  fin_cases i <;>
    simp [divSpinMainRows,
      divSpinAddiX1Row, divSpinAddiX2Row, divSpinDivRow,
      divSpinJalRow, divSpinAddiX1RowTemplate, divSpinAddiX2RowTemplate,
      divSpinDivRowTemplate, divSpinAddiX1ProgramRow, divSpinAddiX2ProgramRow,
      divSpinDivProgramRow, divSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow, mainRomRowOf]

set_option maxHeartbeats 800000 in
theorem divSpinProgramIndex_eq (i j : Fin 4)
    (hline : (divSpinProgram j).line =
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable).pc i.val) :
    j = i := by
  rw [divSpinMainPc] at hline
  apply Fin.ext
  have hval := congrArg (fun value : FGL => value.val) hline
  fin_cases i <;> fin_cases j <;>
    norm_num [divSpinProgram, divSpinAddiX1ProgramRow, divSpinAddiX2ProgramRow,
      divSpinDivProgramRow, divSpinJalProgramRow,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalProgramRow] at hval <;> omega

theorem divSpinReadX0 (i : Fin 4) :
    read_xreg (regidx_to_fin x0) (divSpinSailTrace i) =
      EStateM.Result.ok (0#64) (divSpinSailTrace i) := by
  fin_cases i <;>
    simp [divSpinSailTrace, divSpinState, divSpinRegs, x0, x1, x2, x3,
      regidx_to_fin, read_xreg, reg_of_fin, Std.ExtDHashMap.get?_insert]

theorem divSpinReadX1Div :
    read_xreg (regidx_to_fin x1) (divSpinSailTrace divSpinDivIndex) =
      EStateM.Result.ok (6#64) (divSpinSailTrace divSpinDivIndex) := by
  simp [divSpinSailTrace, divSpinDivIndex, divSpinState, divSpinRegs,
    x1, x2, x3, regidx_to_fin, read_xreg, reg_of_fin,
    Std.ExtDHashMap.get?_insert]

theorem divSpinReadX2Div :
    read_xreg (regidx_to_fin x2) (divSpinSailTrace divSpinDivIndex) =
      EStateM.Result.ok (2#64) (divSpinSailTrace divSpinDivIndex) := by
  simp [divSpinSailTrace, divSpinDivIndex, divSpinState, divSpinRegs,
    x1, x2, x3, regidx_to_fin, read_xreg, reg_of_fin,
    Std.ExtDHashMap.get?_insert]

def divSpinAddiX1Input : PureSpec.AddiInput where
  r1_val := 0#64
  imm := 6#12
  rd := regidx_to_fin x1
  PC := 0#64

def divSpinAddiX2Input : PureSpec.AddiInput where
  r1_val := 0#64
  imm := 2#12
  rd := regidx_to_fin x2
  PC := 4#64

def divSpinDivInput : PureSpec.DivInput where
  r1_val := 6#64
  r2_val := 2#64
  rd := regidx_to_fin x3
  PC := 8#64

def divSpinJalInput : PureSpec.JalInput where
  imm := 0#21
  rd := regidx_to_fin x0
  PC := 12#64

end ZiskFv.Compliance.DivSpinRootSoundness
