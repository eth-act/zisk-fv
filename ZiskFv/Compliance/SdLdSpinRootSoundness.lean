import ZiskFv.Compliance.SdLdSpinWitness
import ZiskFv.Soundness

set_option maxRecDepth 10000

/-!
# Concrete `root_soundness` instantiation for the SD/LD spin trace (#221)

The seven executed rows initialize x1 and x2, store 42 to `0xA0000008`,
load it into x3, and finish at the self-looping JAL.
-/

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.Compliance.SdLdSpinWitness
open ZiskFv.AirsClean.Main
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Trusted

namespace ZiskFv.Compliance.SdLdSpinRootSoundness

def x0 : regidx := regidx.Regidx (0#5)
def x1 : regidx := regidx.Regidx (1#5)
def x2 : regidx := regidx.Regidx (2#5)
def x3 : regidx := regidx.Regidx (3#5)

def sdLdAddiA0Index : Fin 7 := ⟨0, by decide⟩
def sdLdSlliIndex : Fin 7 := ⟨1, by decide⟩
def sdLdAddiEightIndex : Fin 7 := ⟨2, by decide⟩
def sdLdAddiX2Index : Fin 7 := ⟨3, by decide⟩
def sdLdSdIndex : Fin 7 := ⟨4, by decide⟩
def sdLdLdIndex : Fin 7 := ⟨5, by decide⟩
def sdLdJalIndex : Fin 7 := ⟨6, by decide⟩

def sdLdAddiA0Claim : Claim_addi sdLdAcceptedTrace sdLdAddiA0Index where
  r1 := x0
  rd := x1
  imm := 160#12

def sdLdSlliClaim : Claim_slli sdLdAcceptedTrace sdLdSlliIndex where
  r1 := x1
  rd := x1
  shamt := 24#6

def sdLdAddiEightClaim : Claim_addi sdLdAcceptedTrace sdLdAddiEightIndex where
  r1 := x1
  rd := x1
  imm := 8#12

def sdLdAddiX2Claim : Claim_addi sdLdAcceptedTrace sdLdAddiX2Index where
  r1 := x0
  rd := x2
  imm := 42#12

def sdLdSdInput : PureSpec.SdInput where
  r1 := 1#5
  imm := 0#12
  r2 := 2#5
  r1_val := 2684354568#64
  r2_val := 42#64
  PC := 16#64

def sdLdSdClaim : Claim_sd sdLdAcceptedTrace sdLdSdIndex where
  sd_input := sdLdSdInput

def sdLdLdInput : PureSpec.LdInput where
  r1 := 1#5
  imm := 0#12
  rd := 3#5
  r1_val := 2684354568#64
  PC := 20#64
  data0 := 42#8
  data1 := 0#8
  data2 := 0#8
  data3 := 0#8
  data4 := 0#8
  data5 := 0#8
  data6 := 0#8
  data7 := 0#8

def sdLdLdClaim : Claim_ld sdLdAcceptedTrace sdLdLdIndex where
  ld_input := sdLdLdInput

def sdLdJalClaim : Claim_jal sdLdAcceptedTrace sdLdJalIndex where
  imm := 0#21
  rd := x0

def sdLdZiskStep : ∀ i : Fin 7, ZiskStep sdLdAcceptedTrace i
  | ⟨0, _⟩ => .addi sdLdAddiA0Claim
  | ⟨1, _⟩ => .slli sdLdSlliClaim
  | ⟨2, _⟩ => .addi sdLdAddiEightClaim
  | ⟨3, _⟩ => .addi sdLdAddiX2Claim
  | ⟨4, _⟩ => .sd sdLdSdClaim
  | ⟨5, _⟩ => .ld sdLdLdClaim
  | ⟨6, _⟩ => .jal sdLdJalClaim

def sdLdMisa : RegisterType Register.misa := 0#64

def sdLdPmaAttrs : PMA :=
  { cacheable := false
    coherent := false
    executable := true
    readable := true
    writable := true
    read_idempotent := true
    write_idempotent := true
    misaligned_fault := misaligned_fault.AlignmentFault
    reservability := default
    supports_cbo_zero := false }

def sdLdPmaRegion : PMA_Region :=
  { base := 0#64
    size := BitVec.ofNat 64 (2 ^ 32)
    attributes := sdLdPmaAttrs
    include_in_device_tree := false }

def sdLdModeRegs : ZiskFv.Compliance.ModeRegsFull :=
  { mstatus := 0#64
    pmaRegion := sdLdPmaRegion
    misa := sdLdMisa
    mseccfg := 0#64 }

def sdLdRegs (pc x1Value x2Value x3Value : BitVec 64) :
    Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.cur_privilege Privilege.Machine
  let regs3 := regs2.insert Register.mstatus sdLdModeRegs.mstatus
  let regs4 := regs3.insert Register.pma_regions [sdLdModeRegs.pmaRegion]
  let regs5 := regs4.insert Register.htif_tohost_base (none : Option (BitVec 64))
  let regs6 := regs5.insert Register.misa sdLdModeRegs.misa
  let regs7 := regs6.insert Register.mseccfg sdLdModeRegs.mseccfg
  let regs8 := regs7.insert (reg_of_fin (regidx_to_fin x1)) x1Value
  let regs9 := regs8.insert (reg_of_fin (regidx_to_fin x2)) x2Value
  regs9.insert (reg_of_fin (regidx_to_fin x3)) x3Value

def sdLdAcceptedReplayRows : List (Interaction.MemoryBusEntry FGL) :=
  [ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Mem.memBusMessage sdMemRow) 1 2,
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Mem.memBusMessage ldMemRow) (-1) 2]

def sdLdInitialMem : Std.ExtHashMap Nat (BitVec 8) :=
  ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows sdLdAcceptedReplayRows

def sdLdStoredMem : Std.ExtHashMap Nat (BitVec 8) :=
  ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry sdLdInitialMem
    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (ZiskFv.AirsClean.Mem.memBusMessage sdMemRow) 1 2)

def sdLdState (pc x1Value x2Value x3Value : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := sdLdRegs pc x1Value x2Value x3Value
    mem := mem }

def sdLdSailTrace : SailTrace 7
  | ⟨0, _⟩ => sdLdState (0#64) (0#64) (0#64) (0#64) sdLdInitialMem
  | ⟨1, _⟩ => sdLdState (4#64) (160#64) (0#64) (0#64) sdLdInitialMem
  | ⟨2, _⟩ => sdLdState (8#64) (2684354560#64) (0#64) (0#64) sdLdInitialMem
  | ⟨3, _⟩ => sdLdState (12#64) (2684354568#64) (0#64) (0#64) sdLdInitialMem
  | ⟨4, _⟩ => sdLdState (16#64) (2684354568#64) (42#64) (0#64) sdLdInitialMem
  | ⟨5, _⟩ => sdLdState (20#64) (2684354568#64) (42#64) (0#64) sdLdStoredMem
  | ⟨6, _⟩ => sdLdState (24#64) (2684354568#64) (42#64) (42#64) sdLdStoredMem

private theorem sdLdAcceptedTrace_program :
    sdLdAcceptedTrace.program = sdLdProgram := rfl

private theorem sdLdMainRowAt (i : Fin 7) :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero sdLdProgram
        (sdLdTableWithData sdLdMainTable) i.val =
      sdLdMainRows[i.val]'(by
        simpa [sdLdMainRows] using
          Nat.lt_trans i.isLt (by decide : 7 < 8)) := by
  unfold ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
  rw [dif_pos (by change i.val < 8; omega)]
  change Eval.eval (sdLdMainTable.environmentAt ⟨i.val, by
      rw [sdLdMainTable_length]
      omega⟩)
      (componentWithRomMemAndOpBus 7 sdLdProgram).rowInputVar = _
  simpa [sdLdMainRows] using sdLdMainTable_evalAt ⟨i.val, by
    rw [sdLdMainTable_length]
    omega⟩

private theorem sdLdMainPc (i : Fin 7) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdAcceptedTrace.program
        sdLdAcceptedTrace.mainTable).pc i.val = (4 * i.val : Nat) := by
  rw [sdLdAcceptedTrace_mainTable_eq]
  change (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdProgram
      (sdLdTableWithData sdLdMainTable)).pc i.val = _
  rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_pc]
  change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero sdLdProgram
    (sdLdTableWithData sdLdMainTable) i.val).core.pc = _
  rw [congrArg (fun row => row.core.pc) (sdLdMainRowAt i)]
  fin_cases i <;>
    simp [sdLdMainRows, sdLdAddiX1A0Row,
    sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate, sdLdSlliX1Row,
    sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, sdLdAddiX1EightRow,
    sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate, sdLdAddiX2Row,
    sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate, sdLdSdRow, sdLdSdRowTemplate,
    sdLdLdRow, sdLdLdRowTemplate, sdLdJalRow, mainRomRowOf,
    sdLdAddiX1A0ProgramRow, sdLdSlliX1ProgramRow, sdLdAddiX1EightProgramRow,
    sdLdAddiX2ProgramRow, sdLdSdProgramRow, sdLdLdProgramRow, sdLdJalProgramRow]

set_option maxHeartbeats 800000 in
private theorem sdLdProgramIndex_eq (i j : Fin 7)
    (hline : (sdLdProgram j).line =
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdAcceptedTrace.program
        sdLdAcceptedTrace.mainTable).pc i.val) :
    j = i := by
  rw [sdLdMainPc] at hline
  apply Fin.ext
  have hval := congrArg (fun value : FGL => value.val) hline
  fin_cases i <;> fin_cases j <;>
    norm_num [sdLdProgram, sdLdAddiX1A0ProgramRow, sdLdSlliX1ProgramRow,
      sdLdAddiX1EightProgramRow, sdLdAddiX2ProgramRow, sdLdSdProgramRow,
      sdLdLdProgramRow, sdLdJalProgramRow] at hval <;> omega

def sdLdAddiA0ProgramDecode :
    ProgramDecode_addi sdLdAcceptedTrace sdLdAddiA0Index sdLdAddiA0Claim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    norm_num [sdLdAddiA0Index, sdLdTableWithData]
  bits := addiX0Bits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_b_src_imm := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨0, by decide⟩ := sdLdProgramIndex_eq sdLdAddiA0Index j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdAddiX1A0ProgramRow,
      sdLdAddiA0Claim, x1, Transpiler.ind, regidx_to_fin, packFlags, addiX0Bits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdSlliProgramDecode :
    ProgramDecode_slli sdLdAcceptedTrace sdLdSlliIndex sdLdSlliClaim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    change 1 + 1 < (sdLdTableWithData sdLdMainTable).table.length
    norm_num [sdLdTableWithData, sdLdMainTable, sdLdMainTableWithData,
      sdLdMainTableEmptyData, AddSpinWitness.mainRowsTable, sdLdMainRows]
  h_b_lo_t := by
    rw [sdLdAcceptedTrace_mainTable_eq,
      ZiskFv.AirsClean.FullEnsemble.mainOfTable_b_0]
    change
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero sdLdProgram
        (sdLdTableWithData sdLdMainTable) sdLdSlliIndex.val).core.b_0 = _
    rw [congrArg (fun row => row.core.b_0) (sdLdMainRowAt sdLdSlliIndex)]
    norm_num [sdLdSlliIndex, sdLdMainRows, sdLdSlliClaim, sdLdSlliX1Row,
      sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, mainRomRowOf, shamt_b_lo]
    decide
  bits := addiX1Bits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨1, by decide⟩ := sdLdProgramIndex_eq sdLdSlliIndex j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdSlliX1ProgramRow,
      sdLdSlliClaim, x1, Transpiler.ind, regidx_to_fin, packFlags, addiX1Bits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdAddiEightProgramDecode :
    ProgramDecode_addi sdLdAcceptedTrace sdLdAddiEightIndex sdLdAddiEightClaim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    norm_num [sdLdAddiEightIndex, sdLdTableWithData]
  bits := addiX1Bits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_b_src_imm := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨2, by decide⟩ := sdLdProgramIndex_eq sdLdAddiEightIndex j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdAddiX1EightProgramRow,
      sdLdAddiEightClaim, x1, Transpiler.ind, regidx_to_fin, packFlags, addiX1Bits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdAddiX2ProgramDecode :
    ProgramDecode_addi sdLdAcceptedTrace sdLdAddiX2Index sdLdAddiX2Claim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    norm_num [sdLdAddiX2Index, sdLdTableWithData]
  bits := addiX0Bits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_b_src_imm := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨3, by decide⟩ := sdLdProgramIndex_eq sdLdAddiX2Index j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdAddiX2ProgramRow,
      sdLdAddiX2Claim, x2, Transpiler.ind, regidx_to_fin, packFlags, addiX0Bits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdSdProgramDecode :
    ProgramDecode_sd sdLdAcceptedTrace sdLdSdIndex sdLdSdClaim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    norm_num [sdLdSdIndex, sdLdTableWithData]
  bits := sdLdSdBits
  h_bits_ieo := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨4, by decide⟩ := sdLdProgramIndex_eq sdLdSdIndex j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdSdProgramRow, sdLdSdClaim,
      sdLdSdInput, packFlags, sdLdSdBits, ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdLdProgramDecode :
    ProgramDecode_ld sdLdAcceptedTrace sdLdLdIndex sdLdLdClaim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    norm_num [sdLdLdIndex, sdLdTableWithData]
  bits := sdLdLdBits
  h_bits_ieo := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_bits_store_reg := rfl
  h_bits_b_src_ind := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨5, by decide⟩ := sdLdProgramIndex_eq sdLdLdIndex j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdLdProgramRow, sdLdLdClaim,
      sdLdLdInput, Transpiler.ind, Transpiler.regidxOfBitVec5, packFlags,
      sdLdLdBits, ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdJalProgramDecode :
    ProgramDecode_jal sdLdAcceptedTrace sdLdJalIndex sdLdJalClaim where
  h_idx := by
    rw [sdLdAcceptedTrace_mainTable_eq]
    norm_num [sdLdJalIndex, sdLdTableWithData]
  bits := AddSpinWitness.addSpinJalBits
  h_bits_ieo := rfl
  h_bits_m32 := rfl
  h_bits_set_pc := rfl
  h_bits_store_pc := rfl
  h_bits_store_ind := rfl
  h_prog := by
    intro j hline
    have hj : j = ⟨6, by decide⟩ := sdLdProgramIndex_eq sdLdJalIndex j hline
    subst j
    rw [sdLdAcceptedTrace_program]
    norm_num [sdLdAcceptedTrace, sdLdProgram, sdLdJalProgramRow, sdLdJalClaim,
      x0, Transpiler.ind, regidx_to_fin, packFlags, AddSpinWitness.addSpinJalBits,
      ZiskFv.AirsClean.boolF]
    all_goals decide

def sdLdAddiA0Input : PureSpec.AddiInput where
  r1_val := 0#64
  imm := 160#12
  rd := regidx_to_fin x1
  PC := 0#64

private theorem sdLdReadX0 (i : Fin 7) :
    read_xreg (regidx_to_fin x0) (sdLdSailTrace i) =
      EStateM.Result.ok (0#64) (sdLdSailTrace i) := by
  fin_cases i <;>
    simp [sdLdSailTrace, sdLdState, sdLdRegs, x0, x1, x2, x3,
      regidx_to_fin, read_xreg, reg_of_fin, sdLdStoredMem,
      Std.ExtDHashMap.get?_insert]

private theorem sdLdAcceptedMainRowAt (i : Fin 7) :
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero sdLdAcceptedTrace.program
        sdLdAcceptedTrace.mainTable i.val =
      sdLdMainRows[i.val]'(by
        simpa [sdLdMainRows] using Nat.lt_trans i.isLt (by decide : 7 < 8)) := by
  rw [sdLdAcceptedTrace_program, sdLdAcceptedTrace_mainTable_eq]
  exact sdLdMainRowAt i

def sdLdAddiA0Inputs :
    Inputs_addi sdLdAcceptedTrace sdLdSailTrace sdLdAddiA0Index
      sdLdAddiA0Claim where
  addi_input := sdLdAddiA0Input
  h_input_r1 := by
    simpa [sdLdAddiA0Input, sdLdAddiA0Claim] using sdLdReadX0 sdLdAddiA0Index
  h_input_imm := rfl
  h_input_pc := by
    simp [sdLdAddiA0Input, sdLdSailTrace, sdLdAddiA0Index, sdLdState, sdLdRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := rfl
  h_a_lo_t := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdAddiA0Index.val).core.a_0 = _
    rw [congrArg (fun row => row.core.a_0) (sdLdAcceptedMainRowAt sdLdAddiA0Index)]
    simp only [sdLdAddiA0Claim]
    rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
      (sdLdSailTrace sdLdAddiA0Index) (regidx_to_fin x0) (0#64)
      (sdLdReadX0 sdLdAddiA0Index)]
    norm_num [sdLdAddiA0Index, sdLdMainRows, sdLdAddiX1A0Row,
      sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate, mainRomRowOf, lane_lo]
  h_a_hi_t := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdAddiA0Index.val).core.a_1 = _
    rw [congrArg (fun row => row.core.a_1) (sdLdAcceptedMainRowAt sdLdAddiA0Index)]
    simp only [sdLdAddiA0Claim]
    rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
      (sdLdSailTrace sdLdAddiA0Index) (regidx_to_fin x0) (0#64)
      (sdLdReadX0 sdLdAddiA0Index)]
    norm_num [sdLdAddiA0Index, sdLdMainRows, sdLdAddiX1A0Row,
      sdLdAddiX1A0RowWithLast, sdLdAddiX1A0RowTemplate, mainRomRowOf, lane_hi]
  h_pc_bridge := by
    rw [sdLdMainPc]
    norm_num [sdLdAddiA0Index, sdLdAddiA0Input]

private theorem sdLdReadX1 (i : Fin 7) :
    read_xreg (regidx_to_fin x1) (sdLdSailTrace i) =
      EStateM.Result.ok
        ([0#64, 160#64, 2684354560#64, 2684354568#64,
          2684354568#64, 2684354568#64, 2684354568#64][i.val]'(by
            simpa using i.isLt))
        (sdLdSailTrace i) := by
  fin_cases i <;>
    simp [sdLdSailTrace, sdLdState, sdLdRegs, x1, x2, x3, regidx_to_fin,
      read_xreg, reg_of_fin, sdLdStoredMem, Std.ExtDHashMap.get?_insert]

private theorem sdLdReadX2Sd :
    read_xreg (regidx_to_fin x2) (sdLdSailTrace sdLdSdIndex) =
      EStateM.Result.ok (42#64) (sdLdSailTrace sdLdSdIndex) := by
  simp [sdLdSailTrace, sdLdSdIndex, sdLdState, sdLdRegs, x1, x2, x3,
    regidx_to_fin, read_xreg, reg_of_fin, Std.ExtDHashMap.get?_insert]

private theorem sdLdLaneLo
    (i : Fin 7) (value : BitVec 64)
    (hread : read_xreg (regidx_to_fin x1) (sdLdSailTrace i) =
      EStateM.Result.ok value (sdLdSailTrace i))
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (hfield : field
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdAcceptedTrace.program
        sdLdAcceptedTrace.mainTable) i.val = lane_lo value) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdAcceptedTrace.program
      sdLdAcceptedTrace.mainTable) i.val =
      lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (sdLdSailTrace i)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (sdLdSailTrace i) (regidx_to_fin x1) value hread]
  exact hfield

private theorem sdLdLaneHi
    (i : Fin 7) (value : BitVec 64)
    (hread : read_xreg (regidx_to_fin x1) (sdLdSailTrace i) =
      EStateM.Result.ok value (sdLdSailTrace i))
    (field : ZiskFv.Airs.Main.Valid_Main FGL FGL → Nat → FGL)
    (hfield : field
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdAcceptedTrace.program
        sdLdAcceptedTrace.mainTable) i.val = lane_hi value) :
    field (ZiskFv.AirsClean.FullEnsemble.mainOfTable sdLdAcceptedTrace.program
      sdLdAcceptedTrace.mainTable) i.val =
      lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
        (sdLdSailTrace i)).xreg (regidx_to_fin x1)) := by
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    (sdLdSailTrace i) (regidx_to_fin x1) value hread]
  exact hfield

def sdLdSlliInput : PureSpec.SlliInput where
  r1_val := 160#64
  shamt := 24#6
  rd := regidx_to_fin x1
  PC := 4#64

def sdLdSlliInputs :
    Inputs_slli sdLdAcceptedTrace sdLdSailTrace sdLdSlliIndex sdLdSlliClaim where
  slli_input := sdLdSlliInput
  h_input_r1 := by
    simpa [sdLdSlliInput, sdLdSlliIndex] using sdLdReadX1 sdLdSlliIndex
  h_input_shamt := rfl
  h_input_pc := by
    simp [sdLdSlliInput, sdLdSailTrace, sdLdSlliIndex, sdLdState, sdLdRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := rfl
  h_a_lo_t := by
    apply sdLdLaneLo sdLdSlliIndex (160#64)
      (by simpa [sdLdSlliIndex] using sdLdReadX1 sdLdSlliIndex)
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdSlliIndex.val).core.a_0 = _
    rw [congrArg (fun row => row.core.a_0) (sdLdAcceptedMainRowAt sdLdSlliIndex)]
    norm_num [sdLdSlliIndex, sdLdMainRows, sdLdSlliX1Row,
      sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, mainRomRowOf, lane_lo]
    decide
  h_a_hi_t := by
    apply sdLdLaneHi sdLdSlliIndex (160#64)
      (by simpa [sdLdSlliIndex] using sdLdReadX1 sdLdSlliIndex)
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdSlliIndex.val).core.a_1 = _
    rw [congrArg (fun row => row.core.a_1) (sdLdAcceptedMainRowAt sdLdSlliIndex)]
    norm_num [sdLdSlliIndex, sdLdMainRows, sdLdSlliX1Row,
      sdLdSlliX1RowWithLast, sdLdSlliX1RowTemplate, mainRomRowOf, lane_hi]
  h_pc_bridge := by rw [sdLdMainPc]; norm_num [sdLdSlliIndex, sdLdSlliInput]

private def sdLdAddiInput
    (value : BitVec 64) (imm : BitVec 12) (rd : regidx) (pc : BitVec 64) :
    PureSpec.AddiInput where
  r1_val := value
  imm := imm
  rd := regidx_to_fin rd
  PC := pc

def sdLdAddiEightInputs :
    Inputs_addi sdLdAcceptedTrace sdLdSailTrace sdLdAddiEightIndex
      sdLdAddiEightClaim where
  addi_input := sdLdAddiInput (2684354560#64) (8#12) x1 (8#64)
  h_input_r1 := by
    simpa [sdLdAddiInput, sdLdAddiEightClaim, sdLdAddiEightIndex] using
      sdLdReadX1 sdLdAddiEightIndex
  h_input_imm := rfl
  h_input_pc := by
    simp [sdLdAddiInput, sdLdSailTrace, sdLdAddiEightIndex, sdLdState, sdLdRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := rfl
  h_a_lo_t := by
    apply sdLdLaneLo sdLdAddiEightIndex (2684354560#64)
      (by simpa [sdLdAddiEightIndex] using sdLdReadX1 sdLdAddiEightIndex)
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdAddiEightIndex.val).core.a_0 = _
    rw [congrArg (fun row => row.core.a_0) (sdLdAcceptedMainRowAt sdLdAddiEightIndex)]
    norm_num [sdLdAddiEightIndex, sdLdMainRows, sdLdAddiX1EightRow,
      sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate, mainRomRowOf, lane_lo]
    decide
  h_a_hi_t := by
    apply sdLdLaneHi sdLdAddiEightIndex (2684354560#64)
      (by simpa [sdLdAddiEightIndex] using sdLdReadX1 sdLdAddiEightIndex)
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdAddiEightIndex.val).core.a_1 = _
    rw [congrArg (fun row => row.core.a_1) (sdLdAcceptedMainRowAt sdLdAddiEightIndex)]
    norm_num [sdLdAddiEightIndex, sdLdMainRows, sdLdAddiX1EightRow,
      sdLdAddiX1EightRowWithLast, sdLdAddiX1EightRowTemplate, mainRomRowOf, lane_hi]
  h_pc_bridge := by rw [sdLdMainPc]; norm_num [sdLdAddiEightIndex, sdLdAddiInput]

def sdLdAddiX2Inputs :
    Inputs_addi sdLdAcceptedTrace sdLdSailTrace sdLdAddiX2Index sdLdAddiX2Claim where
  addi_input := sdLdAddiInput (0#64) (42#12) x2 (12#64)
  h_input_r1 := by simpa [sdLdAddiInput, sdLdAddiX2Claim] using sdLdReadX0 sdLdAddiX2Index
  h_input_imm := rfl
  h_input_pc := by
    simp [sdLdAddiInput, sdLdSailTrace, sdLdAddiX2Index, sdLdState, sdLdRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_rd := rfl
  h_a_lo_t := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdAddiX2Index.val).core.a_0 = _
    rw [congrArg (fun row => row.core.a_0) (sdLdAcceptedMainRowAt sdLdAddiX2Index)]
    simp only [sdLdAddiX2Claim]
    rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
      (sdLdSailTrace sdLdAddiX2Index) (regidx_to_fin x0) (0#64)
      (sdLdReadX0 sdLdAddiX2Index)]
    norm_num [sdLdAddiX2Index, sdLdMainRows, sdLdAddiX2Row,
      sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate, mainRomRowOf, lane_lo]
  h_a_hi_t := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable
      sdLdAddiX2Index.val).core.a_1 = _
    rw [congrArg (fun row => row.core.a_1) (sdLdAcceptedMainRowAt sdLdAddiX2Index)]
    simp only [sdLdAddiX2Claim]
    rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
      (sdLdSailTrace sdLdAddiX2Index) (regidx_to_fin x0) (0#64)
      (sdLdReadX0 sdLdAddiX2Index)]
    norm_num [sdLdAddiX2Index, sdLdMainRows, sdLdAddiX2Row,
      sdLdAddiX2RowWithLast, sdLdAddiX2RowTemplate, mainRomRowOf, lane_hi]
  h_pc_bridge := by rw [sdLdMainPc]; norm_num [sdLdAddiX2Index, sdLdAddiInput]

def sdLdSdInputs :
    Inputs_sd sdLdAcceptedTrace sdLdSailTrace sdLdSdIndex sdLdSdClaim where
  regs := sdLdModeRegs
  h_opcode_assumptions := by
    unfold PureSpec.sd_state_assumptions
    simp [sdLdSdClaim, sdLdSdInput, sdLdSailTrace, sdLdSdIndex, sdLdState, sdLdRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, LeanRV64D.Functions.rX_bits,
      LeanRV64D.Functions.rX, Std.ExtDHashMap.get?_insert,
      Std.ExtDHashMap.get?_insert_self]
  h_a0_value := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable sdLdSdIndex.val).core.a_0 = _
    rw [congrArg (fun row => row.core.a_0) (sdLdAcceptedMainRowAt sdLdSdIndex)]
    norm_num [sdLdSdIndex, sdLdSdClaim, sdLdSdInput, sdLdMainRows, sdLdSdRow,
      sdLdSdRowTemplate, mainRomRowOf, lane_lo]
    decide
  h_a1_value := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable sdLdSdIndex.val).core.a_1 = _
    rw [congrArg (fun row => row.core.a_1) (sdLdAcceptedMainRowAt sdLdSdIndex)]
    norm_num [sdLdSdIndex, sdLdSdClaim, sdLdSdInput, sdLdMainRows, sdLdSdRow,
      sdLdSdRowTemplate, mainRomRowOf, lane_hi]
  h_b0_value := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_b_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable sdLdSdIndex.val).core.b_0 = _
    rw [congrArg (fun row => row.core.b_0) (sdLdAcceptedMainRowAt sdLdSdIndex)]
    norm_num [sdLdSdIndex, sdLdSdClaim, sdLdSdInput, sdLdMainRows, sdLdSdRow,
      sdLdSdRowTemplate, mainRomRowOf, lane_lo]
    decide
  h_b1_value := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_b_1]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable sdLdSdIndex.val).core.b_1 = _
    rw [congrArg (fun row => row.core.b_1) (sdLdAcceptedMainRowAt sdLdSdIndex)]
    norm_num [sdLdSdIndex, sdLdSdClaim, sdLdSdInput, sdLdMainRows, sdLdSdRow,
      sdLdSdRowTemplate, mainRomRowOf, lane_hi]
  h_risc_v_assumptions := by
    unfold RISC_V_assumptions
    simp [sdLdSailTrace, sdLdSdIndex, sdLdState, sdLdRegs, sdLdModeRegs,
      sdLdPmaRegion, sdLdPmaAttrs, x1, x2, x3, regidx_to_fin, reg_of_fin,
      Sail.readReg, PreSail.readReg,
      Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  h_pc_bridge := by rw [sdLdMainPc]; norm_num [sdLdSdIndex, sdLdSdClaim, sdLdSdInput]

def sdLdLdInputs :
    Inputs_ld sdLdAcceptedTrace sdLdSailTrace sdLdLdIndex sdLdLdClaim where
  regs := sdLdModeRegs
  mem := ZiskFv.AirsClean.FullEnsemble.memOfTableData sdLdMemTable
  r_mem := 1
  h_opcode_assumptions := by
    unfold PureSpec.ld_state_assumptions
    simp [sdLdLdClaim, sdLdLdInput, sdLdSailTrace, sdLdLdIndex, sdLdState, sdLdRegs,
      sdLdStoredMem, sdLdInitialMem, sdLdAcceptedReplayRows, sdMemRow,
      ZiskFv.AirsClean.Mem.memBusMessage, ZiskFv.AirsClean.Mem.memRowOf,
      ZiskFv.AirsClean.Mem.memValueOf,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
      ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry,
      ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows,
      ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfEntry,
      ZiskFv.ZiskCircuit.MemTrace.zeroedMemoryEntryOfEntry,
      ZiskFv.Channels.MemoryBusBytes.byteAt,
      x1, x2, x3, regidx_to_fin, reg_of_fin,
      LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.rX,
      Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self,
      Std.ExtHashMap.getElem_insert, Std.ExtHashMap.getElem_insert_self]
  h_a0_value := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_0]
    change (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
      sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable sdLdLdIndex.val).core.a_0 = _
    rw [congrArg (fun row => row.core.a_0) (sdLdAcceptedMainRowAt sdLdLdIndex)]
    norm_num [sdLdLdIndex, sdLdLdClaim, sdLdLdInput, sdLdMainRows, sdLdLdRow,
      sdLdLdRowTemplate, mainRomRowOf, lane_lo]
    decide
  h_risc_v_assumptions := by
    unfold RISC_V_assumptions
    simp [sdLdSailTrace, sdLdLdIndex, sdLdState, sdLdRegs, sdLdModeRegs,
      sdLdPmaRegion, sdLdPmaAttrs, x1, x2, x3, regidx_to_fin, reg_of_fin,
      Sail.readReg, PreSail.readReg,
      Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]
  h_pc_bridge := by rw [sdLdMainPc]; norm_num [sdLdLdIndex, sdLdLdClaim, sdLdLdInput]
  h_msg := by
    have hmem :
        ZiskFv.AirsClean.Mem.rowAt
          (ZiskFv.AirsClean.FullEnsemble.memOfTableData sdLdMemTable) 1 = ldMemRow := by
      rw [ZiskFv.AirsClean.FullEnsemble.rowAt_memOfTableData sdLdMemTable
        ⟨1, by simp⟩]
      exact sdLdMemTable_memRowAt_one
    rw [hmem]
    rw [show mainRowWithRomLd sdLdAcceptedTrace sdLdLdIndex = sdLdLdRow by
      change ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
        sdLdAcceptedTrace.program sdLdAcceptedTrace.mainTable sdLdLdIndex.val = _
      exact sdLdAcceptedMainRowAt sdLdLdIndex]
    norm_num [loadMemMsg, loadMainMsg, ldMemRow, sdLdLdRow, sdLdLdRowTemplate,
      sdLdLdProgramRow, sdLdLdBits, mainRomRowOf,
      AbstractInteraction.eval, ChannelInteraction.toRaw,
      Channel.emitted,
      ZiskFv.AirsClean.Mem.memBusMessageExpr, bMemMessageExpr,
      bMemOpExpr, memConstVar, mainConstVar, Expression.eval,
      ZiskFv.AirsClean.Mem.memRowOf, ZiskFv.AirsClean.Mem.memReadSameAddrOf,
      ZiskFv.AirsClean.Mem.memValueOf]
    change Array.map (fun x => Expression.eval loadEvalEnv x)
        (toElements (ZiskFv.AirsClean.Mem.memBusMessageExpr (memConstVar ldMemRow))).toArray =
      Array.map (fun x => Expression.eval loadEvalEnv x)
        (toElements (bMemMessageExpr (mainConstVar sdLdLdRow))).toArray
    norm_num [memConstVar, mainConstVar, Expression.eval,
      ZiskFv.AirsClean.Mem.memBusMessageExpr, bMemMessageExpr,
      ldMemRow, sdLdLdRow, sdLdLdRowTemplate, sdLdLdProgramRow, sdLdLdBits,
      bMemOpExpr, sdLdSdRow, sdLdSdRowTemplate, sdLdSdProgramRow, sdLdSdBits,
      sdLdFreeCols, mainRomRowOf, mainRomFreeColsWithRegisterPrevious,
      materializeMainRegisterRow, materializeMainRegisterAccesses,
      withMainRegisterPrevious, ZiskFv.AirsClean.Mem.memRowOf,
      ZiskFv.AirsClean.Mem.memReadSameAddrOf, ZiskFv.AirsClean.Mem.memValueOf]
    simp [toElements, loadEvalEnv, ProvableStruct.componentsToElements,
      ProvableStruct.components, ProvableStruct.toComponents]
    decide
  h_mem_sel := by
    have hmem := ZiskFv.AirsClean.FullEnsemble.rowAt_memOfTableData
      sdLdMemTable ⟨1, by simp⟩
    have hrow := sdLdMemTable_memRowAt_one
    exact congrArg ZiskFv.AirsClean.Mem.MemRow.sel (hmem.trans hrow)
  h_mem_wr := by
    have hmem := ZiskFv.AirsClean.FullEnsemble.rowAt_memOfTableData
      sdLdMemTable ⟨1, by simp⟩
    have hrow := sdLdMemTable_memRowAt_one
    exact congrArg ZiskFv.AirsClean.Mem.MemRow.wr (hmem.trans hrow)

def sdLdJalInput : PureSpec.JalInput where
  imm := 0#21
  rd := regidx_to_fin x0
  PC := 24#64

def sdLdJalInputs :
    Inputs_jal sdLdAcceptedTrace sdLdSailTrace sdLdJalIndex sdLdJalClaim where
  jal_input := sdLdJalInput
  misa_val := sdLdMisa
  h_pc_bridge := by rw [sdLdMainPc]; norm_num [sdLdJalIndex, sdLdJalInput]
  h_input_rd := rfl
  h_input_pc := by
    simp [sdLdJalInput, sdLdSailTrace, sdLdJalIndex, sdLdState, sdLdRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_input_misa := by
    simp [sdLdSailTrace, sdLdJalIndex, sdLdState, sdLdRegs, sdLdModeRegs, sdLdMisa,
      x1, x2, x3,
      regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_misa_c := by simp [sdLdMisa]
  h_success := by simp [sdLdJalInput, PureSpec.execute_JAL_pure]
  h_input_imm := rfl

def sdLdProgramDecodes :
    ∀ i : Fin 7, ProgramDecode sdLdAcceptedTrace i (sdLdZiskStep i)
  | ⟨0, _⟩ => sdLdAddiA0ProgramDecode
  | ⟨1, _⟩ => sdLdSlliProgramDecode
  | ⟨2, _⟩ => sdLdAddiEightProgramDecode
  | ⟨3, _⟩ => sdLdAddiX2ProgramDecode
  | ⟨4, _⟩ => sdLdSdProgramDecode
  | ⟨5, _⟩ => sdLdLdProgramDecode
  | ⟨6, _⟩ => sdLdJalProgramDecode

def sdLdInputsAgree :
    ∀ i : Fin 7, InputsAgree sdLdAcceptedTrace sdLdSailTrace i (sdLdZiskStep i)
  | ⟨0, _⟩ => sdLdAddiA0Inputs
  | ⟨1, _⟩ => sdLdSlliInputs
  | ⟨2, _⟩ => sdLdAddiEightInputs
  | ⟨3, _⟩ => sdLdAddiX2Inputs
  | ⟨4, _⟩ => sdLdSdInputs
  | ⟨5, _⟩ => sdLdLdInputs
  | ⟨6, _⟩ => sdLdJalInputs

private theorem sdLdStoreEntry_eq :
    (busSt sdLdAcceptedTrace sdLdSdIndex
      (Pilot.execRowOf sdLdAcceptedTrace sdLdSdIndex)).e2 =
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage sdMemRow) 1 2 := by
  change ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (cMemMessage (mainRowWithRomSt sdLdAcceptedTrace sdLdSdIndex)) 1 2 = _
  rw [show mainRowWithRomSt sdLdAcceptedTrace sdLdSdIndex = sdLdSdRow by
    exact sdLdAcceptedMainRowAt sdLdSdIndex]
  rw [sdLdStoreMessage_eq_mem]

private theorem sdLdLoadEntry_eq :
    (busLd sdLdAcceptedTrace sdLdLdIndex
      (Pilot.execRowOf sdLdAcceptedTrace sdLdLdIndex)).e1 =
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage ldMemRow) (-1) 2 := by
  change ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
      (bMemMessage (mainRowWithRomLd sdLdAcceptedTrace sdLdLdIndex)) (-1) 2 = _
  rw [show mainRowWithRomLd sdLdAcceptedTrace sdLdLdIndex = sdLdLdRow by
    exact sdLdAcceptedMainRowAt sdLdLdIndex]
  rw [sdLdLoadMessage_eq_mem]

noncomputable def sdLdMemoryRowsOf : ℕ → List (Interaction.MemoryBusEntry FGL)
  | 4 => [(busSt sdLdAcceptedTrace sdLdSdIndex
      (Pilot.execRowOf sdLdAcceptedTrace sdLdSdIndex)).e2]
  | 5 => [(busLd sdLdAcceptedTrace sdLdLdIndex
      (Pilot.execRowOf sdLdAcceptedTrace sdLdLdIndex)).e1]
  | _ => []

private theorem sdLdMemTable_activeReplayRows :
    ZiskFv.AirsClean.FullEnsemble.activeMemReplayRowsOfTable sdLdMemTable =
      sdLdAcceptedReplayRows := by
  unfold ZiskFv.AirsClean.FullEnsemble.activeMemReplayRowsOfTable
  rw [show sdLdMemTable.table =
    [ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
        (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData sdMemRow),
      ZiskFv.AirsClean.Mem.memFixedColumns.materialize 1
        (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData ldMemRow)] by rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hrow0 : Eval.eval
      (sdLdMemTable.environment
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData sdMemRow)))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar = sdMemRow := by
    change Eval.eval
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 0
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData sdMemRow)) sdLdMemData)
      (varFromOffset (F := FGL) ZiskFv.AirsClean.Mem.MemRow 0) = sdMemRow
    exact ZiskFv.AirsClean.Mem.eval_memRawRowWithProverData_materialize
      0 sdLdMemData sdMemRow
  have hrow1 : Eval.eval
      (sdLdMemTable.environment
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 1
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData ldMemRow)))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar = ldMemRow := by
    change Eval.eval
      (Environment.fromArray
        (ZiskFv.AirsClean.Mem.memFixedColumns.materialize 1
          (ZiskFv.AirsClean.Mem.memRawRowWithProverData sdLdMemData ldMemRow)) sdLdMemData)
      (varFromOffset (F := FGL) ZiskFv.AirsClean.Mem.MemRow 0) = ldMemRow
    exact ZiskFv.AirsClean.Mem.eval_memRawRowWithProverData_materialize
      1 sdLdMemData ldMemRow
  rw [hrow0, hrow1]
  rfl

noncomputable def sdLdBootSeed :
    BootSegmentMemorySeed sdLdAcceptedTrace sdLdSailTrace sdLdZiskStep where
  memInit := sdLdInitialMem
  rowsOf := sdLdMemoryRowsOf
  boot := by intro _; rfl
  step := by
    intro j h
    change j + 1 < 7 at h
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [sdLdSailTrace, sdLdState, sdLdMemoryRowsOf, replayMemoryAfterBusRows]
    · simp [sdLdSailTrace, sdLdState, sdLdMemoryRowsOf, replayMemoryAfterBusRows]
    · simp [sdLdSailTrace, sdLdState, sdLdMemoryRowsOf, replayMemoryAfterBusRows]
    · simp [sdLdSailTrace, sdLdState, sdLdMemoryRowsOf, replayMemoryAfterBusRows]
    · rw [show (⟨4, by omega⟩ : Fin 7) = sdLdSdIndex by rfl]
      rw [show sdLdMemoryRowsOf 4 =
        [(busSt sdLdAcceptedTrace sdLdSdIndex
          (Pilot.execRowOf sdLdAcceptedTrace sdLdSdIndex)).e2] by rfl]
      rw [sdLdStoreEntry_eq]
      change sdLdStoredMem =
        replayMemoryAfterBusRows sdLdInitialMem
          [ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
            (ZiskFv.AirsClean.Mem.memBusMessage sdMemRow) 1 2]
      simp only [replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil,
        replayMemoryAfterBusRow, if_true, replayStoreEvent_storeEventOfEntry]
      rfl
    · rw [show (⟨5, by omega⟩ : Fin 7) = sdLdLdIndex by rfl]
      rw [show sdLdMemoryRowsOf 5 =
        [(busLd sdLdAcceptedTrace sdLdLdIndex
          (Pilot.execRowOf sdLdAcceptedTrace sdLdLdIndex)).e1] by rfl]
      rw [sdLdLoadEntry_eq]
      change sdLdStoredMem =
        replayMemoryAfterBusRows sdLdStoredMem
          [ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
            (ZiskFv.AirsClean.Mem.memBusMessage ldMemRow) (-1) 2]
      simp only [replayMemoryAfterBusRows, List.foldl_cons, List.foldl_nil]
      exact (replayMemoryAfterBusRow_eq_self_of_read _ _ (by rfl) (by rfl)).symm
  readSoundInputs := by
    intro h_present
    have h_replayRows :
        sdLdAcceptedTrace.memReplayRows h_present = sdLdAcceptedReplayRows := by
      change ZiskFv.AirsClean.FullEnsemble.activeMemReplayRowsOfTable sdLdMemTable =
        sdLdAcceptedReplayRows
      exact sdLdMemTable_activeReplayRows
    refine ⟨?_, ?_⟩
    · have h_first :
          (sdLdAcceptedTrace.memReplayBridge h_present).segment.is_first_segment = 1 := by
        change ZiskFv.AirsClean.Mem.proverDataScalar sdLdMemData
          ZiskFv.AirsClean.Mem.MemRawSidecarDataKey.Segment.isFirstSegment = 1
        exact sdLdMemData_isFirstSegment
      unfold ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      unfold ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts
      unfold ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge
      rw [dif_pos h_first]
      unfold ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge
      change sdLdInitialMem =
        ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
          (ZiskFv.AirsClean.FullEnsemble.activeMemReplayRowsOfTable sdLdMemTable)
      rw [sdLdMemTable_activeReplayRows]
      rfl
    · change MemoryBusRowsReplaySafePermutation _ _
      rw [ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge_rows]
      have h_execution :
          (List.range sdLdAcceptedTrace.numInstructions).flatMap sdLdMemoryRowsOf =
            sdLdAcceptedTrace.memReplayRows h_present := by
        change
          [(busSt sdLdAcceptedTrace sdLdSdIndex
              (Pilot.execRowOf sdLdAcceptedTrace sdLdSdIndex)).e2,
            (busLd sdLdAcceptedTrace sdLdLdIndex
              (Pilot.execRowOf sdLdAcceptedTrace sdLdLdIndex)).e1] =
            sdLdAcceptedTrace.memReplayRows h_present
        rw [sdLdStoreEntry_eq, sdLdLoadEntry_eq, h_replayRows]
        rfl
      rw [h_execution]
      exact MemoryBusRowsReplaySafePermutation.refl _
  memPresent_of_executionRows_nonempty := by
    intro _
    refine ⟨sdLdTableWithData sdLdMemTable, ?_, rfl, ?_⟩
    · simp [sdLdAcceptedTrace, Air.Flat.EnsembleWitness.allTables, sdLdWitness, sdLdTables]
    · norm_num [sdLdTableWithData, sdLdMemTable, memRowsTable, sdLdMemRows]
  placement := by
    intro i
    fin_cases i <;>
      simp [MemoryOpPlacement, sdLdZiskStep, sdLdMemoryRowsOf,
        sdLdSdIndex, sdLdLdIndex]
    all_goals aesop

def sdLdAddiA0OutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdAddiA0Index
      (sdLdZiskStep sdLdAddiA0Index) := by
  unfold RowOutsideDefectRegion sdLdZiskStep MainSequentialPcDomain mainPcVal
  rw [sdLdMainPc]
  change (0 : Nat) < GL_prime - 4
  norm_num

def sdLdSlliOutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdSlliIndex
      (sdLdZiskStep sdLdSlliIndex) := by
  unfold RowOutsideDefectRegion sdLdZiskStep MainSequentialPcDomain mainPcVal
  rw [sdLdMainPc]
  change (4 : Nat) < GL_prime - 4
  norm_num

def sdLdAddiEightOutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdAddiEightIndex
      (sdLdZiskStep sdLdAddiEightIndex) := by
  unfold RowOutsideDefectRegion sdLdZiskStep MainSequentialPcDomain mainPcVal
  rw [sdLdMainPc]
  change (8 : Nat) < GL_prime - 4
  norm_num

def sdLdAddiX2OutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdAddiX2Index
      (sdLdZiskStep sdLdAddiX2Index) := by
  unfold RowOutsideDefectRegion sdLdZiskStep MainSequentialPcDomain mainPcVal
  rw [sdLdMainPc]
  change (12 : Nat) < GL_prime - 4
  norm_num

def sdLdSdOutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdSdIndex
      (sdLdZiskStep sdLdSdIndex) := by
  unfold RowOutsideDefectRegion sdLdZiskStep MainSequentialPcDomain mainPcVal
  rw [sdLdMainPc]
  change (16 : Nat) < GL_prime - 4
  norm_num

def sdLdLdOutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdLdIndex
      (sdLdZiskStep sdLdLdIndex) := by
  unfold RowOutsideDefectRegion sdLdZiskStep MainSequentialPcDomain mainPcVal
  rw [sdLdMainPc]
  change (20 : Nat) < GL_prime - 4
  norm_num

def sdLdJalOutsideDefectRegion :
    RowOutsideDefectRegion sdLdAcceptedTrace sdLdJalIndex
      (sdLdZiskStep sdLdJalIndex) where
  h_no_fgl_wrap := by
    unfold mainPcVal
    rw [sdLdMainPc]
    change 24 + (BitVec.signExtend 64 (0#21)).toNat < GL_prime
    simp
  h_pc_bound := by
    unfold MainSequentialPcDomain mainPcVal
    rw [sdLdMainPc]
    change 24 < GL_prime - 4
    norm_num
  h_pc_offset_lt_2_32 := by
    intro pc hpc
    unfold mainPcVal at hpc
    rw [sdLdMainPc] at hpc
    rw [BitVec.toNat_add]
    rw [← hpc]
    norm_num [sdLdJalIndex]

def sdLdOutsideDefectRegion :
    ∀ i : Fin 7, RowOutsideDefectRegion sdLdAcceptedTrace i (sdLdZiskStep i)
  | ⟨0, _⟩ => sdLdAddiA0OutsideDefectRegion
  | ⟨1, _⟩ => sdLdSlliOutsideDefectRegion
  | ⟨2, _⟩ => sdLdAddiEightOutsideDefectRegion
  | ⟨3, _⟩ => sdLdAddiX2OutsideDefectRegion
  | ⟨4, _⟩ => sdLdSdOutsideDefectRegion
  | ⟨5, _⟩ => sdLdLdOutsideDefectRegion
  | ⟨6, _⟩ => sdLdJalOutsideDefectRegion

theorem sdLdRootSoundness :
    ∀ i : Fin 7, StepSound sdLdAcceptedTrace sdLdSailTrace i (sdLdZiskStep i) :=
  root_soundness 7 sdLdAcceptedTrace sdLdSailTrace sdLdZiskStep
    sdLdProgramDecodes sdLdInputsAgree sdLdBootSeed sdLdOutsideDefectRegion

theorem sdLdAddiA0StepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdAddiA0Index
      (sdLdZiskStep sdLdAddiA0Index) :=
  sdLdRootSoundness sdLdAddiA0Index

theorem sdLdSlliStepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdSlliIndex
      (sdLdZiskStep sdLdSlliIndex) :=
  sdLdRootSoundness sdLdSlliIndex

theorem sdLdAddiEightStepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdAddiEightIndex
      (sdLdZiskStep sdLdAddiEightIndex) :=
  sdLdRootSoundness sdLdAddiEightIndex

theorem sdLdAddiX2StepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdAddiX2Index
      (sdLdZiskStep sdLdAddiX2Index) :=
  sdLdRootSoundness sdLdAddiX2Index

theorem sdLdSdStepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdSdIndex
      (sdLdZiskStep sdLdSdIndex) :=
  sdLdRootSoundness sdLdSdIndex

theorem sdLdLdStepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdLdIndex
      (sdLdZiskStep sdLdLdIndex) :=
  sdLdRootSoundness sdLdLdIndex

theorem sdLdJalStepSound :
    StepSound sdLdAcceptedTrace sdLdSailTrace sdLdJalIndex
      (sdLdZiskStep sdLdJalIndex) :=
  sdLdRootSoundness sdLdJalIndex

end ZiskFv.Compliance.SdLdSpinRootSoundness
