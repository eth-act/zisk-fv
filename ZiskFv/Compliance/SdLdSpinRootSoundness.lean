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

def sdLdRegs (pc x1Value x2Value x3Value : BitVec 64) :
    Std.ExtDHashMap Register RegisterType :=
  let regs0 := (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC pc
  let regs2 := regs1.insert Register.misa sdLdMisa
  let regs3 := regs2.insert (reg_of_fin (regidx_to_fin x1)) x1Value
  let regs4 := regs3.insert (reg_of_fin (regidx_to_fin x2)) x2Value
  regs4.insert (reg_of_fin (regidx_to_fin x3)) x3Value

def sdLdStoredMem : Std.ExtHashMap Nat (BitVec 8) :=
  (((((((({} : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 2684354568 (42#8))
    |>.insert 2684354569 (0#8))
    |>.insert 2684354570 (0#8))
    |>.insert 2684354571 (0#8))
    |>.insert 2684354572 (0#8))
    |>.insert 2684354573 (0#8))
    |>.insert 2684354574 (0#8))
    |>.insert 2684354575 (0#8)

def sdLdState (pc x1Value x2Value x3Value : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := sdLdRegs pc x1Value x2Value x3Value
    mem := mem }

def sdLdSailTrace : SailTrace 7
  | ⟨0, _⟩ => sdLdState (0#64) (0#64) (0#64) (0#64) {}
  | ⟨1, _⟩ => sdLdState (4#64) (160#64) (0#64) (0#64) {}
  | ⟨2, _⟩ => sdLdState (8#64) (2684354560#64) (0#64) (0#64) {}
  | ⟨3, _⟩ => sdLdState (12#64) (2684354568#64) (0#64) (0#64) {}
  | ⟨4, _⟩ => sdLdState (16#64) (2684354568#64) (42#64) (0#64) {}
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

end ZiskFv.Compliance.SdLdSpinRootSoundness
