import ZiskFv.Compliance.DivSpinRootSoundness.ProgramDecodes

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.AirsClean.Main
open ZiskFv.Trusted

namespace ZiskFv.Compliance.DivSpinRootSoundness

private def divSpinAddiInput
    (index : Fin 4) (claim : Claim_addi divSpinAcceptedTrace index)
    (input : PureSpec.AddiInput)
    (h_read :
      read_xreg (regidx_to_fin claim.r1) (divSpinSailTrace index) =
        EStateM.Result.ok input.r1_val (divSpinSailTrace index))
    (h_imm : input.imm = claim.imm)
    (h_pc : (divSpinSailTrace index).regs.get? Register.PC = .some input.PC)
    (h_rd : input.rd = regidx_to_fin claim.rd)
    (h_a0 :
      (divSpinMainRows[index.val]'(by change index.val < 5; omega)).core.a_0 =
        lane_lo input.r1_val)
    (h_a1 :
      (divSpinMainRows[index.val]'(by change index.val < 5; omega)).core.a_1 =
        lane_hi input.r1_val)
    (h_pc_bridge : (((4 * index.val : Nat) : FGL).val) = input.PC.toNat) :
    Inputs_addi divSpinAcceptedTrace divSpinSailTrace index claim where
  addi_input := input
  h_input_r1 := h_read
  h_input_imm := h_imm
  h_input_pc := h_pc
  h_input_rd := h_rd
  h_a_hi_t := by
    rw [ZiskFv.AirsClean.FullEnsemble.mainOfTable_a_1]
    change
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
        divSpinAcceptedTrace.program divSpinAcceptedTrace.mainTable index.val).core.a_1 = _
    rw [congrArg (fun row => row.core.a_1) (divSpinAcceptedMainRowAt index)]
    rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
      (divSpinSailTrace index) (regidx_to_fin claim.r1) input.r1_val h_read]
    exact h_a1
  h_pc_bridge := by
    rw [divSpinMainPc]
    exact h_pc_bridge

def divSpinAddiX1Inputs :
    Inputs_addi divSpinAcceptedTrace divSpinSailTrace divSpinAddiX1Index
      divSpinAddiX1Claim :=
  divSpinAddiInput divSpinAddiX1Index divSpinAddiX1Claim divSpinAddiX1Input
    (by simpa [divSpinAddiX1Claim, divSpinAddiX1Input] using
      divSpinReadX0 divSpinAddiX1Index)
    rfl
    (by
      simp [divSpinSailTrace, divSpinAddiX1Index, divSpinState, divSpinRegs,
        divSpinAddiX1Input, x1, x2, x3, regidx_to_fin, reg_of_fin,
        Std.ExtDHashMap.get?_insert])
    rfl
    (by
      norm_num [divSpinAddiX1Index, divSpinMainRows, divSpinAddiX1Row,
        divSpinAddiX1RowTemplate, mainRomRowOf, divSpinAddiX1Input, lane_lo])
    (by
      norm_num [divSpinAddiX1Index, divSpinMainRows, divSpinAddiX1Row,
        divSpinAddiX1RowTemplate, mainRomRowOf, divSpinAddiX1Input, lane_hi])
    (by norm_num [divSpinAddiX1Index, divSpinAddiX1Input])

def divSpinAddiX2Inputs :
    Inputs_addi divSpinAcceptedTrace divSpinSailTrace divSpinAddiX2Index
      divSpinAddiX2Claim :=
  divSpinAddiInput divSpinAddiX2Index divSpinAddiX2Claim divSpinAddiX2Input
    (by simpa [divSpinAddiX2Claim, divSpinAddiX2Input] using
      divSpinReadX0 divSpinAddiX2Index)
    rfl
    (by
      simp [divSpinSailTrace, divSpinAddiX2Index, divSpinState, divSpinRegs,
        divSpinAddiX2Input, x1, x2, x3, regidx_to_fin, reg_of_fin,
        Std.ExtDHashMap.get?_insert])
    rfl
    (by
      norm_num [divSpinAddiX2Index, divSpinMainRows, divSpinAddiX2Row,
        divSpinAddiX2RowTemplate, mainRomRowOf, divSpinAddiX2Input, lane_lo])
    (by
      norm_num [divSpinAddiX2Index, divSpinMainRows, divSpinAddiX2Row,
        divSpinAddiX2RowTemplate, mainRomRowOf, divSpinAddiX2Input, lane_hi])
    (by norm_num [divSpinAddiX2Index, divSpinAddiX2Input])

end ZiskFv.Compliance.DivSpinRootSoundness
