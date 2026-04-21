import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure AddiInput where
    -- operands
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure AddiOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_addi_pure (input : AddiInput) : AddiOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val + BitVec.signExtend 64 input.imm
      )
    : AddiOutput
  }

  lemma execute_ITYPE_addi_pure_equiv
    (addi_input : AddiInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (addi_input.r1_val) state)
    (h_input_imm: addi_input.imm = imm)
    (h_input_rd: addi_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some addi_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))
    ) state =
    let addi_output := execute_ITYPE_addi_pure addi_input
    (do
      Sail.writeReg Register.nextPC addi_output.nextPC
      match addi_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
