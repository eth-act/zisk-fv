import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure XoriInput where
    -- operands
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure XoriOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_xori_pure (input : XoriInput) : XoriOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val ^^^ BitVec.signExtend 64 input.imm
      )
    : XoriOutput
  }

  lemma execute_ITYPE_xori_pure_equiv
    (xori_input : XoriInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (xori_input.r1_val) state)
    (h_input_imm: xori_input.imm = imm)
    (h_input_rd: xori_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some xori_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.XORI))
    ) state =
    let xori_output := execute_ITYPE_xori_pure xori_input
    (do
      Sail.writeReg Register.nextPC xori_output.nextPC
      match xori_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
