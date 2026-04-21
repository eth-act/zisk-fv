import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure SrliInput where
    -- opersrls
    r1_val : BitVec 64
    imm : BitVec 6
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SrliOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_SHIFTIOP_srli_pure (input : SrliInput) : SrliOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val >>> (input.imm % 32)
      )
    : SrliOutput
  }

  lemma execute_SHIFTIOP_srli_pure_equiv
    (srli_input : SrliInput)
    (r1 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (srli_input.r1_val) state)
    (h_input_imm: srli_input.imm = imm)
    (h_input_rd: srli_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some srli_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.SHIFTIOP (imm, r1, rd, sop.SRLI))
    ) state =
    let srli_output := execute_SHIFTIOP_srli_pure srli_input
    (do
      Sail.writeReg Register.nextPC srli_output.nextPC
      match srli_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
