import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure MulhInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure MulhOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_MULH_mulh_pure (input : MulhInput) : MulhOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        (execute_MUL_pure input.r1_val input.r2_val .MULH)
      )
    : MulhOutput
  }

  lemma execute_MULH_mulh_pure_equiv
    (mulh_input : MulhInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mulh_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mulh_input.r2_val) state)
    (h_input_rd: mulh_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some mulh_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Signed }))
    ) state =
    let mulh_output := execute_MULH_mulh_pure mulh_input
    (do
      Sail.writeReg Register.nextPC mulh_output.nextPC
      match mulh_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
