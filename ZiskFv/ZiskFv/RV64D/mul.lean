import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure MulInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure MulOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_MULH_mul_pure (input : MulInput) : MulOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        (execute_MUL_pure input.r1_val input.r2_val .MUL)
      )
    : MulOutput
  }

  lemma execute_MULH_mul_pure_equiv
    (mul_input : MulInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mul_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mul_input.r2_val) state)
    (h_input_rd: mul_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some mul_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.Low, signed_rs1 := srs1, signed_rs2 := srs2 }))
    ) state =
    let mul_output := execute_MULH_mul_pure mul_input
    (do
      Sail.writeReg Register.nextPC mul_output.nextPC
      match mul_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
