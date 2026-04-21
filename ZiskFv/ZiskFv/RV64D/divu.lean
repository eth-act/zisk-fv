import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure DivuInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure DivuOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_DIVREM_divu_pure (input : DivuInput) : DivuOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        (execute_DIV_REM_pure input.r1_val input.r2_val .DRU).1
      )
    : DivuOutput
  }

  lemma execute_DIVREM_divu_pure_equiv
    (divu_input : DivuInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (divu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (divu_input.r2_val) state)
    (h_input_rd: divu_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some divu_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, true))
    ) state =
    let divu_output := execute_DIVREM_divu_pure divu_input
    (do
      Sail.writeReg Register.nextPC divu_output.nextPC
      match divu_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
