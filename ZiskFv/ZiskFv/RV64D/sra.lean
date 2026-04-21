import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

  structure SraInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SraOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_RTYPE_sra_pure (input : SraInput) : SraOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        input.r1_val.sshiftRight (input.r2_val.toNat % 32)
      )
    : SraOutput
  }

  lemma execute_RTYPE_sra_pure_equiv
    (sra_input : SraInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (sra_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (sra_input.r2_val) state)
    (h_input_rd: sra_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some sra_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.RTYPE (r2, r1, rd, rop.SRA))
    ) state =
    let sra_output := execute_RTYPE_sra_pure sra_input
    (do
      Sail.writeReg Register.nextPC sra_output.nextPC
      match sra_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
