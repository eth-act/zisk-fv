import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

namespace PureSpec

structure SltInput where
  -- operands
  r1_val : BitVec 64
  r2_val : BitVec 64
  rd : Fin 32
  -- registers
  PC : BitVec 64

structure SltOutput where
  -- registers
  nextPC : BitVec 64
  rd : Option (Finset.Icc 1 31 × BitVec 64)

def execute_RTYPE_slt_pure (input : SltInput) : SltOutput := {
  nextPC := input.PC + 4#64
  rd := if h: input.rd = 0
    then .none
    else .some (
      ⟨
        input.rd.val,
        by apply Finset.mem_Icc.mpr; omega
      ⟩,
      if input.r1_val.slt input.r2_val
      then 1#64
      else 0#64
    )
  : SltOutput
}

lemma execute_RTYPE_slt_pure_equiv
  (slt_input : SltInput)
  (r1 r2 rd: regidx)
  (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (slt_input.r1_val) state)
  (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (slt_input.r2_val) state)
  (h_input_rd: slt_input.rd = regidx_to_fin rd)
  (h_input_pc: state.regs.get? Register.PC = .some slt_input.PC)
:
  (
    do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.RTYPE (r2, r1, rd, rop.SLT))
  ) state =
  let slt_output := execute_RTYPE_slt_pure slt_input
  (do
    Sail.writeReg Register.nextPC slt_output.nextPC
    match slt_output.rd with
      | .some (rd, rd_val) => write_xreg rd rd_val
      | .none => pure ()
    pure (ExecutionResult.Retire_Success ())
  ) state
:= sorry

end PureSpec
