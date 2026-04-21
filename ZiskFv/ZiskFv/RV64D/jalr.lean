import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure JalrInput where
    -- operands
    imm : BitVec 12
    rs1_val: BitVec 64
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure JalrOutput where
    -- registers
    nextPC : Option (BitVec 64)
    rd : Option (Finset.Icc 1 31 × BitVec 64)
    -- result
    success : Bool

  def execute_JALR_pure (input : JalrInput) : JalrOutput :=
    let bit1_valid := (BitVec.ofBool (input.rs1_val + BitVec.signExtend 64 input.imm)[1]! == 0#1)
    let mask := 0xFFFFFFFE
    {
      nextPC :=
        if (!bit1_valid)
        then (.some (input.PC + 4))
        else (.some (mask &&& (input.rs1_val + BitVec.signExtend 64 input.imm)))
      rd := if h: (!bit1_valid) || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := (bit1_valid)
    }

  set_option maxHeartbeats 0 in
  lemma execute_JALR_pure_equiv
    (input : JalrInput)
    (imm: BitVec 12)
    (rs1 rd: regidx)
    (h_input_imm: input.imm = imm)
    (h_input_rd: input.rd = regidx_to_fin rd)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))
    ) state =
    let output := execute_JALR_pure input
    (do
      match output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if !output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (0xFFFFFFFE &&& (input.rs1_val + BitVec.signExtend 64 input.imm))),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := sorry

end PureSpec
