import ZiskFv.Sail.Auxiliaries

namespace PureSpec

  structure BltuInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BltuOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BLTU_pure (input : BltuInput) : BltuOutput :=
    let skip := !(input.r1_val.toNat <b input.r2_val.toNat)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BltuOutput
    }

  set_option maxHeartbeats 400000 in
  /-- BLTU Sail-equivalence: unsigned less-than sibling of BLT. Sail's
      `zopz0zI_u` unfolds to `.toNatInt <b .toNatInt`, and
      `Sail.BitVec.toNatInt x = Int.ofNat x.toNat`, so after the simp
      set and `Int.ofNat_lt_ofNat` reflect, this reduces to the pure
      spec's `.toNat <b .toNat` form. Same taken-polarity as BLT. -/
  lemma execute_BLTU_pure_equiv
    (bltu_input : BltuInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bltu_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bltu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bltu_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BLTU ))
    ) state =
    let bltu_output := execute_BLTU_pure bltu_input
    (do
      Sail.writeReg Register.nextPC bltu_output.nextPC
      if bltu_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bltu_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    simp [
      readReg_succ h_input_pc,
      LeanRV64D.Functions.execute,
      writeReg_state_success,
      LeanRV64D.Functions.execute_BTYPE
    ]
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by { simp [regidx_to_fin] })]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by { simp [regidx_to_fin] })]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp

    -- Case-split on unsigned less-than (BLTU taken when r1.toNat < r2.toNat).
    by_cases h_lt : bltu_input.r1_val.toNat < bltu_input.r2_val.toNat <;>
      simp [h_lt, execute_BLTU_pure]
    have h_pc_post : (write_reg_state state Register.nextPC (bltu_input.PC + 4#64)).regs.get? Register.PC
        = .some bltu_input.PC :=
      writeReg_read_diff h_input_pc (by decide)
    rewrite [readReg_succ h_pc_post]
    simp
    have h_misa_post : (write_reg_state state Register.nextPC (bltu_input.PC + 4#64)).regs.get? Register.misa
        = .some misa_val :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (bltu_input.PC + 4#64)))
      (misa_val := misa_val)
      (target := bltu_input.PC + BitVec.signExtend 64 imm)
      h_misa_post
      h_misa_c]
    by_cases h_throws : (execute_BLTU_pure bltu_input).throws <;>
    simp_all [execute_BLTU_pure]
    . by_cases h_success : (execute_BLTU_pure bltu_input).success
      . simp [execute_BLTU_pure, h_lt, h_throws, h_input_imm] at h_success
        repeat rw [if_neg (by omega)]
        simp
      . simp [execute_BLTU_pure, h_lt, h_throws, h_input_imm] at h_success
        repeat rw [if_pos (by omega)]
        simp

end PureSpec
