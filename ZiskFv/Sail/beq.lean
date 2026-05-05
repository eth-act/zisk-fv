import ZiskFv.Sail.Auxiliaries

namespace PureSpec

  structure BeqInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BeqOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BEQ_pure (input : BeqInput) : BeqOutput :=
    let skip := !(input.r1_val == input.r2_val)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BeqOutput
    }

  lemma execute_BEQ_pure_succ_throws
    (input : BeqInput)
  :
    let output := execute_BEQ_pure input
    output.success = true → output.throws = false
  := by
    simp [execute_BEQ_pure]
    grind

  @[simp]
  lemma sign_extend_equiv :
    @LeanRV64D.Functions.sign_extend width1 width2 =
    @BitVec.signExtend width1 width2
  := rfl

  /-- BEQ Sail-equivalence: the `do` block consisting of a default
      `nextPC ← PC + 4` write followed by `execute (.BTYPE imm r2 r1 BEQ)`
      equals the pure-spec block that (a) writes the taken/not-taken
      `nextPC`, (b) raises `Assertion`/`Memory_Exception` on misaligned
      targets, and (c) retires otherwise.

      Closed via `jump_to_equiv` (now available post-Phase 1.5: the
      `misa[C] = 0` hypothesis is threaded from the `h_input_misa`
      assumption). The structure follows the RV32 sibling
      `OpenvmFv/RV32D/beq.lean` one-for-one, with the RV32→RV64 width
      adjustments (`signExtend 32 → signExtend 64`). -/
  lemma execute_BEQ_pure_equiv
    (beq_input : BeqInput)
    (imm: BitVec 13)
    (h_input_imm: beq_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (beq_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (beq_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BEQ ))
    ) state =
    let beq_output := execute_BEQ_pure beq_input
    (do
      Sail.writeReg Register.nextPC beq_output.nextPC
      if beq_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !beq_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
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

    -- Case-split on the equality r1 == r2 that selects BEQ's taken/not-taken.
    by_cases h_eq: beq_input.r1_val = beq_input.r2_val <;>
      simp [h_eq, execute_BEQ_pure]
    -- Taken case: BEQ jumps to PC + imm via `jump_to`. Close via
    -- `jump_to_equiv` (needs PC readable and misa bit 2 = 0).
    -- Prepare PC read on the `write_reg_state Register.nextPC`-updated state.
    have h_pc_post : (write_reg_state state Register.nextPC (beq_input.PC + 4#64)).regs.get? Register.PC
        = .some beq_input.PC :=
      writeReg_read_diff h_input_pc (by decide)
    rewrite [readReg_succ h_pc_post]
    simp
    -- Apply `jump_to_equiv` with the misa witness threaded through the
    -- intermediate register-write state.
    have h_misa_post : (write_reg_state state Register.nextPC (beq_input.PC + 4#64)).regs.get? Register.misa
        = .some misa_val :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (beq_input.PC + 4#64)))
      (misa_val := misa_val)
      (target := beq_input.PC + BitVec.signExtend 64 imm)
      h_misa_post
      h_misa_c]
    -- Case-split on low 2 bits of the target for throws/fails.
    by_cases h_throws : (execute_BEQ_pure beq_input).throws <;>
    simp_all [execute_BEQ_pure]
    . by_cases h_success : (execute_BEQ_pure beq_input).success
      . simp [execute_BEQ_pure, h_eq, h_throws, h_input_imm] at h_success
        repeat rw [if_neg (by omega)]
        simp
      . simp [execute_BEQ_pure, h_eq, h_throws, h_input_imm] at h_success
        repeat rw [if_pos (by omega)]
        simp

end PureSpec
