import ZiskFv.Sail.Auxiliaries

namespace PureSpec

  structure BneInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BneOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BNE_pure (input : BneInput) : BneOutput :=
    let skip := !(input.r1_val != input.r2_val)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BneOutput
    }

  lemma execute_BNE_pure_succ_throws
    (input : BneInput)
  :
    let output := execute_BNE_pure input
    output.success = true → output.throws = false
  := by
    simp [execute_BNE_pure]
    grind

  set_option maxHeartbeats 400000 in
  /-- BNE Sail-equivalence: mirrors `execute_BEQ_pure_equiv` with
      the case-split polarity flipped.

      Structure: Sail's `execute_BTYPE` on `BNE` evaluates
      `rX rs1 != rX rs2` as the `taken` predicate. The pure-spec
      `skip` variable is `!(r1_val != r2_val) = (r1_val == r2_val)`,
      i.e. skip = equal → not-taken for BNE. The two cases in the
      `by_cases h_eq : r1_val = r2_val` split are therefore reversed
      relative to BEQ:
        * `h_eq` (values equal) → BNE NOT-taken → `nextPC = PC + 4`,
        * `¬ h_eq` (values unequal) → BNE TAKEN → `jump_to` path.

      Uses `jump_to_equiv` (RV64) with the `misa[C] = 0` witness to
      collapse the `jump_to` call in the taken branch. -/
  lemma execute_BNE_pure_equiv
    (bne_input : BneInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bne_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bne_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bne_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BNE ))
    ) state =
    let bne_output := execute_BNE_pure bne_input
    (do
      Sail.writeReg Register.nextPC bne_output.nextPC
      if bne_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bne_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 64 bne_input.imm)),
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

    -- Case-split on r1 = r2. For BNE:
    --   * r1 = r2 → skip = true  → not-taken → nextPC stays at PC+4
    --   * r1 ≠ r2 → skip = false → taken     → jump_to PC+imm
    by_cases h_eq: bne_input.r1_val = bne_input.r2_val <;>
      simp [h_eq, execute_BNE_pure]
    -- Taken case (¬ h_eq): BNE jumps to PC + imm via `jump_to`.
    -- Prepare PC read on the `write_reg_state Register.nextPC`-updated state.
    have h_pc_post : (write_reg_state state Register.nextPC (bne_input.PC + 4#64)).regs.get? Register.PC
        = .some bne_input.PC :=
      writeReg_read_diff h_input_pc (by decide)
    rewrite [readReg_succ h_pc_post]
    simp
    -- Apply `jump_to_equiv` with the misa witness threaded through the
    -- intermediate register-write state.
    have h_misa_post : (write_reg_state state Register.nextPC (bne_input.PC + 4#64)).regs.get? Register.misa
        = .some misa_val :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (bne_input.PC + 4#64)))
      (misa_val := misa_val)
      (target := bne_input.PC + BitVec.signExtend 64 imm)
      h_misa_post
      h_misa_c]
    -- Case-split on low 2 bits of the target for throws/fails.
    by_cases h_throws : (execute_BNE_pure bne_input).throws <;>
    simp_all [execute_BNE_pure]
    . by_cases h_success : (execute_BNE_pure bne_input).success
      . simp [execute_BNE_pure, h_eq, h_throws, h_input_imm] at h_success
        repeat rw [if_neg (by omega)]
        simp
      . simp [execute_BNE_pure, h_eq, h_throws, h_input_imm] at h_success
        repeat rw [if_pos (by omega)]
        simp

end PureSpec
