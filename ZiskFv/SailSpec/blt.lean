import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  structure BltInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BltOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BLT_pure (input : BltInput) : BltOutput :=
    let skip := !(input.r1_val.toInt <b input.r2_val.toInt)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BltOutput
    }

  set_option maxHeartbeats 400000 in
  /-- BLT Sail-equivalence: the `do` block consisting of a default
      `nextPC ← PC + 4` write followed by `execute (.BTYPE imm r2 r1 BLT)`
      equals the pure-spec block (signed less-than; on taken, jump to
      `PC + imm` with throws/fails on misaligned target; on not-taken,
      fall through to `PC + 4`).

      Structure mirrors `execute_BNE_pure_equiv` with the case-split
      predicate swapped to `h_lt : r1_val.toInt < r2_val.toInt`. Sail's
      `execute_BTYPE` BLT arm emits `zopz0zI_s (rX rs1) (rX rs2)` which
      unfolds to `.toInt <b .toInt` — syntactically identical to the
      pure-spec's `skip := !(.toInt <b .toInt)` once `h_lt` is decided.
      Polarity versus BNE is flipped: the `h_lt = true` branch is the
      **taken** branch (needs `jump_to_equiv`), whereas BNE's first
      branch was not-taken. -/
  lemma execute_BLT_pure_equiv
    (blt_input : BltInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: blt_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (blt_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (blt_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BLT ))
    ) state =
    let blt_output := execute_BLT_pure blt_input
    (do
      Sail.writeReg Register.nextPC blt_output.nextPC
      if blt_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !blt_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (blt_input.PC + BitVec.signExtend 64 blt_input.imm)),
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

    -- Case-split on the signed less-than that selects BLT's taken/not-taken.
    -- For BLT: h_lt true → taken (jump_to); h_lt false → not-taken (PC+4).
    by_cases h_lt : blt_input.r1_val.toInt < blt_input.r2_val.toInt <;>
      simp [h_lt, execute_BLT_pure]
    -- Taken case (h_lt): BLT jumps to PC + imm via `jump_to`.
    have h_pc_post : (write_reg_state state Register.nextPC (blt_input.PC + 4#64)).regs.get? Register.PC
        = .some blt_input.PC :=
      writeReg_read_diff h_input_pc (by decide)
    rewrite [readReg_succ h_pc_post]
    simp
    have h_misa_post : (write_reg_state state Register.nextPC (blt_input.PC + 4#64)).regs.get? Register.misa
        = .some misa_val :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (blt_input.PC + 4#64)))
      (misa_val := misa_val)
      (target := blt_input.PC + BitVec.signExtend 64 imm)
      h_misa_post
      h_misa_c]
    -- Case-split on low 2 bits of the target for throws/fails.
    by_cases h_throws : (execute_BLT_pure blt_input).throws <;>
    simp_all [execute_BLT_pure]
    . by_cases h_success : (execute_BLT_pure blt_input).success
      . simp [execute_BLT_pure, h_lt, h_throws, h_input_imm] at h_success
        repeat rw [if_neg (by omega)]
        simp
      . simp [execute_BLT_pure, h_lt, h_throws, h_input_imm] at h_success
        repeat rw [if_pos (by omega)]
        simp

  /-- **BLT next-PC under success.** Projects the pure-spec `nextPC` to the clean
      Sail conditional `if (r1 <s r2) then PC + signExtend imm else PC + 4`, valid
      once the taken branch did not fault. Signed sibling of
      `execute_BLTU_pure_nextPC_of_success`; consumed by `stepStrong_blt`. -/
  lemma execute_BLT_pure_nextPC_of_success (bi : BltInput)
      (h_success : (execute_BLT_pure bi).success = true) :
      (execute_BLT_pure bi).nextPC
        = if BitVec.slt bi.r1_val bi.r2_val
          then bi.PC + BitVec.signExtend 64 bi.imm
          else bi.PC + 4#64 := by
    simp only [show BitVec.slt bi.r1_val bi.r2_val
        = (bi.r1_val.toInt <b bi.r2_val.toInt) from rfl]
    cases h : bi.r1_val.toInt <b bi.r2_val.toInt with
    | false => simp [execute_BLT_pure, h]
    | true => simp_all [execute_BLT_pure]

end PureSpec
