import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  structure BgeuInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BgeuOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BGEU_pure (input : BgeuInput) : BgeuOutput :=
    let skip := !(input.r1_val.toNat ≥b input.r2_val.toNat)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BgeuOutput
    }

  set_option maxHeartbeats 400000 in
  /-- BGEU Sail-equivalence: unsigned greater-equal sibling of BGE /
      BLTU. Closure shape identical to BLTU with `≥` swapped for `<`. -/
  lemma execute_BGEU_pure_equiv
    (bgeu_input : BgeuInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bgeu_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bgeu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bgeu_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BGEU ))
    ) state =
    let bgeu_output := execute_BGEU_pure bgeu_input
    (do
      Sail.writeReg Register.nextPC bgeu_output.nextPC
      if bgeu_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bgeu_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm)),
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

    -- Case-split on unsigned ≥ (BGEU taken when r1.toNat ≥ r2.toNat).
    by_cases h_ge : bgeu_input.r1_val.toNat ≥ bgeu_input.r2_val.toNat <;>
      simp [h_ge, execute_BGEU_pure]
    have h_pc_post : (write_reg_state state Register.nextPC (bgeu_input.PC + 4#64)).regs.get? Register.PC
        = .some bgeu_input.PC :=
      writeReg_read_diff h_input_pc (by decide)
    rewrite [readReg_succ h_pc_post]
    simp
    have h_misa_post : (write_reg_state state Register.nextPC (bgeu_input.PC + 4#64)).regs.get? Register.misa
        = .some misa_val :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (bgeu_input.PC + 4#64)))
      (misa_val := misa_val)
      (target := bgeu_input.PC + BitVec.signExtend 64 imm)
      h_misa_post
      h_misa_c]
    by_cases h_throws : (execute_BGEU_pure bgeu_input).throws <;>
    simp_all [execute_BGEU_pure]
    . by_cases h_success : (execute_BGEU_pure bgeu_input).success
      . simp [execute_BGEU_pure, h_ge, h_throws, h_input_imm] at h_success
        repeat rw [if_neg (by omega)]
        simp
      . simp [execute_BGEU_pure, h_ge, h_throws, h_input_imm] at h_success
        repeat rw [if_pos (by omega)]
        simp

  /-- **BGEU next-PC under success.** Projects the pure-spec `nextPC` to the
      clean Sail conditional `if (r1 <u r2) then PC + 4 else PC + signExtend imm`
      (taken on `r1 ≥u r2`, i.e. `flag = 0`), valid once the taken branch did not
      fault. Consumed by the #100 branch next-PC discharge (`stepStrong_bgeu`). -/
  lemma execute_BGEU_pure_nextPC_of_success (bi : BgeuInput)
      (h_success : (execute_BGEU_pure bi).success = true) :
      (execute_BGEU_pure bi).nextPC
        = if BitVec.ult bi.r1_val bi.r2_val
          then bi.PC + 4#64
          else bi.PC + BitVec.signExtend 64 bi.imm := by
    have hult : BitVec.ult bi.r1_val bi.r2_val
        = !(bi.r1_val.toNat ≥b bi.r2_val.toNat) := by
      simp [BitVec.ult, ge_iff_le, ← decide_not, Nat.not_le]
    rw [hult]
    cases h : bi.r1_val.toNat ≥b bi.r2_val.toNat with
    | false => simp [execute_BGEU_pure, h]
    | true => simp_all [execute_BGEU_pure]

end PureSpec
