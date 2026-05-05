import ZiskFv.Sail.Auxiliaries
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

  /-- RV64 MUL Sail-equivalence (Phase 2 A5-RV64D).

      Mirrors the RV64 `execute_RTYPE_add_pure_equiv` proof shape: strip the
      monadic bindings via the register-read lemmas (`rX_read_xreg_equiv`,
      `read_xreg_write_other_reg_state`), collapse `execute_MUL` to
      `execute_MUL'` via the `Fundamentals/Execution` lemma
      `execute_MUL_eq_execute_MUL'`, then case-split on `rd = 0` to hit the
      `write_xreg` zero/non-zero lemmas.

      Restricted to the MUL (`.MUL` / Low half) case: the input carries a
      `result_part = .Low` discriminator so `mop_of_mul_op` collapses the
      signed/unsigned combinations into the single `.MUL` flavour. MULH /
      MULHU / MULHSU are covered by sibling archetypes (they will share
      the same proof skeleton parameterized on the `mop` constructor). -/
  lemma execute_MULH_mul_pure_equiv
    (mul_input : MulInput)
    (r1 r2 rd: regidx)
    (srs1 srs2 : Signedness)
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
  := by
    -- Mirror the RV64 ADD proof: reduce PC write + `LeanRV64D.Functions.execute`
    -- to `execute_MUL'` via the MUL↔MUL' equivalence.
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_MUL'
    ]

    -- Register reads: rewrite `rX_bits` to `read_xreg`, then use the
    -- write-other-reg commute to pass the `nextPC` write through.
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_MUL_pure,
      execute_MULH_mul_pure,
      mop_of_mul_op
    ]

    -- Case-split rd = 0 vs. nonzero for `write_xreg`.
    obtain ⟨rd⟩ := rd
    by_cases h_zero: rd = 0
    . rewrite [h_zero, wX_write_xreg_zero_equiv]
      simp
      rewrite [dite_cond_eq_true]
      . simp
      . simp [h_input_rd, h_zero, regidx_to_fin]
    . have h_inc := regidx_non_zero h_zero
      apply Finset.mem_Icc.mp at h_inc
      obtain ⟨h_low, h_high⟩ := h_inc
      rewrite [
        wX_write_xreg_non_zero_equiv _ _
          (regidx.Regidx rd)
          ⟨(regidx_to_fin (regidx.Regidx rd)).val, Finset.mem_Icc.mpr ⟨h_low, h_high⟩⟩
          (by simp [regidx_to_fin])
      ]
      simp [regidx_to_fin]
      rewrite [dite_cond_eq_false]
      . simp [h_input_rd, regidx_to_fin]
      . simp [regidx_to_fin] at *
        omega

end PureSpec
