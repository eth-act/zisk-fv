import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 MULW (32-bit multiply). Phase 3A M3.

Takes the low 32 bits of `rs1` and `rs2` as signed 32-bit integers,
multiplies them, truncates the product to 32 bits, and sign-extends
the 32-bit result back to 64. No PC jump; write to `rd`; advance PC
by 4.

The pure spec mirrors LeanRV64D's `execute_MULW`
(`InstsEnd.lean:66799-66806`) with the obvious let-bindings inlined.
Unlike `execute_MUL`, there is no `execute_MULW'` helper in
`Fundamentals/Execution.lean`, so the Sail-equivalence proof below
unfolds `execute_MULW` directly (same skeleton as ADD modulo the
extra `extractLsb` / `sign_extend` plumbing).
-/

namespace PureSpec

  structure MulwInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure MulwOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure MULW semantics. Extract low 32 bits of each source as signed,
      multiply in `ℤ`, truncate to 32 bits via `to_bits_truncate`, then
      sign-extend to 64. Mirrors `execute_MULW` in `InstsEnd.lean`. -/
  def execute_MULW_pure_val (op1 op2 : BitVec 64) : BitVec 64 :=
    let rs1_bits : BitVec 32 := Sail.BitVec.extractLsb op1 31 0
    let rs2_bits : BitVec 32 := Sail.BitVec.extractLsb op2 31 0
    let result32 : BitVec 32 :=
      to_bits_truncate (l := 32) ((BitVec.toInt rs1_bits) * (BitVec.toInt rs2_bits))
    sign_extend (m := 64) result32

  def execute_MULW_pure (input : MulwInput) : MulwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        execute_MULW_pure_val input.r1_val input.r2_val
      )
    : MulwOutput
  }

  /-- **MULW Sail-equivalence (Phase 3A M3).**

      An RV64 MULW `.MULW (r2, r1, rd)` threaded through the standard
      `writeReg nextPC (PC+4); execute …` prelude reduces to the pure-spec
      block that (a) writes `nextPC = PC + 4`, (b) writes the sign-extended
      32-bit product to `rd` (or no-ops when `rd = 0`), (c) retires.

      Same shape as the ADD proof, with `execute_MULW` unfolded directly
      (no `execute_MULW'` helper exists in `Fundamentals/Execution.lean`,
      and that file is read-only in Phase 3A). The extra `extractLsb` /
      `sign_extend` plumbing passes through `simp`. -/
  lemma execute_MULW_pure_equiv
    (mulw_input : MulwInput)
    (r1 r2 rd: regidx)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mulw_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mulw_input.r2_val) state)
    (h_input_rd: mulw_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some mulw_input.PC)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.MULW (r2, r1, rd))
    ) state =
    let mulw_output := execute_MULW_pure mulw_input
    (do
      Sail.writeReg Register.nextPC mulw_output.nextPC
      match mulw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    -- Unfold PC write + `execute_MULW` directly (no helper exists for MULW).
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_MULW
    ]

    -- Register reads: rewrite `rX_bits` to `read_xreg`, then commute through
    -- the `nextPC` write.
    rewrite [rX_read_xreg_equiv _ r1 (regidx_to_fin r1) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r1 reg_of_fin_neq_nextPC]
    simp
    rewrite [rX_read_xreg_equiv _ r2 (regidx_to_fin r2) (by simp [regidx_to_fin])]
    rewrite [read_xreg_write_other_reg_state _ h_input_r2 reg_of_fin_neq_nextPC]
    simp [
      execute_MULW_pure,
      execute_MULW_pure_val
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
