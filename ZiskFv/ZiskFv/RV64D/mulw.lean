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
`execute_MULW_pure_equiv` is axiomatized per the Phase 3A C3-style
precedent: there is no `execute_MULW'` refactor triple in
`Fundamentals/Execution.lean` (and that file is read-only in Phase 3A),
so the Sail-side equivalence is trusted pending a future
`execute_MULW_pure`/`'`/`_eq_` refactor. See `docs/fv/trusted-base.md`
entry C4.
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
      LeanRV64D.Functions.to_bits_truncate (l := 32)
        ((BitVec.toInt rs1_bits) * (BitVec.toInt rs2_bits))
    LeanRV64D.Functions.sign_extend (m := 64) result32

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

  /-- Trusted axiom: RV64 MULW Sail-equivalence (Phase 3A M3, C4).

      Under the standard register-state hypotheses, the Sail
      `execute_instruction (.MULW (r2, r1, rd))` threaded through the
      `writeReg nextPC (PC+4); execute …` prelude reduces to the
      `execute_MULW_pure` block.

      **Trust basis.** `Fundamentals/Execution.lean` has
      `execute_RTYPEW_pure` / `execute_RTYPEW'` / `execute_RTYPEW_eq_…`
      for SLLW/SRLW/SRAW, but no analogous triple for MULW. The
      Phase 3A invariants forbid mutating `Fundamentals/Execution.lean`,
      so MULW's Sail equivalence is axiomatized pointwise pending a
      future refactor that would discharge this via a direct closure. -/
  axiom execute_MULW_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (mulw_input : MulwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mulw_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mulw_input.r2_val) state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC) :
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

  lemma execute_MULW_pure_equiv
    (mulw_input : MulwInput)
    (r1 r2 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (mulw_input.r1_val) state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (mulw_input.r2_val) state)
    (h_input_rd : mulw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some mulw_input.PC) :
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
  := execute_MULW_pure_equiv_axiom mulw_input r1 r2 rd
      h_input_r1 h_input_r2 h_input_rd h_input_pc

end PureSpec
