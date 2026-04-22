import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
RV64 SLLIW (shift-left-immediate-word). Phase 3A H2b sibling of SLLW.

Takes the low 32 bits of `rs1`, shifts left by a 5-bit immediate `shamt`,
sign-extends the 32-bit result back to 64 bits. No PC jump; write to
`rd`; advance PC by 4.

The pure spec mirrors LeanRV64D's `execute_SHIFTIWOP` for `sopw.SLLIW`
(`InstsEnd.lean:65520-65528`): the 32-bit result is
`Sail.shift_bits_left rs1_val shamt` and gets sign-extended to 64 via
`sign_extend (m := 64)`. Unlike the register-variant SLLW, the shift
amount is a 5-bit immediate (not read from a register), so there is no
`r2` read step in the proof.

Trusted-axiom policy: since `Fundamentals/Execution.lean` does not yet
define an `execute_SHIFTIWOP_pure` + `execute_SHIFTIWOP'` refactor pair
(analogous to `execute_RTYPEW_pure` / `execute_RTYPEW'`), we axiomatize
the Sail-side equivalence per the D4b-patch pattern. The axiom
catalogues as **C3a** in `docs/fv/trusted-base.md`. Closure path: add
`execute_SHIFTIWOP_pure` + `_eq_` lemma to `Fundamentals/Execution.lean`
(mechanical port of the `execute_RTYPEW_pure` / `_eq_` pair with
signature `shamt : BitVec 5`, opcode `sopw` instead of `ropw`), then
drop the axiom.
-/

namespace PureSpec

  structure SlliwInput where
    -- operands
    r1_val : BitVec 64
    shamt : BitVec 5
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure SlliwOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure SLLIW: extract low 32 bits of r1, shift left by 5-bit immediate
      `shamt`, sign-extend 32-bit result to 64. PC advances by 4. -/
  def execute_SHIFTIWOP_slliw_pure (input : SlliwInput) : SlliwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.val,
          by apply Finset.mem_Icc.mpr; omega
        ⟩,
        LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_left
            (Sail.BitVec.extractLsb input.r1_val 31 0) input.shamt)
      )
    : SlliwOutput
  }

  /-- **SLLIW Sail-equivalence (trusted — C3a).**

      An RV64 SLLIW `.SHIFTIWOP (shamt, r1, rd, sopw.SLLIW)` reduces to
      the pure-spec block that (a) writes `nextPC = PC + 4`, (b) writes
      the 32-bit-shift-then-sign-extend result to `rd` (or no-ops when
      `rd = 0`), (c) retires.

      Axiomatized because `Fundamentals/Execution.lean` does not yet
      define an `execute_SHIFTIWOP_pure` / `execute_SHIFTIWOP'` /
      `execute_SHIFTIWOP_eq_execute_SHIFTIWOP'` refactor triple that
      would permit the `sllw.lean`-style direct closure via `simp
      [execute_RTYPEW']`. Catalogued as **C3a** in
      `docs/fv/trusted-base.md`.

      **Closure path.** Add the refactor triple to
      `Fundamentals/Execution.lean` (mechanical port of the existing
      `execute_RTYPEW_pure` / `execute_RTYPEW'` /
      `execute_RTYPEW_eq_execute_RTYPEW'` pattern to the 5-bit
      immediate shamt signature), then replace this axiom body with the
      proof shape from `sllw.lean::execute_RTYPE_sllw_pure_equiv`
      stripped of the `r2` register-read step. -/
  axiom execute_SHIFTIWOP_slliw_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (slliw_input : SlliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slliw_input.r1_val state)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slliw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state =
    let slliw_output := execute_SHIFTIWOP_slliw_pure slliw_input
    (do
      Sail.writeReg Register.nextPC slliw_output.nextPC
      match slliw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state

  /-- **SLLIW Sail-equivalence.** Closed via
      `execute_SHIFTIWOP_slliw_pure_equiv_axiom`. -/
  lemma execute_SHIFTIWOP_slliw_pure_equiv
    (slliw_input : SlliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slliw_input.r1_val state)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slliw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state =
    let slliw_output := execute_SHIFTIWOP_slliw_pure slliw_input
    (do
      Sail.writeReg Register.nextPC slliw_output.nextPC
      match slliw_output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state :=
    execute_SHIFTIWOP_slliw_pure_equiv_axiom slliw_input r1 rd
      h_input_r1 h_input_rd h_input_pc

end PureSpec
