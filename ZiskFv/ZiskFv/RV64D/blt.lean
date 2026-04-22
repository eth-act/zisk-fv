import ZiskFv.RV64D.Auxiliaries

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

  /-- Trusted axiom: RV64 BLT Sail-equivalence (Phase 3A B1, sibling of
      C1's D4b-patch pattern).

      Under the standard register-state hypotheses (imm alignment, r1/r2
      readable, PC readable, misa readable with `misa[C] = 0`), the Sail
      `execute_BTYPE (imm, r2, r1, bop.BLT)` threaded through the usual
      `writeReg nextPC (PC+4); execute …` prelude reduces to the pure-spec
      `execute_BLT_pure` evaluation.

      **Trust basis.** BLT differs from BEQ/BNE only in the `taken`
      predicate: the Sail `execute_BTYPE` BLT arm evaluates
      `zopz0zI_s (rX rs1) (rX rs2)` which unfolds to
      `(rX rs1).toInt <b (rX rs2).toInt` — structurally identical to the
      `.toInt <b .toInt` comparison in `execute_BLT_pure`'s `skip` field.
      The circuit-level theorem (`Spec.BranchLessThan`) and metaplan
      theorem (`Equivalence.BranchLessThan`) close directly from this
      axiom; the axiom itself exists because the RV64 direct-closure
      route via `simp`/`by_cases`/`jump_to_equiv` did not fit within the
      Phase 3A heartbeat budget — the signed-comparison case split
      introduces `BitVec.toInt` unfoldings that `simp` does not close
      without additional lemma plumbing. A future direct proof (estimated
      80-120 lines, paralleling the BNE proof with `h_eq` replaced by
      `h_lt : r1_val.toInt < r2_val.toInt`) would eliminate this axiom;
      see `docs/fv/trusted-base.md` entry C2.
  -/
  axiom execute_BLT_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {misa_val : RegisterType Register.misa}
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

  -- BLT Sail-equivalence: the `do` block consisting of a default
  -- `nextPC ← PC + 4` write followed by `execute (.BTYPE imm r2 r1 BLT)`
  -- equals the pure-spec block (signed less-than comparison; on taken,
  -- jump to PC+imm with throws/fails on misaligned target; on not-taken,
  -- fall through to PC+4). Closed via `execute_BLT_pure_equiv_axiom`
  -- (Phase 3A B1). See the axiom's docstring for the audit trail.
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
  := execute_BLT_pure_equiv_axiom blt_input imm r1 r2
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c

end PureSpec
