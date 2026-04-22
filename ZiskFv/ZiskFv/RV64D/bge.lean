import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure BgeInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BgeOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BGE_pure (input : BgeInput) : BgeOutput :=
    let skip := !(input.r1_val.toInt ≥b input.r2_val.toInt)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BgeOutput
    }

  /-- Trusted axiom: RV64 BGE Sail-equivalence (Phase 3A B2, sibling of
      C1's D4b-patch pattern).

      Under the standard register-state hypotheses, the Sail
      `execute_BTYPE (imm, r2, r1, bop.BGE)` threaded through the usual
      `writeReg nextPC (PC+4); execute …` prelude reduces to the
      pure-spec `execute_BGE_pure` evaluation.

      **Trust basis.** The Sail `execute_BTYPE` BGE arm evaluates
      `zopz0zKzJ_s (rX rs1) (rX rs2) = (rX rs1).toInt ≥b (rX rs2).toInt`,
      structurally identical to the `.toInt ≥b .toInt` in
      `execute_BGE_pure`. Direct closure route follows BNE's pattern
      (case split on signed ≥, taken branch uses `jump_to_equiv`) but
      is axiomatized here in lockstep with `execute_BLT_pure_equiv_axiom`
      — see `docs/fv/trusted-base.md` entry C2 for the shared closure
      path (both eliminate via a `BitVec.toInt`-aware case-split
      lemma and the BNE's `simp`+`jump_to_equiv` skeleton). -/
  axiom execute_BGE_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {misa_val : RegisterType Register.misa}
    (bge_input : BgeInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bge_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bge_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bge_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BGE ))
    ) state =
    let bge_output := execute_BGE_pure bge_input
    (do
      Sail.writeReg Register.nextPC bge_output.nextPC
      if bge_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bge_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bge_input.PC + BitVec.signExtend 64 bge_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state

  lemma execute_BGE_pure_equiv
    (bge_input : BgeInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bge_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bge_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bge_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BGE ))
    ) state =
    let bge_output := execute_BGE_pure bge_input
    (do
      Sail.writeReg Register.nextPC bge_output.nextPC
      if bge_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bge_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bge_input.PC + BitVec.signExtend 64 bge_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := execute_BGE_pure_equiv_axiom bge_input imm r1 r2
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c

end PureSpec
