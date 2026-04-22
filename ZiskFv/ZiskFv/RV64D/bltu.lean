import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure BltuInput where
    -- operands
    imm : BitVec 13
    r1_val: BitVec 64
    r2_val: BitVec 64
    -- registers
    PC : BitVec 64

  structure BltuOutput where
    -- registers
    nextPC : BitVec 64
    -- result
    success : Bool
    throws : Bool

  def execute_BLTU_pure (input : BltuInput) : BltuOutput :=
    let skip := !(input.r1_val.toNat <b input.r2_val.toNat)
    let throws := !skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0] == 1#1
    let fails := throws || (!skip && BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1] == 1#1)
    {
      nextPC := if skip || fails
        then (input.PC + 4)
        else (input.PC + BitVec.signExtend 64 input.imm)
      success := !fails
      throws := throws
      : BltuOutput
    }

  /-- Trusted axiom: RV64 BLTU Sail-equivalence (Phase 3A B3, sibling of
      C1's D4b-patch pattern).

      Under the standard register-state hypotheses, the Sail
      `execute_BTYPE (imm, r2, r1, bop.BLTU)` threaded through the usual
      prelude reduces to the pure-spec `execute_BLTU_pure` evaluation.

      **Trust basis.** The Sail `execute_BTYPE` BLTU arm evaluates
      `zopz0zI_u (rX rs1) (rX rs2) = (rX rs1).toNatInt <b (rX rs2).toNatInt`,
      which after unfolding `Sail.BitVec.toNatInt = Int.ofNat ∘ BitVec.toNat`
      equals the `.toNat <b .toNat` comparison in `execute_BLTU_pure`'s
      `skip` field up to an `Int.ofNat` coercion. Direct closure (BEQ
      shape with `h_lt : r1_val.toNat < r2_val.toNat` case-split plus a
      `Int.ofNat_lt` bridge lemma) is tractable but axiomatized here
      alongside BLT — see `docs/fv/trusted-base.md` entry C2 for the
      shared closure path. -/
  axiom execute_BLTU_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {misa_val : RegisterType Register.misa}
    (bltu_input : BltuInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bltu_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bltu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bltu_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BLTU ))
    ) state =
    let bltu_output := execute_BLTU_pure bltu_input
    (do
      Sail.writeReg Register.nextPC bltu_output.nextPC
      if bltu_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bltu_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state

  lemma execute_BLTU_pure_equiv
    (bltu_input : BltuInput)
    (imm: BitVec 13)
    (r1 r2 : regidx)
    (h_input_imm: bltu_input.imm = imm)
    (h_input_r1: read_xreg (regidx_to_fin r1) state = EStateM.Result.ok (bltu_input.r1_val) state)
    (h_input_r2: read_xreg (regidx_to_fin r2) state = EStateM.Result.ok (bltu_input.r2_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.BTYPE (imm, r2, r1, bop.BLTU ))
    ) state =
    let bltu_output := execute_BLTU_pure bltu_input
    (do
      Sail.writeReg Register.nextPC bltu_output.nextPC
      if bltu_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !bltu_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := execute_BLTU_pure_equiv_axiom bltu_input imm r1 r2
      h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c

end PureSpec
