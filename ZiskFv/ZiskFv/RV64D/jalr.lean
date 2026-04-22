import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure JalrInput where
    -- operands
    imm : BitVec 12
    rs1_val: BitVec 64
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure JalrOutput where
    -- registers
    nextPC : Option (BitVec 64)
    rd : Option (Finset.Icc 1 31 × BitVec 64)
    -- result
    success : Bool

  def execute_JALR_pure (input : JalrInput) : JalrOutput :=
    let bit1_valid := (BitVec.ofBool (input.rs1_val + BitVec.signExtend 64 input.imm)[1]! == 0#1)
    let mask := 0xFFFFFFFE
    {
      nextPC :=
        if (!bit1_valid)
        then (.some (input.PC + 4))
        else (.some (mask &&& (input.rs1_val + BitVec.signExtend 64 input.imm)))
      rd := if h: (!bit1_valid) || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := (bit1_valid)
    }

  /-- Trusted axiom: RV64 JALR Sail-equivalence (Phase 2.5 D4b-patch, path (b)).

      Under the standard register-state hypotheses (imm/rd/rs1 alignment,
      PC readable, misa readable, machine privilege, mseccfg readable),
      the Sail `execute_JALR imm rs1 rd` threaded through the usual
      `writeReg nextPC (PC+4); execute …` prelude reduces to the pure-spec
      block: (a) on bit-1 misalignment of the masked target, raise
      `E_Fetch_Addr_Align` without updating nextPC or rd; (b) otherwise
      write `nextPC := 0xFFFFFFFE &&& (rs1 + signExtend imm)`, write the
      link address `PC+4` to rd (if rd ≠ 0), retire success.

      **Trust basis.** Unlike JAL (whose RV64 proof closes via
      `jump_to_equiv` + a misa[C]=0 hypothesis), JALR additionally invokes
      `update_elp_state rs1` before the jump. In RV64D that helper
      consults `currentlyEnabled Ext_Zicfilp`, which in turn depends on
      `currentlyEnabled Ext_Zicsr` and `get_xLPE cur_privilege`
      (readReg mseccfg → `_get_Seccfg_MLPE`). The RV32 companion
      (`OpenvmFv/RV32D/jalr.lean::execute_JALR_pure_equiv`) closes this
      directly because its `hartSupports Ext_Zicsr` simp-chain reduces
      cleanly. The RV64 chain introduces additional CSR register-read
      dependencies (menvcfg / senvcfg probes inside the `get_xLPE` User
      branch) that `RISC_V_assumptions` does not currently witness — the
      same class of platform-config gap documented for LD/SD/LWU/SW in
      `docs/fv/trusted-base.md`, but on the control-flow side rather than
      the memory-model side. A future extension to `RISC_V_assumptions`
      with an `mseccfg.MLPE = 0` (or equivalently `Ext_Zicfilp` disabled)
      witness would convert this axiom to a theorem by the same direct
      route as the RV32 proof. -/
  axiom execute_JALR_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    (input : JalrInput)
    (imm: BitVec 12)
    (rs1 rd: regidx)
    (h_input_imm: input.imm = imm)
    (h_input_rd: input.rd = regidx_to_fin rd)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))
    ) state =
    let output := execute_JALR_pure input
    (do
      match output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if !output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (0xFFFFFFFE &&& (input.rs1_val + BitVec.signExtend 64 input.imm))),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state

  -- JALR Sail-equivalence: the `do` block consisting of a default
  -- `nextPC ← PC + 4` write followed by `execute (.JALR (imm, rs1, rd))`
  -- equals the pure-spec block (masked target; bit-1 misalignment → Memory_Exception;
  -- otherwise link address `PC+4` to rd unless rd = 0; retire success).
  --
  -- Closed via `execute_JALR_pure_equiv_axiom` (Phase 2.5 D4b-patch,
  -- path (b)). Sibling of `execute_JAL_pure_equiv` but takes the axiom
  -- route because RV64's `update_elp_state` introduces CSR-read
  -- dependencies not witnessed by `RISC_V_assumptions`. See the axiom's
  -- docstring and `docs/fv/trusted-base.md` for the audit trail.
  set_option maxHeartbeats 0 in
  lemma execute_JALR_pure_equiv
    (input : JalrInput)
    (imm: BitVec 12)
    (rs1 rd: regidx)
    (h_input_imm: input.imm = imm)
    (h_input_rd: input.rd = regidx_to_fin rd)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))
    ) state =
    let output := execute_JALR_pure input
    (do
      match output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if !output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (0xFFFFFFFE &&& (input.rs1_val + BitVec.signExtend 64 input.imm))),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := execute_JALR_pure_equiv_axiom input imm rs1 rd
      h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa
      h_cur_privilege h_mseccfg

end PureSpec
