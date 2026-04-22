import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure LbuInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    -- registers
    r1_val : BitVec 64
    PC : BitVec 64
    -- memory
    data0 : BitVec 8

  structure LbuOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADBU_pure (input : LbuInput) : LbuOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        (BitVec.setWidth 32 (input.data0))
      )
    : LbuOutput
  }

  def lbu_state_assumptions
    (i : LbuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size

  /-- Trusted axiom: RV64 LBU byte-loop equivalence (Phase 3A L5, path (b)
      — sibling of `execute_LOADWU_pure_equiv_axiom` / `execute_LOADHU_
      pure_equiv_axiom` narrowed to width 1 with `is_unsigned = true`).

      Under `RISC_V_assumptions` + `lbu_state_assumptions` (pins one source
      byte, bounds the address below `OpenVM_address_space_size = 2^29`;
      1-byte "alignment" is trivial), the Sail
      `execute_LOAD imm rs1 rd true 1` reduces to the pure-spec block:
      write `nextPC = PC+4`, conditionally write the byte zero-extended
      into `rd`, retire success.

      **Trust basis.** Same platform-config gap as M1 (LOADD) /
      M3 (LOADWU) / M7 (LOADHU), now at width = 1. The 1-byte case is the
      simplest — alignment is vacuous — but the PMP/CLINT/PMA chain is
      identical. Future closure via `vmem_read_addr_aligned_equiv`
      generalization subsumes all widths uniformly. See
      `docs/fv/trusted-base.md` entry M9 for the audit trail. -/
  axiom execute_LOADBU_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    (input : LbuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lbu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          1
        ))
    ) state =
    let output := execute_LOADBU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state

  -- LBU Sail-equivalence. Closed via `execute_LOADBU_pure_equiv_axiom`
  -- (Phase 3A L5, 2026-04-22). Sibling of M3 (LWU) / M7 (LHU) narrowed to
  -- width = 1.
  set_option maxHeartbeats 0 in
  lemma execute_LOADBU_pure_equiv
    (input : LbuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lbu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          1
        ))
    ) state =
    let output := execute_LOADBU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := execute_LOADBU_pure_equiv_axiom input risc_v_assumptions h_opcode_assumptions

end PureSpec
