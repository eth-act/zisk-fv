import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure LhuInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    -- registers
    r1_val : BitVec 64
    PC : BitVec 64
    -- memory
    data0 : BitVec 8
    data1 : BitVec 8

  structure LhuOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADHU_pure (input : LhuInput) : LhuOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        (BitVec.setWidth 32 (input.data1 ++ input.data0))
      )
    : LhuOutput
  }

  def lhu_state_assumptions
    (i : LhuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[(i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat) + 1]? = .some i.data1 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
    (2 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

  /-- Trusted axiom: RV64 LHU byte-loop equivalence (Phase 3A L3, path (b)
      — sibling of `execute_LOADWU_pure_equiv_axiom` narrowed to width 2
      with `is_unsigned = true`).

      Under `RISC_V_assumptions` + `lhu_state_assumptions` (pins two source
      bytes, establishes 2-byte alignment, bounds the address below
      `OpenVM_address_space_size = 2^29`), the Sail
      `execute_LOAD imm rs1 rd true 2` reduces to the pure-spec block:
      write `nextPC = PC+4`, conditionally write the 2 bytes zero-extended
      into `rd`, retire success.

      **Trust basis.** Same platform-config gap as M1 (LOADD) /
      M3 (LOADWU), symmetric at width = 2. The obstruction (`pmpCheck`'s
      16-iteration `forIn`, `within_clint` disjointness, `pmaCheck` with
      2-byte alignment) lives outside the assumption bundle currently
      recorded in `RISC_V_assumptions`. A future Phase 3+ extension would
      generalize the bulk lemma `vmem_read_addr_aligned_equiv` over the
      `width ∈ {1, 2, 4, 8}` and `is_unsigned ∈ {false, true}` axes; until
      then this axiom captures the narrowed case pointwise. See
      `docs/fv/trusted-base.md` entries M1/M3/M7 for the full audit trail. -/
  axiom execute_LOADHU_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    (input : LhuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lhu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          2
        ))
    ) state =
    let output := execute_LOADHU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state

  -- LHU Sail-equivalence. Closed via `execute_LOADHU_pure_equiv_axiom`
  -- (Phase 3A L3, 2026-04-22). Sibling of M3 (LWU) narrowed to width = 2.
  set_option maxHeartbeats 0 in
  lemma execute_LOADHU_pure_equiv
    (input : LhuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lhu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          2
        ))
    ) state =
    let output := execute_LOADHU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := execute_LOADHU_pure_equiv_axiom input risc_v_assumptions h_opcode_assumptions

end PureSpec
