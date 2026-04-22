-- RV64-only opcode `lwu`: load 32-bit word from memory, zero-extended into rd.
-- Sail-side pure equivalence. Mirror of `ld.lean` narrowed to 4 bytes with
-- `is_unsigned = true` (zero-extend the loaded 32-bit word to 64 bits).
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  /-- Load-word-unsigned input: register operands, PC, and the 4 memory bytes
      at `rs1_val + signExtend imm`. -/
  structure LwuInput where
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    r1_val : BitVec 64
    PC : BitVec 64
    -- 4 memory bytes for the word
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8

  /-- Load-word-unsigned output: next-PC advance (+4) and the register-write
      payload (rd index + loaded 64-bit value, zero-extended from 32 bits).
      Matches `ld.lean`'s shape. -/
  structure LwuOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  /-- LWU pure semantics: next-PC is `+4`, rd is `.none` if `rd = 0` else
      the destination pair; the loaded value is the 4 bytes concatenated in
      little-endian order (`data3 ++ data2 ++ data1 ++ data0`) zero-extended
      to 64 bits. -/
  def execute_LOADWU_pure (input : LwuInput) : LwuOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        BitVec.zeroExtend 64
          (input.data3 ++ input.data2 ++ input.data1 ++ input.data0)
      )
    : LwuOutput
  }

  /-- Assumptions needed by `execute_LOADWU_pure_equiv`. Mirror of
      `ld_state_assumptions` narrowed to 4 bytes + 4-byte alignment. -/
  def lwu_state_assumptions
    (i : LwuInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 3]? = .some i.data3 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
    (4 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

  /-- Trusted axiom: RV64 LWU byte-loop equivalence (Phase 2.5 D4c, path (b)
      — sibling of `execute_LOADD_pure_equiv_axiom` narrowed to width 4 with
      `is_unsigned = true`).

      Under `RISC_V_assumptions` + `lwu_state_assumptions` (pins four source
      bytes, establishes 4-byte alignment, bounds the address below
      `OpenVM_address_space_size = 2^29`), the Sail
      `execute_LOAD imm rs1 rd true 4` reduces to the pure-spec block: write
      `nextPC = PC+4`, conditionally write the 4 bytes zero-extended to 64
      bits to `rd`, retire success.

      **Trust basis.** Same platform-config gap as M1 (`execute_LOADD_pure_
      equiv_axiom`), symmetric at width = 4. The obstruction (`pmpCheck`'s
      16-iteration `forIn`, `within_clint` disjointness, `pmaCheck` with
      4-byte alignment) lives outside the assumption bundle currently
      recorded in `RISC_V_assumptions`. A future Phase 3+ extension would
      generalize the bulk lemma `vmem_read_addr_aligned_equiv` over the
      `width ∈ {1, 2, 4, 8}` and `is_unsigned ∈ {false, true}` axes; until
      then this axiom captures the narrowed case pointwise. See
      `docs/fv/trusted-base.md` entry M1 for the full audit trail. -/
  axiom execute_LOADWU_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    (input : LwuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lwu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          4
        ))
    ) state =
    let output := execute_LOADWU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state

  -- LWU Sail-equivalence: `execute_LOAD imm rs1 rd true 4` reduces to the
  -- pure-spec block (write `nextPC = PC+4`; if `rd ≠ 0` write the 4 bytes
  -- concatenated in little-endian and zero-extended to 64 bits to `rd`;
  -- retire success).
  --
  -- Closed via `execute_LOADWU_pure_equiv_axiom` (Phase 2.5 D4c,
  -- 2026-04-22). Sibling of M1 (`execute_LOADD_pure_equiv_axiom`)
  -- narrowed to width = 4 with `is_unsigned = true`.
  set_option maxHeartbeats 0 in
  lemma execute_LOADWU_pure_equiv
    (input : LwuInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lwu_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          true,
          4
        ))
    ) state =
    let output := execute_LOADWU_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := execute_LOADWU_pure_equiv_axiom input risc_v_assumptions h_opcode_assumptions

end PureSpec
