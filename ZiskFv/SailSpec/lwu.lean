-- RV64-only opcode `lwu`: load 32-bit word from memory, zero-extended into rd.
-- Sail-side pure equivalence. Mirror of `ld.lean` narrowed to 4 bytes with
-- `is_unsigned = true` (zero-extend the loaded 32-bit word to 64 bits).
import ZiskFv.SailSpec.Auxiliaries

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

  -- LWU Sail-equivalence: `execute_LOAD imm rs1 rd true 4` reduces to the
  -- pure-spec block (write `nextPC = PC+4`; if `rd ≠ 0` write the 4 bytes
  -- concatenated in little-endian and zero-extended to 64 bits to `rd`;
  -- retire success).
  --
  -- Direct port of openvm-fv's RV32 LW proof, with the `@[simp high]`
  -- platform axioms in `ZiskFv.PlatformScope` discharging the 16-entry
  -- PMP loop / CLINT MMIO check / PMA alignment chain that RV32 closed
  -- for free (where `sys_pmp_count = 0`). Width = 4, `is_unsigned = true`.
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
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    unfold lwu_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg, _, _, _ ⟩ := next_gma
    have := arithmetic_helper (a := input.r1_val.toNat) (b := (BitVec.signExtend 64 input.imm).toNat) (by grind)

    simp [LeanRV64D.Functions.execute_LOAD, LeanRV64D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_read_addr, ExceptT.run, *]

    simp [write_reg_state, execute_LOADWU_pure, *]

    split_ifs with h_rd
    . simp [LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.wX, *]
    . let r : Finset.Icc 1 31 := ⟨input.rd.toNat, range input.rd h_rd⟩
      rewrite [ wX_write_xreg_non_zero_equiv _ _ _ r (by simp [r])]
      grind

end PureSpec
