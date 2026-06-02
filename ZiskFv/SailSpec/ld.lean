-- RV64-only opcode `ld`: load 64-bit doubleword from memory.
-- Sail-side pure equivalence. Mirror of `lw.lean` widened to 8 bytes.
import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  /-- Load doubleword input: register operands, PC, and the 8 memory bytes
      at `rs1_val + signExtend imm`. -/
  structure LdInput where
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    r1_val : BitVec 64
    PC : BitVec 64
    -- 8 memory bytes for the doubleword
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8
    data4 : BitVec 8
    data5 : BitVec 8
    data6 : BitVec 8
    data7 : BitVec 8

  /-- Load doubleword output: next-PC advance (+4) and the register-write
      payload (rd index + loaded value). Matches `lw.lean`'s shape. -/
  structure LdOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  /-- LD pure semantics: next-PC is `+4`, rd is `.none` if `rd = 0` else
      the destination pair; the loaded value is the 8 bytes concatenated
      in little-endian order (`data7 ++ ... ++ data0`). -/
  def execute_LOADD_pure (input : LdInput) : LdOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        input.data7 ++ input.data6 ++ input.data5 ++ input.data4
          ++ input.data3 ++ input.data2 ++ input.data1 ++ input.data0
      )
    : LdOutput
  }

  /-- Assumptions needed by `execute_LOADD_pure_equiv`. Mirror of
      `lw_state_assumptions` widened to 8 bytes + 8-byte alignment.

      The `8 ∣ (rs1 + imm)` alignment witness steers `vmem_read_addr`'s
      `is_aligned_vaddr` check into the Ok branch under ZisK's RV64IM
      profile (no compressed ext; misaligned accesses fault). -/
  def ld_state_assumptions
    (i : LdInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 3]? = .some i.data3 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 4]? = .some i.data4 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 5]? = .some i.data5 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 6]? = .some i.data6 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 7]? = .some i.data7 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < ZiskPhysicalAddressSpaceSize ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat + 8 ≤ ZiskPhysicalAddressSpaceSize ∧
    (8 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

  -- LD Sail-equivalence: `execute_LOAD imm rs1 rd false 8` reduces to
  -- the pure-spec block (write `nextPC = PC+4`; if `rd ≠ 0` write
  -- little-endian concatenation of `data7..data0` to `rd`; retire
  -- success).
  --
  -- Direct port of the LWU proof widened to 8 bytes. The platform-profile
  -- lemmas in `ZiskFv.PlatformScope` discharge the PMP/CLINT/PMA chain.
  set_option maxHeartbeats 0 in
  lemma execute_LOADD_pure_equiv
    (input : LdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : ld_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          false,
          8
        ))
    ) state =
    let output := execute_LOADD_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    unfold ld_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma
    have := arithmetic_helper (a := input.r1_val.toNat) (b := (BitVec.signExtend 64 input.imm).toNat) (by grind)
    have h_pma := ZiskFv.PlatformScope.pmaCheck_load_is_none
      (state := write_reg_state state Register.nextPC (input.PC + 4#64))
      (pmaRegion := pmaRegion)
      (addr := input.r1_val + BitVec.signExtend 64 input.imm)
      (width := 8)
      (acc := ())
      h_pma_regions h_pma_base h_pma_size h_pma_readable h_pma_misaligned
      (by simp [BitVec.toNat_add, this.2.2]; omega)
      (by simp [BitVec.toNat_add, this.2.2]; omega)

    simp [LeanRV64D.Functions.execute_LOAD, LeanRV64D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_read_addr, ExceptT.run, *]

    simp [write_reg_state, execute_LOADD_pure, *]

    split_ifs with h_rd
    . simp [LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.wX, *]
    . let r : Finset.Icc 1 31 := ⟨input.rd.toNat, range input.rd h_rd⟩
      rewrite [ wX_write_xreg_non_zero_equiv _ _ _ r (by simp [r])]
      grind

end PureSpec
