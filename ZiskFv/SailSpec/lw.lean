import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  structure LwInput where
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
    data2 : BitVec 8
    data3 : BitVec 8

  structure LwOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADW_pure (input : LwInput) : LwOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        BitVec.signExtend 64 (input.data3 ++ input.data2 ++ input.data1 ++ input.data0)
      )
    : LwOutput
  }

  def lw_state_assumptions
    (i : LwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 3]? = .some i.data3 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < ZiskPhysicalAddressSpaceSize ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat + 4 ≤ ZiskPhysicalAddressSpaceSize ∧
    (4 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADW_pure_equiv
    (input : LwInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lw_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          false,
          4
        ))
    ) state =
    let output := execute_LOADW_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    unfold lw_state_assumptions at h_opcode_assumptions

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
      (width := 4)
      (acc := ())
      h_pma_regions h_pma_base h_pma_size h_pma_readable h_pma_misaligned
      (by simp [BitVec.toNat_add, this.2.2]; omega)
      (by simp [BitVec.toNat_add, this.2.2]; omega)

    simp [LeanRV64D.Functions.execute_LOAD, LeanRV64D.Functions.vmem_read, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_read_addr, ExceptT.run, *]

    simp [write_reg_state, execute_LOADW_pure, *]

    split_ifs with h_rd
    . simp [LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.wX, *]
    . let r : Finset.Icc 1 31 := ⟨input.rd.toNat, range input.rd h_rd⟩
      rewrite [ wX_write_xreg_non_zero_equiv _ _ _ r (by simp [r])]
      grind

end PureSpec
