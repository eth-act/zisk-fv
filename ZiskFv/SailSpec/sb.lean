import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  structure SbInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure SbOutput where
    -- registers
    nextPC : BitVec 64
    -- memory
    data0 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREB_pure (input : SbInput) : SbOutput := {
    nextPC := input.PC + 4#64
    data0 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    : SbOutput
  }

  def modify_memory_1
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_output: SbOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      s.mem.insert sb_output.data0.1 sb_output.data0.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sb_state_assumptions
    (i : SbInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + (BitVec.signExtend 64 i.imm)).toNat < ZiskPhysicalAddressSpaceSize ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat + 1 ≤ ZiskPhysicalAddressSpaceSize

  -- SB Sail-equivalence. Direct port of SH narrowed to width = 1
  -- (alignment vacuous). The platform-profile lemmas discharge the
  -- PMP/CLINT/PMA chain.
  set_option maxHeartbeats 0 in
  lemma execute_STOREB_pure_equiv
    (input : SbInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sb_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          1
        ))
    ) state =
    let output := execute_STOREB_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_1 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    unfold sb_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC
    have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_opcode_assumptions.2.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg ⟩ := next_gma

    simp at h_opcode_assumptions
    have h_pma := ZiskFv.PlatformScope.pmaCheck_store_is_none
      (state := write_reg_state state Register.nextPC (input.PC + 4#64))
      (pmaRegion := pmaRegion)
      (addr := input.r1_val + BitVec.signExtend 64 input.imm)
      (width := 1)
      (acc := LeanRV64D.Functions.default_write_acc)
      h_pma_regions h_pma_base h_pma_size h_pma_writable h_pma_misaligned
      (by simp [BitVec.toNat_add]; omega)
      (by simp [BitVec.toNat_add])
    simp [LeanRV64D.Functions.execute_STORE, LeanRV64D.Functions.vmem_write, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_write_addr, ExceptT.run, *]

    simp [execute_STOREB_pure, EStateM.set, modify_memory_1,
          BitVec.extractLsb, BitVec.extractLsb', *]
    have h_eq0 : BitVec.ofNat 8 (input.r2_val.toNat % 256) =
                 BitVec.setWidth 8 input.r2_val := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [h_eq0]

end PureSpec
