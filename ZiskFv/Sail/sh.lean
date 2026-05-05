import ZiskFv.Sail.Auxiliaries

namespace PureSpec

  structure ShInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure ShOutput where
    -- registers
    nextPC : BitVec 64
    -- memory
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREH_pure (input : ShInput) : ShOutput := {
    nextPC := input.PC + 4#64
    data0 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    data1 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 1,
      BitVec.extractLsb 15 8 input.r2_val
    )
    : ShOutput
  }

  def modify_memory_2
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (output: ShOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((s.mem.insert output.data0.1 output.data0.2
      ).insert output.data1.1 output.data1.2)
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sh_state_assumptions
    (i : ShInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + (BitVec.signExtend 64 i.imm)).toNat < OpenVM_address_space_size ∧
    (2 : ℤ) ∣ (i.r1_val + (BitVec.signExtend 64 i.imm)).toNat

  -- SH Sail-equivalence. Phase 3.5 promotion: direct port of SW narrowed
  -- to width = 2. The `@[simp high]` P1-P3 platform axioms discharge
  -- the PMP/CLINT/PMA chain.
  set_option maxHeartbeats 0 in
  lemma execute_STOREH_pure_equiv
    (input : ShInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sh_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          2
        ))
    ) state =
    let output := execute_STOREH_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_2 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    unfold sh_state_assumptions at h_opcode_assumptions

    simp [
      Sail.readReg,
      PreSail.readReg,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      *
    ]

    have h_r1_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_opcode_assumptions.2.1 reg_of_fin_neq_nextPC
    have h_r2_val := rX_bits_write_other_reg_state (val := input.PC + 4#64) h_opcode_assumptions.2.2.1 reg_of_fin_neq_nextPC

    obtain ⟨ h_priv, h_mprv, h_pma_regions, h_pma_base, h_pma_size, h_pma_readable, h_pma_writable, h_pma_misaligned, h_htif, h_misa, h_mseccfg, _, _, _ ⟩ := next_gma

    simp at h_opcode_assumptions
    simp [LeanRV64D.Functions.execute_STORE, LeanRV64D.Functions.vmem_write, EStateM.map, *]
    simp [LeanRV64D.Functions.vmem_write_addr, ExceptT.run, *]
    rw [if_pos (by omega)]; simp [*]

    simp [execute_STOREH_pure, EStateM.set, modify_memory_2,
          BitVec.extractLsb, BitVec.extractLsb', *]
    have h_eq0 : BitVec.ofNat 8 (input.r2_val.toNat % 65536) =
                 BitVec.setWidth 8 input.r2_val := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have h_eq1 : BitVec.ofNat 8 ((input.r2_val.toNat % 65536) >>> 8) =
                 BitVec.ofNat 8 (input.r2_val.toNat >>> 8) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
    rw [h_eq0, h_eq1]

end PureSpec
