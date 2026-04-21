import ZiskFv.RV64D.Auxiliaries

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
  := sorry

end PureSpec
