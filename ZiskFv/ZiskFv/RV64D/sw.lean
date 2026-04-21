import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SwInput where
    -- operands
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    -- registers
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure SwOutput where
    -- registers
    nextPC : BitVec 64
    -- memory
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8
    data2 : ℕ × BitVec 8
    data3 : ℕ × BitVec 8

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_STOREW_pure (input : SwInput) : SwOutput := {
    nextPC := input.PC + 4#64
    data0 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat,
      BitVec.extractLsb 7 0 input.r2_val
    )
    data1 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 1,
      BitVec.extractLsb 15 8 input.r2_val
    )
    data2 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 2,
      BitVec.extractLsb 23 16 input.r2_val
    )
    data3 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 3,
      BitVec.extractLsb 31 24 input.r2_val
    )
    : SwOutput
  }

  def modify_memory_4
    (s: PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (output: SwOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((((s.mem.insert output.data0.1 output.data0.2
      ).insert output.data1.1 output.data1.2)
      ).insert output.data2.1 output.data2.2
      ).insert output.data3.1 output.data3.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  def sw_state_assumptions
    (i : SwInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
    (4 : ℤ) ∣ (i.r1_val.toNat + (BitVec.signExtend 64 i.imm)).toNat

  set_option maxHeartbeats 0 in
  lemma execute_STOREW_pure_equiv
    (input : SwInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sw_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          4
        ))
    ) state =
    let output := execute_STOREW_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_4 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
