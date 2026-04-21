import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure LhInput where
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

  structure LhOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  def execute_LOADH_pure (input : LhInput) : LhOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        (BitVec.signExtend 64 (input.data1 ++ input.data0))
      )
    : LhOutput
  }

  def lh_state_assumptions
    (i : LhInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[(i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat) + 1]? = .some i.data1 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
    (2 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

  set_option maxHeartbeats 0 in
  lemma execute_LOADH_pure_equiv
    (input : LhInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lh_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          false,
          2
        ))
    ) state =
    let output := execute_LOADH_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := sorry

end PureSpec
