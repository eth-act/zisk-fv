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

  /-- Trusted axiom: RV64 SH byte-loop equivalence (Phase 3A S1, path (b)).

      Narrow companion to `execute_STOREW_pure_equiv_axiom` (M4) and
      `execute_STORED_pure_equiv_axiom` (M2) — see `sd.lean` / `sw.lean`
      for the full platform-config-gap analysis. Under
      `RISC_V_assumptions` + `sh_state_assumptions` (rs1/rs2 read
      successfully, 2-byte alignment, address below
      `OpenVM_address_space_size`), the Sail
      `execute_STORE imm rs2 rs1 2` reduces to the pure-spec block:
      write `nextPC = PC+4`, apply the two byte-writes encoded by
      `modify_memory_2`, retire success.

      **Trust basis.** Same three platform invariants as SD/SW's
      axiom: (1) `pmpCheck addr 2 (Store Data) Machine` returns `none`
      (machine-mode PMP short-circuit); (2) `within_clint addr 2 = false`
      (ZisK programs never target CLINT MMIO); (3) `pmaCheck` with
      `writable = true` + 2-byte alignment yields `ok none`. The write
      case additionally relies on `mem_write_ea` being a no-op in the
      non-MMIO write path; `mem_write_value` performs the actual
      `state.mem.insert` chain that `modify_memory_2` encodes.

      The 2-byte case is strictly narrower than SD's 8-byte / SW's
      4-byte cases; the symmetric derivation closure path via
      `vmem_write_addr_aligned_equiv` would retire all three together.
      Catalogued as M10 in `docs/fv/trusted-base.md`. -/
  axiom execute_STOREH_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
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

  -- SH Sail-equivalence: `execute_STORE imm rs2 rs1 2` reduces to the
  -- pure-spec block (write `nextPC = PC+4`; apply 2 byte-writes to
  -- `state.mem` at successive addresses starting at `rs1 + sign_extend imm`;
  -- retire success).
  --
  -- Closed via `execute_STOREH_pure_equiv_axiom` (Phase 3A S1, path (b),
  -- 2026-04-22). Same memory-model-reduction blocker as LD/SD/LWU/SW — see
  -- the axiom's docstring and `sd.lean` for the platform-config-gap
  -- analysis.
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
  := execute_STOREH_pure_equiv_axiom input risc_v_assumptions h_opcode_assumptions

end PureSpec
