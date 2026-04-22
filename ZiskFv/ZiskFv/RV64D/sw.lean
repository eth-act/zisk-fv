-- RV64 opcode `sw`: store 32-bit word (lower 4 bytes of rs2) to memory.
-- Sail-side pure equivalence. Mirror of `sd.lean` narrowed from 8-byte
-- to 4-byte store (Phase 2.5 D4d).
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

  /-- Trusted axiom: RV64 SW byte-loop equivalence (Phase 2.5 D4d, path (b)).

      Narrow companion to `execute_STORED_pure_equiv_axiom` — see
      `sd.lean` for the full platform-config-gap analysis. Under
      `RISC_V_assumptions` + `sw_state_assumptions` (rs1/rs2 read
      successfully, 4-byte alignment, address below
      `OpenVM_address_space_size`), the Sail `execute_STORE imm rs2 rs1 4`
      reduces to the pure-spec block: write `nextPC = PC+4`, apply the
      four byte-writes encoded by `modify_memory_4`, retire success.

      **Trust basis.** Same three platform invariants as SD's axiom:
      (1) `pmpCheck addr 4 (Store Data) Machine` returns `none`
      (machine-mode PMP short-circuit); (2) `within_clint addr 4 = false`
      (ZisK programs never target CLINT MMIO); (3) `pmaCheck` with
      `writable = true` + 4-byte alignment yields `ok none`. The write
      case additionally relies on:

        (4) `mem_write_ea` is a no-op in the non-MMIO write path (it
            returns `ok ()` after passing the alignment check); the
            subsequent `mem_write_value` performs the actual
            `state.mem.insert` chain that `modify_memory_4` encodes.

      Unlike RV32 (where openvm-fv's `sw.lean` discharges this without
      an axiom), the vendored `LeanRV64D` platform config
      (`sys_pmp_count = 16`, `plat_clint_base = 2^25`,
      `plat_clint_size = 786432`) adds PMP / MMIO state dependencies not
      witnessed by the current assumption bundle — the same blocker
      documented in SD. The 4-byte case is strictly narrower than SD's
      8-byte case; the symmetric derivation closure path via
      `vmem_write_addr_aligned_equiv` would retire both together. -/
  axiom execute_STOREW_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
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

  -- SW Sail-equivalence: `execute_STORE imm rs2 rs1 4` reduces to the
  -- pure-spec block (write `nextPC = PC+4`; apply 4 byte-writes to
  -- `state.mem` at successive addresses starting at `rs1 + sign_extend imm`;
  -- retire success).
  --
  -- Closed via `execute_STOREW_pure_equiv_axiom` (Phase 2.5 D4d, path (b),
  -- 2026-04-22). Same memory-model-reduction blocker as LD/SD/LWU — see
  -- the axiom's docstring and `sd.lean` for the platform-config-gap
  -- analysis. The 4-byte case is the RV64 twin of openvm-fv's RV32
  -- `execute_STOREW_pure_equiv`, which closed without an axiom; the
  -- derivation-only closure path for both RV64 variants is symmetric.
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
  := execute_STOREW_pure_equiv_axiom input risc_v_assumptions h_opcode_assumptions

end PureSpec
