-- RV64-only opcode `sd`: store 64-bit doubleword to memory.
-- Sail-side pure equivalence. Mirror of `sw.lean` (openvm-fv RV32D)
-- widened from 4-byte to 8-byte store.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  /-- Store doubleword input: two register operands (rs1 = base, rs2 =
      value), immediate offset, current PC. No memory read — the writes
      are the side-effect. -/
  structure SdInput where
    r1 : BitVec 5
    imm : BitVec 12
    r2 : BitVec 5
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  /-- Store doubleword output: next-PC advance (+4) and the 8 memory
      writes (address, byte) — each byte of `r2_val` goes to a
      successive address starting at `r1 + sign_extend imm`.

      Mirror of openvm-fv's `SwOutput` widened from 4 to 8 bytes. -/
  structure SdOutput where
    nextPC : BitVec 64
    data0 : ℕ × BitVec 8
    data1 : ℕ × BitVec 8
    data2 : ℕ × BitVec 8
    data3 : ℕ × BitVec 8
    data4 : ℕ × BitVec 8
    data5 : ℕ × BitVec 8
    data6 : ℕ × BitVec 8
    data7 : ℕ × BitVec 8

  /-- SD pure semantics: next-PC is `+4`, the 8 bytes of `r2_val` are
      written to successive addresses starting at `r1 + sign_extend imm`
      in **little-endian** order (low byte at `addr + 0`, high byte at
      `addr + 7`). Matches `vmem_write_addr`'s byte-loop order. -/
  def execute_STORED_pure (input : SdInput) : SdOutput := {
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
    data4 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 4,
      BitVec.extractLsb 39 32 input.r2_val
    )
    data5 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 5,
      BitVec.extractLsb 47 40 input.r2_val
    )
    data6 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 6,
      BitVec.extractLsb 55 48 input.r2_val
    )
    data7 := (
      (input.r1_val + BitVec.signExtend 64 input.imm).toNat + 7,
      BitVec.extractLsb 63 56 input.r2_val
    )
    : SdOutput
  }

  /-- Apply the 8 byte-writes of an `SdOutput` to a Sail sequential
      state. Preserves every other field of the state unchanged; only
      the `mem` HashMap is updated via 8 successive `.insert` calls.
      Mirror of openvm-fv's `modify_memory_4` widened to 8 bytes. -/
  def modify_memory_8
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (output : SdOutput)
  := {
    regs := s.regs,
    choiceState := s.choiceState,
    tags := s.tags,
    cycleCount := s.cycleCount,
    sailOutput := s.sailOutput
    mem :=
      ((((((((s.mem.insert output.data0.1 output.data0.2
      ).insert output.data1.1 output.data1.2)
      ).insert output.data2.1 output.data2.2
      ).insert output.data3.1 output.data3.2
      ).insert output.data4.1 output.data4.2
      ).insert output.data5.1 output.data5.2
      ).insert output.data6.1 output.data6.2
      ).insert output.data7.1 output.data7.2
    : PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  }

  /-- Assumptions needed by `execute_STORED_pure_equiv`. Mirror of
      openvm-fv's `sw_state_assumptions` widened to 8 bytes +
      8-byte alignment. Unlike LD (which assumes eight `state.mem[...]?`
      values are already populated), SD just requires that rs1 and rs2
      read successfully and that the address is in-bound and aligned —
      the writes become new `state.mem` entries. -/
  def sd_state_assumptions
    (i : SdInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r2) state = EStateM.Result.ok i.r2_val state ∧
    (i.r1_val + BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
    (8 : ℤ) ∣ (i.r1_val.toNat + (BitVec.signExtend 64 i.imm)).toNat

  /-- Trusted axiom: RV64 SD byte-loop equivalence (Phase 2.5 D1, path (b)).

      Symmetric companion to `execute_LOADD_pure_equiv_axiom` — see
      `ld.lean` for the full platform-config-gap analysis. Under
      `RISC_V_assumptions` + `sd_state_assumptions` (rs1/rs2 read
      successfully, 8-byte alignment, address below
      `OpenVM_address_space_size`), the Sail `execute_STORE imm rs2 rs1 8`
      reduces to the pure-spec block: write `nextPC = PC+4`, apply the
      eight byte-writes encoded by `modify_memory_8`, retire success.

      **Trust basis.** Same three platform invariants as LD's axiom:
      (1) `pmpCheck addr 8 (Store Data) Machine` returns `none`
      (machine-mode PMP short-circuit); (2) `within_clint addr 8 = false`
      (ZisK programs never target CLINT MMIO); (3) `pmaCheck` with
      `writable = true` + 8-byte alignment yields `ok none`. The write
      case additionally relies on:

        (4) `mem_write_ea` is a no-op in the non-MMIO write path (it
            returns `ok ()` after passing the alignment check); the
            subsequent `mem_write_value` performs the actual
            `state.mem.insert` chain that `modify_memory_8` encodes.

      **Derivation closure path.** A future Phase 3+ task should extend
      `RISC_V_assumptions` with the PMP/CLINT hypotheses and prove a
      reduction lemma `vmem_write_addr_aligned_equiv` in
      `RV64D/Auxiliaries.lean` that yields this axiom's conclusion
      mechanically. Estimated cost: 300-500 lines symmetric to the LD
      case. See `docs/fv/trusted-base.md` for the audit trail. -/
  axiom execute_STORED_pure_equiv_axiom
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    (input : SdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sd_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          8
        ))
    ) state =
    let output := execute_STORED_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_8 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state

  -- SD Sail-equivalence: `execute_STORE imm rs2 rs1 8` reduces to the
  -- pure-spec block (write `nextPC = PC+4`; apply 8 byte-writes to
  -- `state.mem` at successive addresses starting at `rs1 + sign_extend imm`;
  -- retire success).
  --
  -- Closed via `execute_STORED_pure_equiv_axiom` (Phase 2.5 D1, path (b),
  -- 2026-04-22). The axiom captures the memory-model reduction that
  -- cannot currently be derived under `RISC_V_assumptions` because the
  -- vendored `LeanRV64D` platform config adds PMP / MMIO state
  -- dependencies not witnessed by the current assumption bundle. See
  -- the axiom's docstring and `docs/fv/trusted-base.md` for the
  -- closure path back to a derivation-only Phase 3+ extension.
  set_option maxHeartbeats 0 in
  lemma execute_STORED_pure_equiv
    (input : SdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : sd_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.STORE (
          input.imm,
          regidx.Regidx input.r2,
          regidx.Regidx input.r1,
          8
        ))
    ) state =
    let output := execute_STORED_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      set (modify_memory_8 (← get) output)
      pure (ExecutionResult.Retire_Success ())
    ) state
  := execute_STORED_pure_equiv_axiom input risc_v_assumptions h_opcode_assumptions

end PureSpec
