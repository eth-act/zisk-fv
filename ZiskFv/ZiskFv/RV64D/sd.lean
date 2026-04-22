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

  -- SD Sail-equivalence: `execute_STORE imm rs2 rs1 8` reduces to the
  -- pure-spec block (write `nextPC = PC+4`; apply 8 byte-writes to
  -- `state.mem` at successive addresses starting at `rs1 + sign_extend imm`;
  -- retire success).
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
  := by
    -- BLOCKER (Phase 2.5 D1 investigation, 2026-04-22, symmetric to
    -- `ld.lean`). The Phase 2 A4 diagnosis ("8-iteration `untilFuelM`
    -- byte loop in `vmem_write_addr`") turned out to have the right
    -- address but the wrong floor — for aligned access,
    -- `split_misaligned` returns `(n, bytes) = (1, 8)`, so the write
    -- loop runs ONCE, not eight times. The real blocker is an
    -- architectural gap between RV32 and RV64 platform configs
    -- (see `ld.lean` companion comment for the full diagnosis):
    --
    --   * `sys_pmp_count = 16` vs 0: `pmpCheck` unfolds to a
    --     16-iteration loop `simp` cannot reduce without
    --     `pmpcfg_n`/`pmpaddr_n` state assumptions (absent from
    --     `RISC_V_assumptions`).
    --   * `plat_clint_base/_size` nonzero: `within_clint` can be `true`
    --     for addresses in `[2^25, 2^25+786432)`, taking the
    --     `mmio_write` branch that bypasses the `state.mem.insert`
    --     chain `modify_memory_8` encodes.
    --
    -- The write case adds the additional complication that
    -- `vmem_write_addr`'s `mem_write_ea` is a *separate* precommit
    -- hook before the actual `mem_write_value` ram write — both reduce
    -- to `pure ()` / `write_ram` in the non-MMIO branch but need to
    -- stay synchronized. The `sw.lean` port surfaces four consecutive
    -- `if_pos` / `if_neg` rewrites (vs LD's two); each would need a
    -- platform-config-aware resolution.
    --
    -- Real closure requires the same infrastructure `ld.lean` outlines
    -- (either extend `RISC_V_assumptions` with PMP/CLINT hypotheses and
    -- prove reduction lemmas, or axiomatize
    -- `vmem_write_addr_aligned_equiv` in `Fundamentals/Transpiler.lean`).
    -- Both paths exceed D1's 2-day wall-clock budget given the
    -- discovery cost.
    -- Status tracked in `ai_plans/zisk-fv-phase-2.md` (Phase 2.5 D1).
    sorry

end PureSpec
