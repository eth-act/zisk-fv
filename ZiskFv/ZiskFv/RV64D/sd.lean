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
  --
  -- Proof strategy mirrors `RV32D/sw.lean` widened from 4-byte to 8-byte
  -- store. Encounters the same A3-class blocker (8-iteration `untilFuelM`
  -- byte loop in `vmem_write_addr`, symmetric to `vmem_read_addr`).
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
    -- BLOCKER (Phase 2 A4 budget, symmetric to A3's `ld.lean:131` sorry).
    -- Sail's `execute_STORE` at width = 8 reduces through the 8-iteration
    -- `untilFuelM` byte loop in `vmem_write_addr`
    -- (sail-riscv-lean/LeanRV64D/VmemUtils.lean:309). openvm-fv's
    -- `RV32D/sw.lean` proves the 4-byte version by a ~25-line simp-chain
    -- against `vmem_write_addr`'s body. Porting that chain to width = 8
    -- encounters the same two issues the LD case did:
    --   (1) The 8-byte alignment witness `8 ∣ (r1_val + imm)` fails
    --       `omega` at the `if is_aligned_vaddr` branch without an
    --       explicit `Nat.mod_eq_zero_of_dvd` rewrite;
    --   (2) The byte-loop produces a nested `match`-tree without a
    --       top-level `if`; `rw [if_pos ...]` doesn't fire.
    --
    -- RECOMMENDATION (carried forward from A3). A shared Phase 3 sweep
    -- task should produce both:
    --   * `vmem_read_aligned_equiv` (bypasses the 8-iteration read loop
    --     given `RISC_V_assumptions + 8-byte alignment`, closing A3's
    --     `ld.lean:131` sorry);
    --   * `vmem_write_aligned_equiv` (bypasses the 8-iteration write
    --     loop under the same hypotheses, closing this sorry).
    --
    -- Placing both bulk lemmas in `RV64D/Auxiliaries.lean` closes the
    -- entire RV64 8-byte memory-op family (LD + SD) in one sweep plus
    -- the per-opcode consumer lines. Estimated 1-2 days; the A4
    -- ambitious-mode attempt deferred this to a dedicated session.
    -- Status tracked in `ai_plans/zisk-fv-phase-2.md` (A4 CLOSED).
    sorry

end PureSpec
