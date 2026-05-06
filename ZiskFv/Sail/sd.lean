-- RV64-only opcode `sd`: store 64-bit doubleword to memory.
-- Sail-side pure equivalence. Mirror of `sw.lean` (openvm-fv RV32D)
-- widened from 4-byte to 8-byte store.
import ZiskFv.Sail.Auxiliaries

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
  -- Direct port of openvm-fv's RV32 SW proof, widened to 8 bytes. The
  -- `@[simp high]` platform axioms in `ZiskFv.PlatformScope` discharge
  -- the PMP/CLINT/PMA chain.
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
    have next_gma := RISC_V_assumptions_invariant_under_pc_increment risc_v_assumptions (val := input.PC + 4#64)
    unfold sd_state_assumptions at h_opcode_assumptions

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
    rw [if_pos (by omega)]
    -- Layered structural normalization (replaces a `simp [*]` here that
    -- peaked at ~42 GiB on a 32 GiB CI runner — see commit message).
    --
    -- The original `simp [*]` had to traverse the entire untilFuelM body
    -- inline, building Eq.trans proof-term chains for every rewrite as it
    -- went. The 33 GiB blowup came from this monolithic pass.
    --
    -- Strategy:
    --   (1) `dsimp only` over the monadic-bind primitives — pure
    --       definitional unfolding, no proof-term construction.
    --   (2) `unfold untilFuelM.go` to expose the 1-iteration loop body.
    --   (3) Peel one readReg/CSR layer at a time with `rw [hyp]; try dsimp`.
    --       Each step is O(1) memory; the .ok-constructor match resolves
    --       definitionally without simp's caching overhead.
    --   (4) Once enough layers are peeled, the residual goal is small
    --       enough that the closing `simp [*]` runs at low cost.
    --
    -- Final peak: ~9 GiB (vs 42 GiB before) — fits comfortably in CI.
    dsimp only [bind, EStateM.bind, EStateM.pure, pure, EStateM.modifyGet, modify, modifyGet,
                PreSail.PreSailM, ExceptT.bind, ExceptT.pure, ExceptT.run, ExceptT.mk]
    unfold untilFuelM.go
    dsimp only [Int.toNat, bind, EStateM.bind, EStateM.pure, pure, ExceptT.bind, ExceptT.pure,
                ExceptT.run, ExceptT.mk]
    rw [h_mprv.1]; try dsimp only [bind, EStateM.bind, ExceptT.bind, EStateM.pure, ExceptT.pure, pure]
    rw [h_priv];   try dsimp only [bind, EStateM.bind, ExceptT.bind, EStateM.pure, ExceptT.pure, pure]
    rw [h_mprv.2]; try dsimp only [bind, EStateM.bind, ExceptT.bind, EStateM.pure, ExceptT.pure, pure]
    simp only [show ¬ ((0#1 : BitVec 1) = (1#1 : BitVec 1)) from by decide,
               and_false, if_false]
    try dsimp only [bind, EStateM.bind, ExceptT.bind, EStateM.pure, ExceptT.pure, pure]
    simp [*]

    simp [execute_STORED_pure, EStateM.set, modify_memory_8,
          BitVec.extractLsb, BitVec.extractLsb']

end PureSpec
