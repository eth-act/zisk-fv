-- RV64-only opcode `ld`: load 64-bit doubleword from memory.
-- Sail-side pure equivalence. Mirror of `lw.lean` widened to 8 bytes.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  /-- Load doubleword input: register operands, PC, and the 8 memory bytes
      at `rs1_val + signExtend imm`. -/
  structure LdInput where
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    r1_val : BitVec 64
    PC : BitVec 64
    -- 8 memory bytes for the doubleword
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8
    data4 : BitVec 8
    data5 : BitVec 8
    data6 : BitVec 8
    data7 : BitVec 8

  /-- Load doubleword output: next-PC advance (+4) and the register-write
      payload (rd index + loaded value). Matches `lw.lean`'s shape. -/
  structure LdOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31
  := by
    apply Finset.mem_Icc.mpr
    obtain ⟨x: Fin 32⟩ := bv
    fin_cases x <;> simp_all

  /-- LD pure semantics: next-PC is `+4`, rd is `.none` if `rd = 0` else
      the destination pair; the loaded value is the 8 bytes concatenated
      in little-endian order (`data7 ++ ... ++ data0`). -/
  def execute_LOADD_pure (input : LdInput) : LdOutput := {
    nextPC := input.PC + 4#64
    rd := if h: input.rd = 0
      then .none
      else .some (
        ⟨
          input.rd.toNat,
          range input.rd h
        ⟩,
        input.data7 ++ input.data6 ++ input.data5 ++ input.data4
          ++ input.data3 ++ input.data2 ++ input.data1 ++ input.data0
      )
    : LdOutput
  }

  /-- Assumptions needed by `execute_LOADD_pure_equiv`. Mirror of
      `lw_state_assumptions` widened to 8 bytes + 8-byte alignment.

      The `8 ∣ (rs1 + imm)` alignment witness steers `vmem_read_addr`'s
      `is_aligned_vaddr` check into the Ok branch under ZisK's RV64IM
      profile (no compressed ext; misaligned accesses fault). -/
  def ld_state_assumptions
    (i : LdInput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
  : Prop :=
    state.regs.get? Register.PC = .some i.PC ∧
    LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state = EStateM.Result.ok i.r1_val state ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]? = .some i.data0 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 1]? = .some i.data1 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 2]? = .some i.data2 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 3]? = .some i.data3 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 4]? = .some i.data4 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 5]? = .some i.data5 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 6]? = .some i.data6 ∧
    state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 7]? = .some i.data7 ∧
    i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
    (8 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

  -- LD Sail-equivalence: `execute_LOAD imm rs1 rd false 8` reduces to
  -- the pure-spec block (write `nextPC = PC+4`; if `rd ≠ 0` write
  -- little-endian concatenation of `data7..data0` to `rd`; retire
  -- success).
  --
  -- Proof strategy mirrors `RV64D/lw.lean` widened from 4-byte to 8-byte
  -- load. The `arithmetic_helper` lemma in `Auxiliaries.lean` already
  -- accounts for the 8-byte width (third conjunct, `mod 2^64`).
  set_option maxHeartbeats 0 in
  lemma execute_LOADD_pure_equiv
    (input : LdInput)
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : ld_state_assumptions input state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.LOAD (
          input.imm,
          regidx.Regidx input.r1,
          regidx.Regidx input.rd,
          false,
          8
        ))
    ) state =
    let output := execute_LOADD_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())
    ) state
  := by
    -- BLOCKER (Phase 2 A3 budget): Sail's `execute_LOAD` at width = 8
    -- reduces through the 8-iteration `untilFuelM` byte loop in
    -- `vmem_read_addr` (sail-riscv-lean/LeanRV64D/VmemUtils.lean:251).
    -- openvm-fv's `RV32D/lw.lean` proves the 4-byte version by a
    -- ~15-line simp-chain against `vmem_read_addr`'s body. Porting
    -- that chain to width = 8 surfaces two issues:
    --   (1) The 8-byte alignment witness `8 ∣ (r1_val + imm)` fails
    --       `omega` at the `if is_aligned_vaddr` branch — `omega` can't
    --       reason modularly about the div-by-8 residue without an
    --       explicit `Nat.mod_eq_zero_of_dvd` rewrite;
    --   (2) The `rw [if_pos ...]` doesn't fire because the 8-iteration
    --       loop produces a nested `match`-tree without a top-level
    --       `if`, requiring a different tactical decomposition
    --       (per-iteration simp + `forIn_succ` unfolding).
    -- Both are tractable Phase 3 sweep work — estimated 1-2 days per
    -- load-family opcode (LD/LWU/LHU/LBU). The circuit-side archetype
    -- stack is complete and consumes this lemma parametrically.
    -- Status tracked in `ai_plans/zisk-fv-phase-2.md` (A3 CLOSED).
    sorry

end PureSpec
