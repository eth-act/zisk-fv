import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure JalInput where
    -- operands
    imm : BitVec 21
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure JalOutput where
    -- registers
    nextPC : Option (BitVec 64)
    rd : Option (Finset.Icc 1 31 × BitVec 64)
    -- result
    success : Bool
    throws : Bool

  def execute_JAL_pure (input : JalInput) : JalOutput :=
    let bit0_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[0]! == 0#1)
    let bit1_valid := (BitVec.ofBool (input.PC + BitVec.signExtend 64 input.imm)[1]! == 0#1)
    {
      nextPC :=
        if !bit0_valid || !bit1_valid
        then (.some (input.PC + 4))
        else (.some (input.PC + BitVec.signExtend 64 input.imm))
      rd := if h: !bit0_valid || !bit1_valid || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := bit0_valid && bit1_valid
      throws := !bit0_valid
    }

  /-- Dispatcher-unfold: `execute (.JAL …)` reduces to `execute_JAL`.
      Mirrors `RV32D/jal.lean`'s `rv32d_execute_jal` lemma. -/
  lemma rv64d_execute_jal :
    LeanRV64D.Functions.execute (instruction.JAL (imm, rd)) state =
    LeanRV64D.Functions.execute_JAL imm rd state
  := by
    simp [LeanRV64D.Functions.execute]

  /- JAL Sail-equivalence: the `do` block consisting of a default
      `nextPC ← PC + 4` write followed by `execute (.JAL (imm, rd))`
      equals the pure-spec block that (a) writes the taken `nextPC`
      (either `PC + imm` or `PC + 4` on misalignment), (b) writes the
      link address `PC + 4` to rd (when not zero and no misalignment),
      (c) raises `Assertion`/`Memory_Exception` on misaligned targets,
      and (d) retires otherwise.

      Closed via `jump_to_equiv` (the misa[C] = 0 hypothesis is threaded
      from `h_input_misa` + `h_misa_c`). The structure mirrors the RV32
      sibling `OpenvmFv/RV32D/jal.lean` one-for-one, with the
      RV32 → RV64 width adjustments (`signExtend 32 → signExtend 64`)
      and the additional misa-bit-2 hypothesis that RV64's `jump_to`
      consumes. -/
  set_option maxHeartbeats 0 in
  lemma execute_JAL_pure_equiv
    (jal_input : JalInput)
    (imm: BitVec 21)
    (rd: regidx)
    (h_input_imm: jal_input.imm = imm)
    (h_input_rd: jal_input.rd = regidx_to_fin rd)
    (h_input_pc: state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa_val)
    (h_misa_c: Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JAL (imm, rd))
    ) state =
    let jal_output := execute_JAL_pure jal_input
    (do
      match jal_output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match jal_output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if jal_output.throws then
        throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
      else if !jal_output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    -- Step 1: unfold the dispatcher + the `link_address ← get_next_pc ()` read
    -- (which reads `nextPC`, just set to `PC + 4` by `execute_instruction`).
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      rv64d_execute_jal,
      LeanRV64D.Functions.execute_JAL,
      LeanRV64D.Functions.get_next_pc,
      readReg_succ (writeReg_read_same _),
      readReg_succ (writeReg_read_diff h_input_pc (show Register.PC ≠ Register.nextPC by grind)),
    ]
    -- Step 2: reduce `jump_to target` via `jump_to_equiv`, threading the
    -- misa[C] = 0 witness through the `writeReg Register.nextPC` state.
    have h_misa_post :
      (write_reg_state state Register.nextPC (jal_input.PC + 4#64)).regs.get? Register.misa
        = .some misa_val :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (jal_input.PC + 4#64)))
      (misa_val := misa_val)
      (target := jal_input.PC + BitVec.signExtend 64 imm)
      h_misa_post
      h_misa_c]
    -- Step 3: case-split on bit 0 of the jump target (misalignment by 1).
    by_cases h_bit0 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 imm)[0] = 0#1
    . simp [h_bit0]
      -- Step 4: case-split on bit 1 (misalignment by 2).
      by_cases h_bit1 : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 imm)[1] = 1#1
      . simp [h_bit1]
        simp [
          execute_JAL_pure,
          h_input_imm,
          h_bit0,
          h_bit1
        ]
      . have h_bit1' : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 imm)[1] = 0#1 := by grind
        rw [if_neg (by grind)]
        simp [execute_JAL_pure]
        rw [if_neg (by grind)]
        simp
        rw [if_pos (by grind)]
        rw [if_neg (by grind)]
        simp [
          h_input_imm,
          h_bit0,
          h_bit1'
        ]
        -- Step 5: case-split on whether rd = 0 (no register write).
        by_cases h_rd_0 : jal_input.rd = 0 <;> simp [h_rd_0]
        . replace h_rd_0 : rd.1.toNat = 0
          := by
            simp [regidx_to_fin, h_rd_0] at h_input_rd
            rcases rd with ⟨ rd, h_rd ⟩
            simp_all
          simp [
            LeanRV64D.Functions.wX_bits,
            LeanRV64D.Functions.wX,
            h_rd_0
          ]
        . rcases rd with ⟨ rd, h_rd ⟩
          simp [regidx_to_fin] at h_input_rd
          simp [h_input_rd, Fin.ext_iff] at h_rd_0
          simp at h_rd
          simp [
            write_xreg,
            Sail.writeReg,
            PreSail.writeReg,
            LeanRV64D.Functions.wX_bits,
            LeanRV64D.Functions.wX,
            reg_of_fin
          ]
          interval_cases rd <;> simp
          . omega
          all_goals
            congr <;> simp_all
    . -- bit0 = 1 case: target is misaligned; Sail throws Assertion.
      have h_bit0' : BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 imm)[0] = 1#1 := by grind
      simp [h_bit0']
      simp [execute_JAL_pure, h_input_imm, h_bit0']

end PureSpec
