import ZiskFv.SailSpec.Auxiliaries

namespace PureSpec

  structure JalrInput where
    -- operands
    imm : BitVec 12
    rs1_val: BitVec 64
    rd: Fin 32
    -- registers
    PC : BitVec 64

  structure JalrOutput where
    -- registers
    nextPC : Option (BitVec 64)
    rd : Option (Finset.Icc 1 31 × BitVec 64)
    -- result
    success : Bool

  def execute_JALR_pure (input : JalrInput) : JalrOutput :=
    let bit1_valid := (BitVec.ofBool (input.rs1_val + BitVec.signExtend 64 input.imm)[1]! == 0#1)
    let mask := 0xFFFFFFFFFFFFFFFE
    {
      nextPC :=
        if (!bit1_valid)
        then (.some (input.PC + 4))
        else (.some (mask &&& (input.rs1_val + BitVec.signExtend 64 input.imm)))
      rd := if h: (!bit1_valid) || input.rd = 0
      then .none
      else (
        .some (⟨input.rd, by {
          simp at h
          apply Finset.mem_Icc.mpr
          omega
        }⟩, input.PC + 4))
      success := (bit1_valid)
    }

  -- JALR Sail-equivalence. Direct port of the `execute_JAL_pure_equiv`
  -- proof shape, adapted for JALR's pre-masked target
  -- (`BitVec.update target 0 0#1` clears bit 0, so the
  -- bit-0-Assertion branch never fires). The `@[simp high]` platform
  -- axiom `ZiskFv.PlatformScope.update_elp_state_is_pure_unit` collapses
  -- the Zicfilp guard that RV64 otherwise consults.
  set_option maxHeartbeats 0 in
  lemma execute_JALR_pure_equiv
    (input : JalrInput)
    (imm: BitVec 12)
    (rs1 rd: regidx)
    (h_input_imm: input.imm = imm)
    (h_input_rd: input.rd = regidx_to_fin rd)
    (h_input_rs1: read_xreg (regidx_to_fin rs1) state = EStateM.Result.ok (input.rs1_val) state)
    (h_input_pc: state.regs.get? Register.PC = .some input.PC)
    (h_input_misa: state.regs.get? Register.misa = .some misa)
    (h_misa_c: Sail.BitVec.extractLsb misa 2 2 = 0#1)
    (_h_cur_privilege : Sail.readReg Register.cur_privilege state = EStateM.Result.ok Privilege.Machine state)
    (_h_mseccfg : Sail.readReg Register.mseccfg state = EStateM.Result.ok mseccfg state)
  :
    (
      do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))
    ) state =
    let output := execute_JALR_pure input
    (do
      match output.nextPC with
        | .some nextPC => Sail.writeReg Register.nextPC nextPC
        | .none => pure ()
      match output.rd with
        | .some (reg, rd_val) => write_xreg reg rd_val
        | .none => pure ()
      if !output.success then
        pure (
          ExecutionResult.Memory_Exception (
            (virtaddr.Virtaddr (0xFFFFFFFFFFFFFFFE &&& (input.rs1_val + BitVec.signExtend 64 input.imm))),
            (ExceptionType.E_Fetch_Addr_Align ())
          )
        )
      else
        (pure (ExecutionResult.Retire_Success ()))) state
  := by
    -- Step 1: unfold execute + execute_JALR. P4 collapses update_elp_state.
    -- get_next_pc reads nextPC which we just set to PC+4.
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      LeanRV64D.Functions.execute_JALR,
      LeanRV64D.Functions.get_next_pc,
      readReg_succ (writeReg_read_same _),
    ]
    -- Step 2: read rs1_val from the mutated state.
    obtain ⟨⟨rs1_fin: Fin 32⟩⟩ := rs1
    rewrite [rX_read_xreg_equiv _ ⟨⟨rs1_fin⟩⟩ rs1_fin (by simp)]
    simp [regidx_to_fin] at h_input_rs1
    rewrite [read_xreg_write_other_reg_state (register := Register.nextPC)
      (write_val := input.PC + 4#64) rs1_fin h_input_rs1 reg_of_fin_neq_nextPC]
    simp
    -- Step 3: reduce `jump_to (BitVec.update (rs1_val + signExtend imm) 0 0#1)`
    -- via jump_to_equiv on the mutated state.
    have h_misa_post :
      (write_reg_state state Register.nextPC (input.PC + 4#64)).regs.get? Register.misa
        = .some misa :=
      writeReg_read_diff h_input_misa (by decide)
    rewrite [jump_to_equiv
      (state := (write_reg_state state Register.nextPC (input.PC + 4#64)))
      (misa_val := misa)
      (target := Sail.BitVec.update (input.rs1_val + BitVec.signExtend 64 imm) 0 0#1)
      h_misa_post
      h_misa_c]
    -- Step 4: bit 0 of `Sail.BitVec.update x 0 0#1` is always 0, so the
    -- bit-0 Assertion branch never fires.
    have h_bit0 : BitVec.ofBool
        (Sail.BitVec.update (input.rs1_val + BitVec.signExtend 64 imm) 0 0#1)[0] = 0#1 := by
      simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
    rw [if_neg (by grind)]
    -- Step 5: case-split on bit 1 of the masked target.
    -- `(Sail.BitVec.update x 0 0#1)[1] = x[1]` (mask preserves bit 1).
    have h_bit1_preserved :
      BitVec.ofBool (Sail.BitVec.update (input.rs1_val + BitVec.signExtend 64 imm) 0 0#1)[1] =
      BitVec.ofBool (input.rs1_val + BitVec.signExtend 64 imm)[1] := by
      simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
    rw [h_bit1_preserved]
    by_cases h_bit1 : BitVec.ofBool (input.rs1_val + BitVec.signExtend 64 imm)[1] = 1#1
    . -- Misaligned: Memory_Exception. Pure-spec: success = false.
      simp [h_bit1, execute_JALR_pure, h_input_imm]
      -- The virtaddr in Sail is `Sail.BitVec.update (...) 0 0#1`; pure-spec writes
      -- `0xFFFFFFFFFFFFFFFE &&& (...)`. These are equal.
      simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
    . -- Aligned: Retire_Success, write nextPC := masked target, optional
      -- link-address write to rd.
      have h_bit1_zero : BitVec.ofBool (input.rs1_val + BitVec.signExtend 64 imm)[1] = 0#1 := by
        grind
      simp [h_bit1_zero, execute_JALR_pure, h_input_imm]
      -- Bridge the write_reg_state nextPC with the masked target.
      have h_mask_eq :
        Sail.BitVec.update (input.rs1_val + BitVec.signExtend 64 imm) 0 0#1 =
        18446744073709551614#64 &&& (input.rs1_val + BitVec.signExtend 64 imm) := by
        simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']
      rw [h_mask_eq]
      -- Step 6: case-split on whether rd = 0.
      by_cases h_rd_0 : input.rd = 0 <;> simp [h_rd_0]
      . replace h_rd_0 : rd.1.toNat = 0 := by
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

end PureSpec
