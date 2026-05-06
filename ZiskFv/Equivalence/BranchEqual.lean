import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.BranchEqual
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.beq
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BEQ. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BEQ`),
* the compositional BEQ spec (`ZiskFv.Circuit.BranchEqual.branch_eq_compositional`),
* the Sail pure-function equivalence (`PureSpec.execute_BEQ_pure_equiv`),

into a canonical theorem:

* `equiv_BEQ_metaplan` — the metaplan target shape:
  `execute_instruction (.BTYPE (imm, r2, r1, BEQ)) state
    = (bus_effect exec_row mem_row state).2`.
-/

namespace ZiskFv.Equivalence.BranchEqual

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BEQ theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BEQ`, the
    next-pc cell advances by either `jmp_offset1` (taken) or
    `jmp_offset2` (not-taken), dispatched on `flag`:
    `next_pc = pc + jmp_offset2 + flag * (jmp_offset1 - jmp_offset2)`.

    This is the circuit-level companion to `equiv_BEQ_sail` below —
    together they form the analogue of `equiv_ADD` + `equiv_ADD_sail`
    from the ADD archetype. -/
theorem equiv_BEQ
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_eq_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_eq_compositional m r_main next_pc h_circuit

/-- **Closed-form circuit-level BEQ theorem.** Eliminates the
    `next_pc : FGL` parameter by deriving it from the extracted
    closed-form `pc_handshake` (Main constraint 20) via
    `pc_handshake_to_next_pc`. The caller supplies instead:

    * the booleans + disjointness for row `r_main`,
    * the BEQ mode witnesses at `r_main`,
    * the extracted handshake at `r_main + 1` (closed form — no
      `next_pc` quantifier),
    * the non-segment-boundary witness `segment_l1 (r_main + 1) = 0`.

    The next-row `pc` cell (`m.pc (r_main + 1)`) plays the role of
    `next_pc` in the conclusion. -/
theorem equiv_BEQ_closed
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (h_flag_bool : flag_boolean m r_main)
    (h_ext_bool : is_external_op_boolean m r_main)
    (h_disjoint : flag_set_pc_disjoint m r_main)
    (h_mode : main_row_in_beq_mode m r_main)
    (h_seg : m.segment_l1 (r_main + 1) = 0)
    (h_handshake_next : pc_handshake m (r_main + 1)) :
    m.pc (r_main + 1) = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_eq_compositional m r_main (m.pc (r_main + 1))
    ⟨⟨h_flag_bool, h_ext_bool, h_disjoint,
      pc_handshake_to_next_pc m r_main h_seg h_handshake_next⟩,
     h_mode⟩

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BEQ reduces to the pure-function block supplied by
    `PureSpec.execute_BEQ_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` (no compressed extension)
    witness.

    Wraps `PureSpec.execute_BEQ_pure_equiv` to expose the Sail chain at
    this module's export surface. -/
theorem equiv_BEQ_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = let beq_output := PureSpec.execute_BEQ_pure beq_input
        (do
          Sail.writeReg Register.nextPC beq_output.nextPC
          if beq_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !beq_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BEQ_pure_equiv beq_input imm h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 BEQ
    equals the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows. The memory-bus component is empty
    for BEQ (no register write, no memory access). -/
theorem equiv_BEQ_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC)
    (h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false)
    (h_success : (PureSpec.execute_BEQ_pure beq_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BEQ_sail state beq_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge the bus-side equation via the shape lemma.
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BEQ_pure beq_input).nextPC
    (PureSpec.execute_BEQ_pure beq_input).throws
    (PureSpec.execute_BEQ_pure beq_input).success
    beq_input.PC beq_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- **Bus-driven companion for BEQ.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. Other
    `h_input_*` stay — branch memory bus is empty, so rs1/rs2
    reads go via operation bus (not derivable from `h_bus` here). -/
theorem equiv_BEQ_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : beq_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    -- Structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC)
    (h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false)
    (h_success : (PureSpec.execute_BEQ_pure beq_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2
    := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some beq_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_BEQ_metaplan state beq_input imm r1 r2 misa_val exec_row h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- Constructor: build a `PureSpec.BeqInput` from exec_row PC + free operand values. -/
def BeqInput_of_bus
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 13)
    (r1_val r2_val : BitVec 64) :
    PureSpec.BeqInput :=
  { imm := imm
    r1_val := r1_val
    r2_val := r2_val
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for BEQ.** Bus-derived input form. -/
theorem equiv_BEQ_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (r1_val r2_val : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok (BeqInput_of_bus exec_row imm r1_val r2_val).r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok (BeqInput_of_bus exec_row imm r1_val r2_val).r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    -- Structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure (BeqInput_of_bus exec_row imm r1_val r2_val)).nextPC)
    (h_not_throws : (PureSpec.execute_BEQ_pure (BeqInput_of_bus exec_row imm r1_val r2_val)).throws = false)
    (h_success : (PureSpec.execute_BEQ_pure (BeqInput_of_bus exec_row imm r1_val r2_val)).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2

    := by
  exact equiv_BEQ_metaplan_from_bus state
    (BeqInput_of_bus exec_row imm r1_val r2_val) imm r1 r2 misa_val exec_row
    rfl h_input_r1 h_input_r2
    h_input_misa h_misa_c 
    h_bus rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_not_throws h_success

/-- **Track Q POC for BEQ.** Operation-bus companion to
    `equiv_BEQ_metaplan_from_bus`: drops the scenario-binding
    `h_input_r1` / `h_input_r2` parameters in favour of a single
    `h_op_bus : (op_bus_effect [op_entry] state rs1 rs2).1`
    precondition.

    The op-bus carries register *values* (in `a_lo`/`a_hi`/`b_lo`/`b_hi`)
    rather than pointer-keyed register-byte payloads — so the user
    additionally supplies the proof witness that the bus's
    `lanes_to_bv64` reconstructions equal `beq_input.r1_val` /
    `beq_input.r2_val`. The hypothesis `h_mult : op_entry.multiplicity
    = 1` pins the entry as Main's assume-side branch emission.

    Proof body: split `h_op_bus` via `chip_op_bus_hyps_branch`,
    rewrite the resulting `read_xreg` values to match the
    `beq_input` fields via `h_a_match` / `h_b_match`, and delegate to
    `equiv_BEQ_metaplan_from_bus`. -/
theorem equiv_BEQ_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (op_entry : OperationBusEntry FGL)
    (h_input_imm : beq_input.imm = imm)
    -- Op-bus precondition (replaces h_input_r1 / h_input_r2).
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      beq_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      beq_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Memory-bus precondition (PC read).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : beq_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    -- Structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC)
    (h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false)
    (h_success : (PureSpec.execute_BEQ_pure beq_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2 := by
  -- Extract the two register-read equalities from the op-bus precondition.
  have h_reads := ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_branch
    state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  obtain ⟨h_r1_read, h_r2_read⟩ := h_reads
  -- Rewrite the lane-recombined values to match `beq_input.r1_val` / `r2_val`.
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state := by rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state := by rw [h_b_match]; exact h_r2_read
  -- Delegate to the previously-shipped `_from_bus` form.
  exact equiv_BEQ_metaplan_from_bus state beq_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_misa h_misa_c
    h_bus h_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Two Sail-side-only theorems characterising the
`success = false` ∨ `throws = true` partition of `execute_BEQ_pure`'s
output. No bus-effect equation — see the docstring on
`equiv_BLT_metaplan_misaligned` for the modeling-gap analysis.

Case-split predicate is `h_taken : beq_input.r1_val = beq_input.r2_val`
(BEQ taken on EQUAL). -/

/-- **Misaligned-target companion (bit-1 case): Sail-side reduction.**
    Mirrors `equiv_BLT_metaplan_misaligned`. -/
theorem equiv_BEQ_metaplan_misaligned
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Misaligned-target hypotheses (bit-1 case, bit-0 aligned):
    (h_taken : beq_input.r1_val = beq_input.r2_val)
    (h_bit0_aligned :
      BitVec.ofBool (beq_input.PC + BitVec.signExtend 64 beq_input.imm)[0] = 0#1)
    (h_bit1_misaligned :
      BitVec.ofBool (beq_input.PC + BitVec.signExtend 64 beq_input.imm)[1] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = EStateM.Result.ok
          (ExecutionResult.Memory_Exception
            ((virtaddr.Virtaddr (beq_input.PC + BitVec.signExtend 64 beq_input.imm)),
             (ExceptionType.E_Fetch_Addr_Align ())))
          (write_reg_state state Register.nextPC (beq_input.PC + 4#64)) := by
  rw [equiv_BEQ_sail state beq_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  have h_eq_b : (beq_input.r1_val == beq_input.r2_val) = true := by
    simp [h_taken]
  simp [PureSpec.execute_BEQ_pure, h_eq_b, h_bit0_aligned, h_bit1_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure, write_reg_state]

/-- **Misaligned-target companion (bit-0 case): Sail-side reduction.**
    Mirrors `equiv_BLT_metaplan_misaligned_bit0`. -/
theorem equiv_BEQ_metaplan_misaligned_bit0
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_taken : beq_input.r1_val = beq_input.r2_val)
    (h_bit0_misaligned :
      BitVec.ofBool (beq_input.PC + BitVec.signExtend 64 beq_input.imm)[0] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = EStateM.Result.error
          (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          (write_reg_state state Register.nextPC (beq_input.PC + 4#64)) := by
  rw [equiv_BEQ_sail state beq_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  have h_eq_b : (beq_input.r1_val == beq_input.r2_val) = true := by
    simp [h_taken]
  simp [PureSpec.execute_BEQ_pure, h_eq_b, h_bit0_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind,
        EStateM.bind, write_reg_state]

end ZiskFv.Equivalence.BranchEqual
