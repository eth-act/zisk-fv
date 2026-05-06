import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.BranchNotEqual
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.bne
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BNE. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BNE`),
* the compositional BNE spec
  (`ZiskFv.Circuit.BranchNotEqual.branch_ne_compositional`, which is
  a thin wrapper over the archetype macro
  `BranchArchetype.branch_archetype_pc_dispatch` at `opcode_lit = OP_EQ`),
* the Sail pure-function equivalence (`PureSpec.execute_BNE_pure_equiv`,
  closed in `RV64D/bne.lean`),

into three theorems mirroring `Equivalence/BranchEqual.lean`:

* `equiv_BNE_circuit` — the circuit-level flag-dispatched next-pc formula
  (same shape as `equiv_BEQ_circuit`; the polarity flip only shows up after
  composing with `transpile_BNE`'s `jmp_offset1`/`jmp_offset2` swap),
* `equiv_BNE_sail` — the Sail reduction to `PureSpec.execute_BNE_pure`,
* `equiv_BNE` — the canonical shape:
  `execute_instruction (.BTYPE (imm, r2, r1, BNE)) state
    = (bus_effect exec_row mem_row state).2`.

**Hypothesis-free bus side.** BEQ and BNE share shape (b) so the
equivalence theorem reuses `bus_effect_matches_sail_beq` — the shape
lemma is opcode-agnostic within shape (b).
-/

namespace ZiskFv.Equivalence.BranchNotEqual

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchNotEqual

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BNE theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BNE`, the
    next-pc cell satisfies the same flag-dispatched handshake formula
    as BEQ. The polarity flip (flag = 0 taken, flag = 1 not-taken)
    emerges after composing with `transpile_BNE`'s
    `jmp_offset1 = 4, jmp_offset2 = imm` assignment — at the Main-AIR
    level, the formula is literally the same as BEQ's. -/
theorem equiv_BNE_circuit
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_ne_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_ne_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BNE reduces to the pure-function block supplied by
    `PureSpec.execute_BNE_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` witness.

    Wraps `PureSpec.execute_BNE_pure_equiv`. -/
theorem equiv_BNE_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = let bne_output := PureSpec.execute_BNE_pure bne_input
        (do
          Sail.writeReg Register.nextPC bne_output.nextPC
          if bne_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bne_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 64 bne_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BNE_pure_equiv bne_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.**

    `execute_instruction` on an RV64 BNE equals the state computed by
    applying `bus_effect` to the circuit's execution and memory bus rows.
    BEQ and BNE share shape (b) — two execution-bus entries (pc read,
    nextpc write), empty memory bus — so this theorem reuses
    `bus_effect_matches_sail_beq` directly. -/
theorem equiv_BNE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses (shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false)
    (h_success : (PureSpec.execute_BNE_pure bne_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BNE_sail state bne_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge the bus-side equation via the shape (b) lemma (shared
  -- with BEQ — shape (b) is the externally-routed branch shape).
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BNE_pure bne_input).nextPC
    (PureSpec.execute_BNE_pure bne_input).throws
    (PureSpec.execute_BNE_pure bne_input).success
    bne_input.PC bne_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- **Bus-driven companion for BNE.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. Other
    `h_input_*` stay — branch memory bus is empty, so rs1/rs2
    reads go via operation bus (not derivable from `h_bus` here). -/
theorem equiv_BNE_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : bne_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    -- Structural bus hypotheses (shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false)
    (h_success : (PureSpec.execute_BNE_pure bne_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2
    := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some bne_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_BNE state bne_input imm r1 r2 misa_val exec_row h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- Constructor: build a `PureSpec.BneInput` from exec_row PC + free operand values. -/
def BneInput_of_bus
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 13)
    (r1_val r2_val : BitVec 64) :
    PureSpec.BneInput :=
  { imm := imm
    r1_val := r1_val
    r2_val := r2_val
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for BNE.** Bus-derived input form. -/
theorem equiv_BNE_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (r1_val r2_val : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok (BneInput_of_bus exec_row imm r1_val r2_val).r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok (BneInput_of_bus exec_row imm r1_val r2_val).r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    -- Structural bus hypotheses (shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure (BneInput_of_bus exec_row imm r1_val r2_val)).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure (BneInput_of_bus exec_row imm r1_val r2_val)).throws = false)
    (h_success : (PureSpec.execute_BNE_pure (BneInput_of_bus exec_row imm r1_val r2_val)).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2

    := by
  exact equiv_BNE_from_bus state
    (BneInput_of_bus exec_row imm r1_val r2_val) imm r1 r2 misa_val exec_row
    rfl h_input_r1 h_input_r2
    h_input_misa h_misa_c
    h_bus rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_not_throws h_success

/-- **Track Q POC for BNE.** Operation-bus companion to
    `equiv_BNE_from_bus`: drops the scenario-binding
    `h_input_r1` / `h_input_r2` parameters in favour of a single
    `h_op_bus : (op_bus_effect [op_entry] state rs1 rs2).1`
    precondition.

    Mirrors `equiv_BEQ_op_bus` shape-for-shape; only the
    opcode literal (`bop.BNE`) and pure-spec name (`execute_BNE_pure`)
    change. -/
theorem equiv_BNE_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (op_entry : OperationBusEntry FGL)
    (h_input_imm : bne_input.imm = imm)
    -- Op-bus precondition (replaces h_input_r1 / h_input_r2).
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      bne_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      bne_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Memory-bus precondition (PC read).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : bne_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    -- Structural bus hypotheses (shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false)
    (h_success : (PureSpec.execute_BNE_pure bne_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2 := by
  have h_reads := ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_branch
    state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  obtain ⟨h_r1_read, h_r2_read⟩ := h_reads
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state := by rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state := by rw [h_b_match]; exact h_r2_read
  exact equiv_BNE_from_bus state bne_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_misa h_misa_c
    h_bus h_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BEQ; case-split predicate is `h_taken : r1_val ≠ r2_val`
(BNE taken on NOT-EQUAL — `skip = !(r1 != r2) = (r1 == r2) = false`). -/

/-- **Misaligned-target companion (bit-1 case): Sail-side reduction.** -/
theorem equiv_BNE_misaligned
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_taken : bne_input.r1_val ≠ bne_input.r2_val)
    (h_bit0_aligned :
      BitVec.ofBool (bne_input.PC + BitVec.signExtend 64 bne_input.imm)[0] = 0#1)
    (h_bit1_misaligned :
      BitVec.ofBool (bne_input.PC + BitVec.signExtend 64 bne_input.imm)[1] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = EStateM.Result.ok
          (ExecutionResult.Memory_Exception
            ((virtaddr.Virtaddr (bne_input.PC + BitVec.signExtend 64 bne_input.imm)),
             (ExceptionType.E_Fetch_Addr_Align ())))
          (write_reg_state state Register.nextPC (bne_input.PC + 4#64)) := by
  rw [equiv_BNE_sail state bne_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  have h_neq_b : (bne_input.r1_val != bne_input.r2_val) = true :=
    bne_iff_ne.mpr h_taken
  simp [PureSpec.execute_BNE_pure, h_neq_b, h_bit0_aligned, h_bit1_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure, write_reg_state]

/-- **Misaligned-target companion (bit-0 case): Sail-side reduction.** -/
theorem equiv_BNE_misaligned_bit0
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_taken : bne_input.r1_val ≠ bne_input.r2_val)
    (h_bit0_misaligned :
      BitVec.ofBool (bne_input.PC + BitVec.signExtend 64 bne_input.imm)[0] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = EStateM.Result.error
          (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          (write_reg_state state Register.nextPC (bne_input.PC + 4#64)) := by
  rw [equiv_BNE_sail state bne_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  have h_neq_b : (bne_input.r1_val != bne_input.r2_val) = true :=
    bne_iff_ne.mpr h_taken
  simp [PureSpec.execute_BNE_pure, h_neq_b, h_bit0_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind,
        EStateM.bind, write_reg_state]

end ZiskFv.Equivalence.BranchNotEqual
