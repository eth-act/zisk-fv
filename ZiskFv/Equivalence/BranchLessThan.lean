import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchLessThan
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.blt
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BLT (Phase 3A B1). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BLT`),
* the compositional BLT spec
  (`ZiskFv.Spec.BranchLessThan.branch_lt_compositional`, a thin
  wrapper over `BranchArchetype.branch_archetype_pc_dispatch` at
  `opcode_lit = OP_LT`),
* the Sail pure-function equivalence
  (`PureSpec.execute_BLT_pure_equiv`, a direct proof port of
  `execute_BNE_pure_equiv` with `h_lt : r1.toInt < r2.toInt` as the
  case-split predicate — Phase 4 retired C2a),

into three theorems mirroring `Equivalence/BranchEqual.lean` /
`Equivalence/BranchNotEqual.lean`:

* `equiv_BLT` — circuit-level flag-dispatched next-pc formula;
* `equiv_BLT_sail` — Sail reduction to `PureSpec.execute_BLT_pure`;
* `equiv_BLT_metaplan` — the metaplan target:
  `execute_instruction (.BTYPE (imm, r2, r1, BLT)) state
    = (bus_effect exec_row mem_row state).2`.

**Hypothesis-free bus side.** D3 closed bus-emission for shape (b)
(externally-routed branches); BLT shares shape (b) with BEQ/BNE so
the metaplan theorem reuses `bus_effect_matches_sail_beq` directly.
-/

namespace ZiskFv.Equivalence.BranchLessThan

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.BranchLessThan

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BLT theorem.** Given the branch-subset Main
    constraints plus the mode witnesses from `transpile_BLT`, the
    next-pc cell satisfies the flag-dispatched handshake formula.
    Identical in shape to `equiv_BEQ`/`equiv_BNE` — the opcode literal
    only surfaces at the bus-flag-correctness layer. -/
theorem equiv_BLT
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_lt_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_lt_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BLT reduces to the pure-function block supplied by
    `PureSpec.execute_BLT_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` witness.

    Wraps `PureSpec.execute_BLT_pure_equiv`. -/
theorem equiv_BLT_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = let blt_output := PureSpec.execute_BLT_pure blt_input
        (do
          Sail.writeReg Register.nextPC blt_output.nextPC
          if blt_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !blt_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (blt_input.PC + BitVec.signExtend 64 blt_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BLT_pure_equiv blt_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem (Phase 3A B1).**

    `execute_instruction` on an RV64 BLT equals the state computed by
    applying `bus_effect` to the circuit's execution and memory bus rows.
    Reuses `bus_effect_matches_sail_beq` (shape (b), branch-shape). -/
theorem equiv_BLT_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses (Phase 2.5 D3 shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false)
    (h_success : (PureSpec.execute_BLT_pure blt_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BLT_sail state blt_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge bus-side equation via the shape (b) lemma (shared across
  -- shape (b) branch opcodes: BEQ/BNE/BLT/BGE/BLTU/BGEU).
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BLT_pure blt_input).nextPC
    (PureSpec.execute_BLT_pure blt_input).throws
    (PureSpec.execute_BLT_pure blt_input).success
    blt_input.PC blt_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- **Phase 5 V12 companion for BLT.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. Other
    `h_input_*` stay — branch memory bus is empty, so rs1/rs2
    reads go via operation bus (not derivable from `h_bus` here). -/
theorem equiv_BLT_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Phase 5 V12: bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : blt_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    -- Structural bus hypotheses (Phase 2.5 D3 shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false)
    (h_success : (PureSpec.execute_BLT_pure blt_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2
    := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some blt_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_BLT_metaplan state blt_input imm r1 r2 misa_val exec_row h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- Constructor: build a `PureSpec.BltInput` from exec_row PC + free operand values. -/
def BltInput_of_bus
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 13)
    (r1_val r2_val : BitVec 64) :
    PureSpec.BltInput :=
  { imm := imm
    r1_val := r1_val
    r2_val := r2_val
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for BLT.** Bus-derived input form. -/
theorem equiv_BLT_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (r1_val r2_val : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok (BltInput_of_bus exec_row imm r1_val r2_val).r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok (BltInput_of_bus exec_row imm r1_val r2_val).r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Phase 5 V12: bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    -- Structural bus hypotheses (Phase 2.5 D3 shape (b)).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure (BltInput_of_bus exec_row imm r1_val r2_val)).nextPC)
    (h_not_throws : (PureSpec.execute_BLT_pure (BltInput_of_bus exec_row imm r1_val r2_val)).throws = false)
    (h_success : (PureSpec.execute_BLT_pure (BltInput_of_bus exec_row imm r1_val r2_val)).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2

    := by
  exact equiv_BLT_metaplan_from_bus state
    (BltInput_of_bus exec_row imm r1_val r2_val) imm r1 r2 misa_val exec_row
    rfl h_input_r1 h_input_r2
    h_input_misa h_misa_c 
    h_bus rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_not_throws h_success

/-- **Track Q POC for BLT.** Operation-bus companion to
    `equiv_BLT_metaplan_from_bus`: drops the scenario-binding
    `h_input_r1` / `h_input_r2` parameters in favour of a single
    `h_op_bus : (op_bus_effect [op_entry] state rs1 rs2).1`
    precondition. Mirrors `equiv_BEQ_metaplan_op_bus`. -/
theorem equiv_BLT_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (op_entry : OperationBusEntry FGL)
    (h_input_imm : blt_input.imm = imm)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      blt_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      blt_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : blt_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false)
    (h_success : (PureSpec.execute_BLT_pure blt_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2 := by
  have h_reads := ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_branch
    state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  obtain ⟨h_r1_read, h_r2_read⟩ := h_reads
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state := by rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state := by rw [h_b_match]; exact h_r2_read
  exact equiv_BLT_metaplan_from_bus state blt_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_misa h_misa_c
    h_bus h_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Phase 6 Track T POC: misaligned-target companion

The metaplan theorems above (`equiv_BLT_metaplan`,
`equiv_BLT_metaplan_from_bus`, `equiv_BLT_metaplan_bus_self`) cover
**only the happy path** where the branch target is 4-byte aligned
(both bit-0 and bit-1 of `PC + sext imm` are 0). The hypotheses
`h_not_throws : (...).throws = false` and
`h_success : (...).success = true` exclude misaligned targets.

This is a real completeness gap for the FV trust base: a binary that
emits a BLT whose taken target is misaligned (bit-1 of `PC + sext imm`
equals 1) would, per RV64I, raise `Memory_Exception
(Virtaddr (PC + sext imm), E_Fetch_Addr_Align ())`. Our existing
proofs say nothing about that path.

### Bus-effect modeling gap

ZisK's PIL emits **no fault-flag column** on the operation/execution
bus (see `vendor/zisk/pil/zisk.pil` — no `fault`/`misalign`/`exception`
identifiers anywhere in the column set). Consequently
`bus_effect : List ExecutionBusEntry × List MemoryBusEntry × State →
Prop × EStateM.Result` is **hardcoded** to return
`EStateM.Result.ok (Retire_Success ()) state'` whenever the
execution-bus shape (length 2 + multiplicities ±1) is well-formed
(`RV64D/BusEffect.lean:115-121`). It cannot model `Memory_Exception`.

So the metaplan-shape equation
`execute_instruction (.BTYPE …) state = (bus_effect exec_row [] state).2`
is **literally false** in the misaligned-success-fail case: the LHS
returns `.ok (Memory_Exception …) state'` while the RHS returns
`.ok (Retire_Success ()) state'`. The two `EStateM.Result.ok` payloads
have different `ExecutionResult` constructors (`Memory_Exception` vs.
`Retire_Success`), so propositional equality fails by a constructor
mismatch even when the post-states agree.

Closing this gap requires one of:

1. **Extend `bus_effect`** to emit `Memory_Exception` when a future
   PIL fault-flag column is asserted. This needs new ZisK PIL columns
   (Track T's circuit-side prerequisite — out of scope for the FV-only
   POC), then a Phase 4-shape extension to `RV64D/BusEffect.lean`'s
   final `match post_memory.2 with` block to dispatch on the new flag.

2. **Project the comparison to states only.** Prove
   `(execute_instruction …).snd state = (bus_effect …).snd state` —
   weaker but directly closeable, since `execute_BLT_pure` already
   pins the misaligned-failure nextPC writeback to `PC + 4` (matching
   what an honest ZisK trace would emit for a known-misaligned target,
   though ZisK has no enforcement mechanism today).

3. **Companion theorem characterising the Sail RHS only.** Prove
   that under misaligned-target hypotheses the LHS reduces to a
   concrete `Memory_Exception` form, leaving the bus-side equation
   for option (1)/(2) once infrastructure exists. **This is what the
   POC below ships.**

### Theorem

`equiv_BLT_metaplan_misaligned` characterises the bit-1-misaligned
case (target's bit-1 = 1, bit-0 = 0): under taken (`r1 < r2` signed)
and the misalignment hypothesis, `execute_instruction (.BTYPE …)`
yields `EStateM.Result.ok (Memory_Exception (Virtaddr (PC + sext imm),
E_Fetch_Addr_Align ())) state'` where `state'` is `state` with
`Register.nextPC` set to `PC + 4` (the pure-spec-mandated fall-through).

The bit-0-misaligned case is documented in a sibling theorem
`equiv_BLT_metaplan_misaligned_bit0` at the end of this file: that one
yields `EStateM.Result.error (Sail.Error.Assertion …) state'` (a Sail
assertion failure rather than `Memory_Exception`), reflecting the
RVA/RVI distinction in `LeanRV64D.Functions.jump_to`.

Together these two companions cover both halves of the
`success = false` ∨ `throws = true` partition of `execute_BLT_pure`'s
output. -/

/-- **Misaligned-target companion (bit-1 case): Sail-side reduction.**

    Under taken-branch and bit-1-misaligned target hypotheses (and
    bit-0 aligned, so this is `Memory_Exception` not `Assertion`),
    `execute_instruction (.BTYPE …)` reduces to
    `.ok (Memory_Exception (Virtaddr target, E_Fetch_Addr_Align ()))`
    on a state with `nextPC := PC + 4` (per `execute_BLT_pure`'s
    fall-through normalisation when `fails = true`).

    No bus-effect comparison: see the docstring above for why
    `(bus_effect exec_row [] state).2` cannot be reached today.

    Reuses `equiv_BLT_sail` (no new axiom). -/
theorem equiv_BLT_metaplan_misaligned
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Misaligned-target hypotheses (bit-1 case, bit-0 aligned):
    (h_taken : blt_input.r1_val.toInt < blt_input.r2_val.toInt)
    (h_bit0_aligned :
      BitVec.ofBool (blt_input.PC + BitVec.signExtend 64 blt_input.imm)[0] = 0#1)
    (h_bit1_misaligned :
      BitVec.ofBool (blt_input.PC + BitVec.signExtend 64 blt_input.imm)[1] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = EStateM.Result.ok
          (ExecutionResult.Memory_Exception
            ((virtaddr.Virtaddr (blt_input.PC + BitVec.signExtend 64 blt_input.imm)),
             (ExceptionType.E_Fetch_Addr_Align ())))
          (write_reg_state state Register.nextPC (blt_input.PC + 4#64)) := by
  -- Reduce the LHS to the pure-spec block via `equiv_BLT_sail`.
  rw [equiv_BLT_sail state blt_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Pattern follows `RV64D/jal.lean` misaligned-bit-1 case (lines 125-132).
  have h_lt_b : (blt_input.r1_val.toInt <b blt_input.r2_val.toInt) = true := by
    simp [h_taken]
  -- The post-rewrite goal references `blt_input.imm`; use raw hypotheses.
  simp [PureSpec.execute_BLT_pure, h_lt_b, h_bit0_aligned, h_bit1_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure, write_reg_state]

/-- **Misaligned-target companion (bit-0 case): Sail-side reduction.**

    Under taken-branch and bit-0-misaligned target hypotheses
    (bit-0 = 1), `execute_instruction (.BTYPE …)` reduces to
    `.error (Sail.Error.Assertion …)` on a state with
    `nextPC := PC + 4`. This is a Sail-level assertion failure, not a
    `Memory_Exception` ExecutionResult — `LeanRV64D.Functions.jump_to`
    triggers the assertion path before the alignment-check fall-through.

    Like the bit-1 case, no bus-effect equation: `bus_effect` cannot
    return `EStateM.Result.error`. -/
theorem equiv_BLT_metaplan_misaligned_bit0
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Misaligned-target hypotheses (bit-0 case):
    (h_taken : blt_input.r1_val.toInt < blt_input.r2_val.toInt)
    (h_bit0_misaligned :
      BitVec.ofBool (blt_input.PC + BitVec.signExtend 64 blt_input.imm)[0] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = EStateM.Result.error
          (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          (write_reg_state state Register.nextPC (blt_input.PC + 4#64)) := by
  rw [equiv_BLT_sail state blt_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Pattern follows `RV64D/jal.lean` misaligned-bit-0 case (lines 173-176).
  have h_lt_b : (blt_input.r1_val.toInt <b blt_input.r2_val.toInt) = true := by
    simp [h_taken]
  -- Reduce the pure-spec record fields and the Sail bind chain.
  -- (`EStateM.throw` reduces to `EStateM.Result.error` via the high-priority
  -- `throw_equiv` simp lemma in `RV64D/Auxiliaries.lean`.)
  simp [PureSpec.execute_BLT_pure, h_lt_b, h_bit0_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind,
        EStateM.bind, write_reg_state]

end ZiskFv.Equivalence.BranchLessThan
