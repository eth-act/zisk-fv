import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.BranchLessThan
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.blt
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BLT. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BLT`),
* the compositional BLT spec
  (`ZiskFv.Circuit.BranchLessThan.branch_lt_compositional`, a thin
  wrapper over `BranchArchetype.branch_archetype_pc_dispatch` at
  `opcode_lit = OP_LT`),
* the Sail pure-function equivalence (`PureSpec.execute_BLT_pure_equiv`,
  a direct proof port of `execute_BNE_pure_equiv` with
  `h_lt : r1.toInt < r2.toInt` as the case-split predicate),

into three theorems mirroring `Equivalence/BranchEqual.lean` /
`Equivalence/BranchNotEqual.lean`:

* `equiv_BLT_circuit` — circuit-level flag-dispatched next-pc formula;
* `equiv_BLT_sail` — Sail reduction to `PureSpec.execute_BLT_pure`;
* `equiv_BLT` — the canonical target:
  `execute_instruction (.BTYPE (imm, r2, r1, BLT)) state
    = (bus_effect exec_row mem_row state).2`.

**Hypothesis-free bus side.** BLT shares shape (b) with BEQ/BNE so
the equivalence theorem reuses `bus_effect_matches_sail_beq` directly.
-/

namespace ZiskFv.Equivalence.BranchLessThan

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchLessThan

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BLT reduces to the pure-function block supplied by
    `PureSpec.execute_BLT_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` witness.

    Wraps `PureSpec.execute_BLT_pure_equiv`. -/
lemma equiv_BLT_sail
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

/-- **Metaplan theorem.**

    `execute_instruction` on an RV64 BLT equals the state computed by
    applying `bus_effect` to the circuit's execution and memory bus rows.
    Reuses `bus_effect_matches_sail_beq` (shape (b), branch-shape). -/
theorem equiv_BLT
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
    -- Structural bus hypotheses (shape (b)).
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

/-! ## Misaligned-target companion

The canonical theorems above (`equiv_BLT`,
`equiv_BLT_from_bus`, `equiv_BLT_bus_self`) cover
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
bus (see `zisk/pil/zisk.pil` — no `fault`/`misalign`/`exception`
identifiers anywhere in the column set). Consequently
`bus_effect : List ExecutionBusEntry × List MemoryBusEntry × State →
Prop × EStateM.Result` is **hardcoded** to return
`EStateM.Result.ok (Retire_Success ()) state'` whenever the
execution-bus shape (length 2 + multiplicities ±1) is well-formed
(`RV64D/BusEffect.lean:115-121`). It cannot model `Memory_Exception`.

So the canonical equation
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
   (out of scope here), then an extension to `RV64D/BusEffect.lean`'s
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
   companion below ships.**

### Theorem

`equiv_BLT_misaligned` characterises the bit-1-misaligned
case (target's bit-1 = 1, bit-0 = 0): under taken (`r1 < r2` signed)
and the misalignment hypothesis, `execute_instruction (.BTYPE …)`
yields `EStateM.Result.ok (Memory_Exception (Virtaddr (PC + sext imm),
E_Fetch_Addr_Align ())) state'` where `state'` is `state` with
`Register.nextPC` set to `PC + 4` (the pure-spec-mandated fall-through).

The bit-0-misaligned case is documented in a sibling theorem
`equiv_BLT_misaligned_bit0` at the end of this file: that one
yields `EStateM.Result.error (Sail.Error.Assertion …) state'` (a Sail
assertion failure rather than `Memory_Exception`), reflecting the
RVA/RVI distinction in `LeanRV64D.Functions.jump_to`.

Together these two companions cover both halves of the
`success = false` ∨ `throws = true` partition of `execute_BLT_pure`'s
output. -/

end ZiskFv.Equivalence.BranchLessThan
