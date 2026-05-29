import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.ZiskCircuit.BranchNotEqual
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.bne
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.EquivCore.Promises.Branch
import ZiskFv.Compliance.SharedBundles

/-!
End-to-end theorem for RV64 BNE. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_BNE`),
* the compositional BNE spec
  (`ZiskFv.ZiskCircuit.BranchNotEqual.branch_ne_compositional`, which is
  a thin wrapper over the archetype macro
  `BranchArchetype.branch_archetype_pc_dispatch` at `opcode_lit = OP_EQ`),
* the Sail pure-function equivalence (`PureSpec.execute_BNE_pure_equiv`,
  closed in `RV64D/bne.lean`),

into three theorems mirroring `Equivalence/Beq.lean`:

* `equiv_BNE_sail` — the Sail reduction to `PureSpec.execute_BNE_pure`,
* `equiv_BNE` — the canonical shape:
  `execute_instruction (.BTYPE (imm, r2, r1, BNE)) state
    = (bus_effect exec_row mem_row state).2`.

**Hypothesis-free bus side.** BEQ and BNE share shape (b) so the
equivalence theorem reuses `bus_effect_matches_sail_beq` — the shape
lemma is opcode-agnostic within shape (b).
-/

namespace ZiskFv.EquivCore.Bne

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.BranchNotEqual


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 BNE reduces to the pure-function block supplied by
    `PureSpec.execute_BNE_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` witness.

    Wraps `PureSpec.execute_BNE_pure_equiv`. -/
lemma equiv_BNE_sail
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

/-- **Canonical equivalence.**

    `execute_instruction` on an RV64 BNE equals the state computed by
    applying `bus_effect` to the circuit's execution and memory bus rows.
    BEQ and BNE share shape (b) — two execution-bus entries (pc read,
    nextpc write), empty memory bus — so this theorem reuses
    `bus_effect_matches_sail_beq` directly. -/
theorem equiv_BNE
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    execute_instruction (instruction.BTYPE (ops.imm, ops.r2, ops.r1, bop.BNE)) state
      = (bus_effect ops.exec_row [] state).2 := by
  obtain ⟨imm, r1, r2, misa_val, exec_row⟩ := ops
  obtain ⟨h_input_imm, h_input_r1, h_input_r2, h_input_pc,
          h_input_misa, h_misa_c, h_exec_len, h_e0_mult, h_e1_mult,
          h_nextPC_matches, h_not_throws, h_success⟩ := promises
  rw [equiv_BNE_sail state bne_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  -- Discharge the bus-side equation via the shape (b) lemma (shared
  -- with BEQ — shape (b) is the externally-routed branch shape).
  symm
  exact ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BNE_pure bne_input).nextPC
    (PureSpec.execute_BNE_pure bne_input).throws
    (PureSpec.execute_BNE_pure bne_input).success
    bne_input.PC bne_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BEQ; case-split predicate is `h_taken : r1_val ≠ r2_val`
(BNE taken on NOT-EQUAL — `skip = !(r1 != r2) = (r1 == r2) = false`). -/

end ZiskFv.EquivCore.Bne
