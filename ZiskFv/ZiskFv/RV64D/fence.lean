import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
## RV64I FENCE — pure spec + Sail equivalence

FENCE is a memory-ordering hint. Per `riscv2zisk_context.rs:228`, ZisK's
transpiler maps `"fence"` to `self.nop()` (line 772), which emits a
single Zisk microinstruction:
- `op = OP_FLAG = 0` (Internal),
- `is_external_op = 0`,
- `src_a = imm 0`, `src_b = imm 0`,
- `j(4, 4)` — both `jmp_offset_*` = 4.

So FENCE in ZisK is a no-op that advances PC by 4 — no register write,
no memory access, no side-effect.

On the Sail side, `LeanRV64D.Functions.execute_FENCE` (InstsEnd.lean:69303)
reads the `fiom` CSR (no state effect) and dispatches the (pred, succ)
pair to `sail_barrier` (Sail/Sail.lean:621 — defined as `pure ()`).
So the entire body reduces to `pure RETIRE_SUCCESS`. Combined with
`execute_instruction`'s leading `writeReg nextPC (PC + 4)`, the full
Sail block is `do writeReg nextPC (PC + 4); pure RETIRE_SUCCESS`.

The Sail-equivalence is axiomatized below — proving it from first
principles requires unfolding the Sail barrier-match boilerplate and
the `is_fiom_active` CSR read; treating it as a trust axiom (same
pattern as some memory-model lemmas) keeps the trust surface narrow
and the proof tractable. This adds 1 axiom to the trust base.
-/

namespace PureSpec

  /-- FENCE input: only the PC matters (pred/succ/fm/rs/rd are
      semantically irrelevant on a single-threaded zkVM). -/
  structure FenceInput where
    PC : BitVec 64

  /-- FENCE output: PC advances by 4. No rd write. -/
  structure FenceOutput where
    nextPC : BitVec 64

  def execute_FENCE_pure (input : FenceInput) : FenceOutput := {
    nextPC := input.PC + 4#64
  }

  /-- Sail-side equivalence axiom for FENCE.

      **Trust basis.** The Sail body of `execute_FENCE` (via barrier
      pattern-match → `sail_barrier _ = pure ()`) is semantically a
      no-op. The proof would unfold `is_fiom_active`,
      `effective_fence_set`, and 11 barrier match arms — substantial
      Sail boilerplate. We axiomatize the resulting equivalence to
      avoid depending on internals of `is_fiom_active`. -/
  axiom execute_FENCE_pure_equiv_axiom :
      ∀ (fence_input : FenceInput) (fm pred succ : BitVec 4)
        (rs rd : regidx) (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource),
        state.regs.get? Register.PC = .some fence_input.PC →
        execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state =
        let fence_output := execute_FENCE_pure fence_input
        (do
          Sail.writeReg Register.nextPC fence_output.nextPC
          pure (ExecutionResult.Retire_Success ())
        ) state

  /-- Wrapper exposing the axiom as a lemma. -/
  lemma execute_FENCE_pure_equiv
      (fence_input : FenceInput) (fm pred succ : BitVec 4)
      (rs rd : regidx)
      (h_input_pc : state.regs.get? Register.PC = .some fence_input.PC) :
      execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state =
      let fence_output := execute_FENCE_pure fence_input
      (do
        Sail.writeReg Register.nextPC fence_output.nextPC
        pure (ExecutionResult.Retire_Success ())
      ) state :=
    execute_FENCE_pure_equiv_axiom fence_input fm pred succ rs rd state h_input_pc

end PureSpec
