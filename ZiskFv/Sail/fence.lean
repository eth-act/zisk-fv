import ZiskFv.Sail.Auxiliaries
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

**Track R retirement:** the previous trust axiom
`execute_FENCE_pure_equiv_axiom` is now `theorem
execute_FENCE_pure_equiv`, proved under the M-mode privilege
assumption (consistent with `RISC_V_assumptions` A1.1 — ZisK targets
RV64IM Machine-mode only). The proof unfolds `is_fiom_active` via
the privilege hypothesis, simplifies `effective_fence_set _ false`
to identity, and discharges the 11-arm `(pred, succ)` barrier match
by exhausting the 16 BitVec-2 pair combinations (each arm becomes
the constant `fun s ↦ EStateM.Result.ok RETIRE_SUCCESS s` after
`sail_barrier` unfolds to `pure ()`).
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

  /-- Helper: with `cur_privilege = Machine`, `is_fiom_active ()`
      returns `false` without modifying state. -/
  private lemma is_fiom_active_machine
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (h_priv : state.regs.get? Register.cur_privilege = .some Privilege.Machine) :
      LeanRV64D.Functions.is_fiom_active () state =
        EStateM.Result.ok false state := by
    simp [LeanRV64D.Functions.is_fiom_active, readReg_succ h_priv]

  /-- Helper: under `cur_privilege = Machine`, the entire body of
      Sail's `execute_FENCE` reduces to `pure RETIRE_SUCCESS` with no
      state change.

      All 11 (pred, succ) match arms are either `sail_barrier _`
      (defined as `pure ()`) or an explicit `pure ()`, so the inner
      match collapses uniformly. With `fiom = false`,
      `effective_fence_set _ false` is identity. -/
  private lemma execute_FENCE_machine_pure
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
      (fm pred succ : BitVec 4) (rs rd : regidx)
      (h_priv : state.regs.get? Register.cur_privilege = .some Privilege.Machine) :
      LeanRV64D.Functions.execute_FENCE fm pred succ rs rd state =
        EStateM.Result.ok (ExecutionResult.Retire_Success ()) state := by
    simp [LeanRV64D.Functions.execute_FENCE,
          is_fiom_active_machine _ h_priv,
          LeanRV64D.Functions.effective_fence_set,
          Sail.ConcurrencyInterfaceV1.sail_barrier,
          PreSail.ConcurrencyInterfaceV1.sail_barrier]
    -- All 11 (pred, succ) match arms are now the same constant
    -- function `fun s ↦ EStateM.Result.ok RETIRE_SUCCESS s`. Apply
    -- `congrFun` to push the `state` argument inward, then split on
    -- the pair-match (now state-free) and close each arm by `rfl`.
    generalize BitVec.extractLsb 1 0 pred = p
    generalize BitVec.extractLsb 1 0 succ = q
    rcases p with ⟨np, hp⟩
    rcases q with ⟨nq, hq⟩
    -- BitVec 2 = Fin 4, so 16 cases
    interval_cases np <;> interval_cases nq <;> rfl

  /-- Sail-side equivalence theorem for FENCE.

      The Sail body of `execute_FENCE` (via barrier pattern-match →
      `sail_barrier _ = pure ()`) is semantically a no-op. With
      `cur_privilege = Machine` (true for ZisK's M-mode-only zkVM),
      `is_fiom_active ()` is constantly `false`, `effective_fence_set
      _ false` is identity, and the 11-arm pred/succ match collapses
      uniformly to `pure ()` regardless of input bits. -/
  theorem execute_FENCE_pure_equiv
      (fence_input : FenceInput) (fm pred succ : BitVec 4)
      (rs rd : regidx)
      (h_input_pc : state.regs.get? Register.PC = .some fence_input.PC)
      (h_input_priv :
        state.regs.get? Register.cur_privilege = .some Privilege.Machine) :
      execute_instruction (instruction.FENCE (fm, pred, succ, rs, rd)) state =
      let fence_output := execute_FENCE_pure fence_input
      (do
        Sail.writeReg Register.nextPC fence_output.nextPC
        pure (ExecutionResult.Retire_Success ())
      ) state := by
    -- The post-`writeReg nextPC (PC+4)` state still has
    -- `cur_privilege = Machine` (only `nextPC` changed).  Use the
    -- normalised `+ 4#64` form so the rewrite below matches the goal
    -- shape after `simp` reduces `Sail.BitVec.addInt`.
    have h_priv' : (write_reg_state state Register.nextPC
        (fence_input.PC + 4#64)).regs.get?
          Register.cur_privilege = .some Privilege.Machine := by
      simp [write_reg_state]
      grind
    simp [
      readReg_succ h_input_pc,
      writeReg_state_success,
      LeanRV64D.Functions.execute,
      execute_FENCE_machine_pure _ fm pred succ rs rd h_priv',
      execute_FENCE_pure,
    ]

end PureSpec
