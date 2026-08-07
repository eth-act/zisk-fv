import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridges

/-!
# Register-access chain bridges (#330)

`MemBusRowBridges` walks an active Main memory pull (`as = 2`) to its provider, and rules the
register boundary *out* of that classification by `mem_op` mismatch. This module walks the
complementary partition: the register file lives on the same MemBus at `mem_op = 3`
(`MEMORY_REG_OP`), and its accesses telescope boot → a → b → store → reload.

The first step is the dual exclusion. A Main pull whose evaluated `mem_op` is `3` cannot have been
provided by any of the memory-side components, because none of them can emit `mem_op = 3`:

| provider | `mem_op` | source |
|---|---|---|
| `MemAlignReadByte` | literal `1` | `MemAlignReadByte/Bridge.lean:76-77` |
| `MemAlignByte` | `1 + is_write` | `MemAlignByte/Bridge.lean:92-93` |
| `MemAlign` | `wr + 1` | `MemAlign/Bridge.lean:155-156` |
| `Mem` | `wr + 1` | `Mem/Bridge.lean:90` |
| `RegisterBoundary` boot / reload | literal `3` | `RegisterBoundary.lean:81,91` |
| Main `aRegPre` / `bRegPre` / `cRegPre` | literal `3` | `Main/Constraints.lean:397-403` |

`MemAlignReadByte` is the literal case and needs no booleanity hypothesis; the `wr` / `is_write`
cases need their AIR's booleanity and are handled separately.

Combined with `activeMainNonMutableMemProviderRowMatchSpec_branch_cases`, ruling the memory
providers out leaves exactly the two register-side branches — Main-self and `RegisterBoundary` —
which is the step that lets the register chain be walked forward rather than only ruled out.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- A component's row input, read from the environment, is the evaluation of its row input variable.

    Both sides reduce to `valueFromOffset component.Input 0`, but a provider `Spec` destructured out
    of a `…ProviderRowMatchSpec` arrives in the `rowInput` form while the message equality derived
    from balance arrives in the `eval … rowInputVar` form, so the two never meet syntactically.
    Bridging with `simp [circuit_norm]` instead times out at `whnf`. -/
theorem component_rowInput_eq_eval_rowInputVar
    (component : Component FGL) (env : Environment FGL) :
    component.rowInput env = eval env component.rowInputVar := by
  rw [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar,
    eval_varFromOffset_valueFromOffset]

/-- A Main memory-bus interaction at `mem_op = 3` (a register access) cannot have been provided by
    `MemAlignReadByte`, whose message pins `mem_op` to the literal `1`.

    Dual of `not_activeMainSelfAMemProviderRowMatchSpec_of_main_mem_op_one` and friends, which rule
    the register boundary out of the `as = 2` memory classification. -/
theorem not_activeMainMemAlignReadByteProviderRowMatchSpec_of_main_mem_op_three
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 3) :
    ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_marb
  rcases h_marb with
    ⟨providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, _h_providerTable, _h_providerInteraction,
      providerRow, _h_providerRow, _h_providerSpec, _h_providerComponent,
      h_providerEval, _h_providerMatches⟩
  have h_raw :
      (((MemBusChannel.pushed
        (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
          ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op :
      (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).mem_op =
        (eval (mainTable.environment mainRow) mainMsg).mem_op :=
    memBusMessage_mem_op_eq_of_eval_pushed_provider_msg_eq (h_msg := h_raw)
  rw [ZiskFv.AirsClean.MemAlignReadByte.eval_memBusMessageExpr] at h_provider_mem_op
  simp [h_main_mem_op] at h_provider_mem_op

/-- A Main memory-bus interaction at `mem_op = 3` cannot have been provided by `MemAlign`, whose
    message sets `mem_op := wr + 1` for a `wr` its own `Spec` pins boolean (`MemAlign/Spec.lean:49`).
    So its `mem_op` is `1` or `2`, never `3`. -/
theorem not_activeMainMemAlignProviderRowMatchSpec_of_main_mem_op_three
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 3) :
    ¬ ActiveMainMemAlignProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_memAlign
  rcases h_memAlign with
    ⟨providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, _h_providerTable, _h_providerInteraction,
      providerRow, _h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval, _h_providerMatches⟩
  -- The provider's own `Spec` pins `wr` boolean; bridge it to the `eval … rowInputVar` form.
  rw [h_providerComponent, ZiskFv.AirsClean.MemAlign.component_spec,
    component_rowInput_eq_eval_rowInputVar] at h_providerSpec
  have h_wr := h_providerSpec.1
  -- Balance forces the two messages equal, hence their `mem_op` fields.
  have h_raw :
      (((MemBusChannel.emitted
        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op :
      (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).mem_op =
        (eval (mainTable.environment mainRow) mainMsg).mem_op :=
    memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
  rw [ZiskFv.AirsClean.MemAlign.eval_memBusMessageExpr, h_main_mem_op] at h_provider_mem_op
  -- `wr + 1 = 3` gives `wr = 2`, contradicting booleanity.
  have h_wr_two :
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlign.component.rowInputVar).wr = 2 := by
    linear_combination h_provider_mem_op
  rw [h_wr_two] at h_wr
  exact absurd h_wr (by decide)

/-- A Main memory-bus interaction at `mem_op = 3` cannot have been provided by `MemAlignByte`, whose
    message sets `mem_op := 1 + is_write` for an `is_write` its own `Spec` bounds by `2 ^ 1`
    (`MemAlignByte/Spec.lean`, last conjunct). So its `mem_op` is `1` or `2`, never `3`. -/
theorem not_activeMainMemAlignByteProviderRowMatchSpec_of_main_mem_op_three
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 3) :
    ¬ ActiveMainMemAlignByteProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_mab
  rcases h_mab with
    ⟨providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, _h_providerTable, _h_providerInteraction,
      providerRow, _h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval, _h_providerMatches⟩
  rw [h_providerComponent, ZiskFv.AirsClean.MemAlignByte.component_spec,
    component_rowInput_eq_eval_rowInputVar] at h_providerSpec
  have h_isw := h_providerSpec.2.2.2.2.2.2.2
  have h_raw :
      (((MemBusChannel.pushed
        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op :
      (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).mem_op =
        (eval (mainTable.environment mainRow) mainMsg).mem_op :=
    memBusMessage_mem_op_eq_of_eval_pushed_provider_msg_eq (h_msg := h_raw)
  rw [ZiskFv.AirsClean.MemAlignByte.eval_memBusMessageExpr, h_main_mem_op] at h_provider_mem_op
  -- `1 + is_write = 3` gives `is_write = 2`, contradicting the `2 ^ 1` bound.
  have h_isw_two :
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar).is_write = 2 := by
    linear_combination h_provider_mem_op
  rw [h_isw_two] at h_isw
  exact absurd h_isw (by decide)

/-- A Main memory-bus interaction at `mem_op = 3` cannot have been provided by the mutable-Mem
    component on either of its two emission shapes: the primary message sets `mem_op := wr + 1` for a
    `wr` its `Spec` pins boolean (`Mem/Spec.lean:60`), and the dual message pins `mem_op` to the
    literal `1` (`Mem/Bridge.lean:102`). -/
theorem not_activeMainMutableMemProviderRowMatchSpec_of_main_mem_op_three
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 3) :
    ¬ ActiveMainMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_mem
  rcases h_mem with
    ⟨providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, _h_providerTable, _h_providerInteraction,
      providerRow, _h_providerRow, h_providerSpec, h_providerComponent, h_branch⟩
  rw [h_providerComponent] at h_providerSpec
  have h_rowSpec :=
    ZiskFv.AirsClean.Mem.spec_of_componentWithDualMemBus_spec _ h_providerSpec
  rw [component_rowInput_eq_eval_rowInputVar] at h_rowSpec
  rcases h_branch with ⟨h_providerEval, _⟩ | ⟨h_providerEval, _⟩
  · -- Primary emission: `mem_op = wr + 1`, and `wr` is boolean.
    have h_wr := h_rowSpec.2.2.2.2.1
    have h_raw :
        (((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Mem.memBusMessageExpr
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr, h_main_mem_op] at h_provider_mem_op
    have h_wr_two :
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 2 := by
      linear_combination h_provider_mem_op
    rw [h_wr_two] at h_wr
    exact absurd h_wr (by decide)
  · -- Dual emission: `mem_op` is the literal `1`.
    have h_raw :
        (((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr] at h_provider_mem_op
    simp [h_main_mem_op] at h_provider_mem_op

/-- **The register-partition classification.** For a Main memory-bus interaction at `mem_op = 3`,
    every memory-side provider is excluded, so the counterpart is one of the two register-side
    branches: another Main row's register pre-load push, or the `RegisterBoundary` boot / reload.

    This is the step that turns the register branch from something only ever *ruled out*
    (`BootSegmentMemorySeed.lean:942`) into something that can be walked forward: the counterpart of
    a register read is the previous access to that register, and the chain terminates at
    `RegisterBoundary.bootMessage`'s literal `(timestamp 0, value 0)`. -/
theorem activeMainRegisterProviderRowMatchSpec_of_main_mem_op_three
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 3)
    (h_match :
      ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as) :
    ActiveMainSelfMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainRegisterBoundaryProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  rcases activeMainMemProviderRowMatchSpec_mutable_or_nonmutable h_match with
    h_mutable | h_nonmutable
  · exact absurd h_mutable
      (not_activeMainMutableMemProviderRowMatchSpec_of_main_mem_op_three
        h_mainEval h_main_mem_op)
  rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases h_nonmutable with
    h_marb | h_mab | h_memAlign | h_main | h_regBoundary
  · exact absurd h_marb
      (not_activeMainMemAlignReadByteProviderRowMatchSpec_of_main_mem_op_three
        h_mainEval h_main_mem_op)
  · exact absurd h_mab
      (not_activeMainMemAlignByteProviderRowMatchSpec_of_main_mem_op_three
        h_mainEval h_main_mem_op)
  · exact absurd h_memAlign
      (not_activeMainMemAlignProviderRowMatchSpec_of_main_mem_op_three
        h_mainEval h_main_mem_op)
  · exact Or.inl h_main
  · exact Or.inr h_regBoundary

/-! ## Phase 5 — the PC arm

`h_pc_bridge` is the one `InputsAgree` field present in all 63 `Inputs_<op>` structures, and it does
not go through the MemBus at all: PC adjacency is a component `transition`, so this arm is
independent of the register-partition ordering question above.

The ZisK side needs no new premise. `AcceptedZiskTrace.transitions_hold` is a *field*
(`AcceptedZiskTrace.lean:126`), it unfolds to a per-table `Table.TransitionConstraints`
(`Clean/Air/FlatEnsemble.lean:216`), and Main's component transition is `pcHandshakeTransition`
(`Main/Circuit.lean:941`), which is `transitionBetween` on the evaluated predecessor and current
rows. -/

/-- Main's predecessor/current PC handshake holds at every row of the Main table, extracted from the
    accepted trace's `transitions_hold` certificate.

    Ordering-free and premise-free: this composes a field the trace already carries, exactly as the
    register work composes `channels_balanced`. -/
theorem main_transitionBetween_of_transitions_hold
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_transitions : witness.TransitionConstraints)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (index : Fin mainTable.length) :
    ZiskFv.AirsClean.Main.transitionBetween
      (Eval.eval (mainTable.previousEnvironment index)
        (varFromOffset (F := FGL) ZiskFv.AirsClean.Main.MainRowWithRom 0))
      (Eval.eval (mainTable.environmentAt index)
        (varFromOffset (F := FGL) ZiskFv.AirsClean.Main.MainRowWithRom 0)) := by
  have h_table := h_transitions mainTable h_mainTable index
  rw [h_mainComponent] at h_table
  exact h_table

end ZiskFv.AirsClean.FullEnsemble
