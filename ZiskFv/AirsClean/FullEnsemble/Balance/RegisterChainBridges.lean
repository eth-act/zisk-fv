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

end ZiskFv.AirsClean.FullEnsemble
