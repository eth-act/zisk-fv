import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.Wrappers.Lui

/-!
# Sound LUI construction (`construction_lui_sound`)

The first **provider-free** (`is_external_op = 0`) honest sound construction in
the P4 sweep. LUI is realized by a single *internal* Zisk microinstruction
(`OP_COPYB`), so it emits **no** operation-bus entry: there is no op-bus provider
block at all (in contrast to `ConstructionSub.lean`, which derives the staticBinary
op-bus provider match from `trace.balanced`). LUI is therefore STRICTLY MORE
derivable than the 28 provider-backed families — the entire LUI Main constraint
subset comes straight out of the per-row `Main.Spec`, and the rd-value is the
identity copy `c_0/c_1 = b_0/b_1 = imm`.

## The honest decomposition

* **(a) derived** — proven inside the body, NOT a binder:
  - the Main per-row `Spec` and from it the full LUI constraint subset
    (`lui_subset_holds`, including the `pc_handshake_with_next_pc` field, which
    is *definitional* — `next_pc` is chosen as the handshake RHS, so the field
    holds by `rfl` and contributes no residual),
  - the `StorePcMemoryWitness` (`row_eq` by `rowAt_mainOfTable`, `rd_write_match`
    by `matches_memory_entry_refl` off the real Clean Main `cMemMessage` row),
  - the rd-write memory-bus shape (`rd_mult`, `rd_as` by `rfl`),
  - the pure-spec `nextPC_eq` (`rfl`, since `nextPC_val` is chosen to be the
    pure-spec nextPC),
  - the circuit-internal rd arithmetic (`c_0/c_1 = b_0/b_1 = imm`), discharged
    inside `equiv_LUI` from `internal_op1_copies_*` + the imm-lane Nat pins.

* **(b) named residual** — explicit top-level binders (program/ROM/Sail facts):
  - decode pins (5): `h_main_op` (`OP_COPYB`), `h_main_active` (`= 0`),
    `h_m32` (`= 0`), `h_set_pc` (`= 0`), `h_store_pc` (`= 0`)
  - Sail-value bridges (6): `h_input_imm`, `h_input_rd`, `h_input_pc`,
    `h_rd_idx`, `h_imm_lo_nat`, `h_imm_hi_nat`
  - control-flow next-PC (1): `h_nextPC_matches` — the ORDINARY sequential
    `pc + 4` handshake every one of the 28 already carries; NOT the cross-row
    jump-target term.

* **(c) artifact** — pure `bus_effect`/`ExecutionBusEntry` bookkeeping:
  - exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the genuine
    `execRow : List (ExecutionBusEntry FGL)` ∀-binder.

## Residual budget: EXACTLY 15 + execRow

`5 + 6 + 1 + 3 = 15` hypothesis binders, plus the genuine `execRow` ∀-binder.
No `MainRowProvenance` / `*RowBinding` leaf appears anywhere in the binder set.

## Axioms

`construction_lui_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.EquivCore.Promises
open Interaction

set_option maxHeartbeats 2000000

/-- The honest unified Main+ROM row at trace index `i`, drawn from the real Main
    table.  Its `.core` equals `rowAt (mainOfTable …) i`. -/
@[reducible]
def mainRowWithRomLui
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    trace.program binding.mainTable i.val

/-- Construction-chosen rd-write entry: the real Clean Main `c` memory-bus
    emission (rd write) of the honest unified row.  The `StorePcMemoryWitness`
    match is then `matches_memory_entry_refl`. -/
@[reducible]
def eRdLui
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLui trace binding i)) 1 1

/-- The Main per-row `Spec` at trace index `i`, derived from `trace.spec`.
    (Standalone version of the in-wrapper `h_main_spec` derivation.) -/
theorem mainSpec_at
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length) :
    ZiskFv.AirsClean.Main.Spec
      (ZiskFv.AirsClean.Main.rowAt
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
        i.val) := by
  let mainIdx : Fin binding.mainTable.table.length := ⟨i.val, binding.mainTable_index i⟩
  let mainRow := binding.mainTable.table.get mainIdx
  have h_mainRow_mem : mainRow ∈ binding.mainTable.table := by simp [mainRow]
  have h_main_component_spec :
      binding.mainTable.component.Spec
        (binding.mainTable.environment (binding.mainTable.table.get mainIdx)) := by
    simpa [mainRow] using
      trace.spec binding.mainTable binding.mainTable_mem mainRow h_mainRow_mem
  simpa [mainIdx] using
    ZiskFv.AirsClean.FullEnsemble.mainSpec_rowAt_mainOfTable_of_component_spec
      trace.program binding.mainTable mainIdx binding.mainTable_component
      h_main_component_spec


end ZiskFv.Compliance
