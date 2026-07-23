import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.FullEnsemble.Balance.RowsBridgeFacts
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections

/-!
# Accepted trace

An `AcceptedZiskTrace` is one fully-populated, verifier-accepted run of the RV64IM
circuit for a fixed committed `program` and an executed trace. Execution can revisit
committed instructions, so its step count need not equal the ROM length.

The circuit is an **Air.Flat ensemble**: a collection of AIRs (the Main table
plus the binary / arithmetic / memory / lookup tables) wired together by shared
*channels* — the operation bus and the lookup / permutation buses.
`(fullRv64imEnsemble length program).ensemble` is just that collection of column
layouts and channels; it holds no data of its own.

The `witness` is the ensemble *filled in* with concrete Goldilocks values: every
AIR's grid of rows. The remaining two fields are the proofs that make the
witness "accepted" — exactly what a real ZisK proof certifies:

* `constraints_hold : witness.Constraints` — every per-row algebraic gate of every
  table holds (the polynomial constraint equations are satisfied).
* `channels_balanced : witness.BalancedChannels` — despite the name, **not a boolean**: it
  is the *proposition* that every cross-table channel balances, i.e. for each bus
  the multiset of messages sent equals the multiset received (the logUp /
  permutation argument). This is what stops a table from fabricating or dropping
  a bus message, gluing the otherwise-independent AIRs into one sound machine.

The per-AIR *spec* is not an assumed field: it is derived from these two by
`AcceptedZiskTrace.spec_holds` (in `AcceptedZiskTrace/Spec.lean`).

It is the single object the soundness development quantifies over; everything
downstream (`SailTrace`, the provider-match wrappers, the per-op
constructions) is built relative to one of these.
-/

namespace ZiskFv.Compliance

/-- Objective guard for mutable-Mem replay evidence.

    The accepted-trace Mem replay package is meaningful exactly when the concrete witness contains
    a nonempty mutable-Mem table. This guard is determined by `witness.allTables`; memory-less traces
    discharge it by proving their mutable-Mem table is empty, while memory-carrying traces provide
    the same bridge package #115 already required. -/
def MutableMemPresent
    {programLength : Nat}
    {program : ZiskFv.AirsClean.ZiskInstructionRom.Program programLength}
    (witness :
      Air.Flat.EnsembleWitness
        (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble programLength program).ensemble) :
    Prop :=
  ∃ table ∈ witness.allTables,
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus ∧
      0 < table.table.length

/-- Derived fixed-column facts for Main's `main_step` ROM companion column.

    PIL defines `STEP = main_segment * N + SEGMENT_STEP` (`main.pil:90`), with
    `SEGMENT_STEP` the deterministic row counter. Clean materializes
    `main_step` as component-owned indexed fixed data; the canonical table
    schema and its intrinsic domain bound derive these row-index and no-wrap
    facts in `mainStepIndexFixedFacts_of_component_fixedColumns`. -/
structure MainStepIndexFixedFacts
    (numInstructions : Nat)
    (programLength : Nat)
    (program : ZiskFv.AirsClean.ZiskInstructionRom.Program programLength)
    (table : Air.Flat.Table FGL) : Prop where
  main_step_eq_index : ∀ i : Fin numInstructions,
    (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero program table i.val).rom.main_step =
      (i.val : FGL)
  timestamp_bound : ∀ i : Fin numInstructions, 4 * i.val + 3 < GL_prime
  load_timestamp_toNat : ∀ i : Fin numInstructions,
    (2 +
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero program table i.val).rom.main_step *
        4).toNat =
      2 + 4 * i.val
  store_timestamp_toNat : ∀ i : Fin numInstructions,
    (3 +
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero program table i.val).rom.main_step *
        4).toNat =
      3 + 4 * i.val

/-- Accepted committed trace for the full RV64IM Clean ensemble.

    `numInstructions` is a **structure parameter** (not a field): it counts
    executed steps and therefore remains shared with the Sail trace and
    `root_soundness`. `programLength` is a dependent field because the committed
    ROM can be longer than the executed trace, while loops can execute more steps
    than the committed ROM has entries.
    The `AcceptedZiskTrace.numInstructions` accessor below preserves existing
    execution-indexed uses. -/
structure AcceptedZiskTrace (numInstructions : Nat) where
  programLength : Nat
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program programLength
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble programLength program).ensemble
  constraints_hold : witness.Constraints
  channels_balanced : witness.BalancedChannels
  /-- Guarded concrete mutable-Mem table for traces whose witness has mutable-Mem rows.

      This is table/source selection only: it records which witness table is the mutable Mem AIR,
      that it is part of the witness, that it has the mutable-Mem component, and that it is nonempty.
      It does not carry generated Mem facts or read-value agreement. -/
  mem_replay_table : ∀ (_h : MutableMemPresent witness),
    { table : Air.Flat.Table FGL //
      table ∈ witness.allTables ∧
        table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus ∧
          0 < table.table.length }
  /-- Structural source-correlation certificate for the guarded Mem AIR source:
      every mutable-Mem table in the accepted witness is the selected source
      table. This is table identity only, not read-value agreement. It is kept
      separate from the source package so the remaining accepted-trace residue is
      visible per factor. -/
  mem_replay_source_covers : ∀ (h : MutableMemPresent witness),
    ∀ table ∈ witness.allTables,
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        table = (mem_replay_table h).1
  /-- Component-owned predecessor/current transitions hold on every table row.
      This includes Main's PC handshake (`main.pil:409-410`) and MemAlign's
      gated predecessor `delta_addr` plus `down_to_up` register continuity
      (`mem_align.pil:116-117,142`). These polynomial relations are declared
      by their components' intrinsic D1 predicates and are verifier-checked,
      constructible accepted-trace obligations—not caller assumptions. -/
  transitions_hold : witness.TransitionConstraints
  /-- MemAlign's D3 successor/current relations hold on every effective row:
      h998 `DELTA_PC = pc' - pc` and the `up_to_down` register continuity
      constraints (`mem_align.pil:113-118,139-143`), including the intrinsic
      final-row to row-zero wrap. This is a verifier-checked certificate over
      component-owned predicates, never a caller assumption. -/
  cyclic_successor_transitions_hold : witness.CyclicSuccessorTransitionConstraints
  /-- The Main execution table covers every instruction: any witness table with
      the Main component has a row for each instruction. This is the one genuine
      row-count assumption — the witness pins table count and component, but never
      row count — specialized to the derived `mainTable` by `mainTable_index`. -/
  main_height : ∀ table ∈ witness.allTables,
      table.component =
          ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus programLength program →
        ∀ i : Fin numInstructions, i.val < table.table.length
/-- Recover the instruction count from a parameterized `AcceptedZiskTrace`.
    `numInstructions` is now a structure parameter rather than a field; this
    accessor keeps the many value-level `trace.numInstructions` projections
    working. Type-level uses inside the heavy provider-match lemmas instead
    reference the structure parameter directly (the autobound `numInstructions`
    / `n`), so this accessor never has to unfold into the heavy
    `componentWithRomMemAndOpBus …` subterms during `whnf` (issue #144). -/
def AcceptedZiskTrace.numInstructions {n : Nat} (_ : AcceptedZiskTrace n) : Nat := n

/-- The guarded mutable-Mem table selected when the accepted witness has mutable-Mem rows. -/
def AcceptedZiskTrace.memReplayTable {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) : Air.Flat.Table FGL :=
  (trace.mem_replay_table h_present).1

/-- The selected mutable-Mem table's row range facts are derived from the
    accepted live component constraints. The static lookups mirror
    `mem.pil:384-385,397`; no accepted-trace range certificate remains. -/
theorem AcceptedZiskTrace.memReplayRowRanges {n : Nat}
    (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    ZiskFv.AirsClean.FullEnsemble.MemTableGeneratedRangeFacts
      (trace.memReplayTable h_present)
      (ZiskFv.AirsClean.FullEnsemble.memOfTableData
        (trace.memReplayTable h_present)) := by
  apply ZiskFv.AirsClean.FullEnsemble.memTableGeneratedRangeFacts_of_component_constraints_canonical
  · exact (trace.mem_replay_table h_present).2.2.1
  · exact trace.constraints_hold (trace.memReplayTable h_present)
      (trace.mem_replay_table h_present).2.1

/-- The selected mutable-Mem table's generated constraints are derived from
    its live row constraints and right-indexed transition. The source is the
    same materialized table data and component-owned fixed schema consumed by
    the verifier; no accepted-trace generated-constraint certificate remains. -/
theorem AcceptedZiskTrace.memReplayGeneratedConstraintFacts {n : Nat}
    (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    ZiskFv.AirsClean.FullEnsemble.MemTableGeneratedConstraintFacts
      (trace.memReplayTable h_present)
      (ZiskFv.AirsClean.FullEnsemble.memOfTableData
        (trace.memReplayTable h_present))
      (ZiskFv.AirsClean.FullEnsemble.memSegmentOfTableData
        (trace.memReplayTable h_present))
      (ZiskFv.AirsClean.FullEnsemble.memPermutationOfTableData
        (trace.memReplayTable h_present)) := by
  apply ZiskFv.AirsClean.FullEnsemble.memTableGeneratedConstraintFacts_of_component_constraints_transitions
  · exact (trace.mem_replay_table h_present).2.2.1
  · exact trace.constraints_hold (trace.memReplayTable h_present)
      (trace.mem_replay_table h_present).2.1
  · exact trace.transitions_hold (trace.memReplayTable h_present)
      (trace.mem_replay_table h_present).2.1

/-- The accepted Mem replay rows selected when the accepted witness has mutable-Mem rows. -/
def AcceptedZiskTrace.memReplayRows {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    List (Interaction.MemoryBusEntry FGL) :=
  ZiskFv.AirsClean.FullEnsemble.activeMemReplayRowsOfTable
    (trace.memReplayTable h_present)

end ZiskFv.Compliance
