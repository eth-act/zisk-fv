import Source458DomainComparison.Old18
import ZiskFv.Compliance.AcceptedZiskTrace

/-!
# Historical accepted eighteen-entry domain at a015aaa7

The original fields and selected-table/replay-row definitions, with the exact
historical Mem component, are retained only for comparative proof. No numeric
restriction is reconstructed from the corrected domain. This is not a new
public Root premise or a replacement production accepted-trace certificate.
-/

namespace ZiskFv.Compliance.Legacy457

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
        (ZiskFv.AirsClean.FullEnsemble.Legacy457.fullRv64imEnsemble programLength program).ensemble) :
    Prop :=
  ∃ table ∈ witness.allTables,
    table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus ∧
      0 < table.table.length

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
      (ZiskFv.AirsClean.FullEnsemble.Legacy457.fullRv64imEnsemble programLength program).ensemble
  constraints_hold : witness.Constraints
  channels_balanced : witness.BalancedChannels
  /-- Guarded concrete mutable-Mem table for traces whose witness has mutable-Mem rows.

      This is table/source selection only: it records which witness table is the mutable Mem AIR,
      that it is part of the witness, that it has the mutable-Mem component, and that it is nonempty.
      It does not carry generated Mem facts or read-value agreement. -/
  mem_replay_table : ∀ (_h : MutableMemPresent witness),
    { table : Air.Flat.Table FGL //
      table ∈ witness.allTables ∧
        table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus ∧
          0 < table.table.length }
  /-- Structural source-correlation certificate for the guarded Mem AIR source:
      every mutable-Mem table in the accepted witness is the selected source
      table. This is table identity only, not read-value agreement. It is kept
      separate from the source package so the remaining accepted-trace residue is
      visible per factor. -/
  mem_replay_source_covers : ∀ (h : MutableMemPresent witness),
    ∀ table ∈ witness.allTables,
      table.component = ZiskFv.AirsClean.Mem.Legacy457.componentWithDualMemBus →
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

/-- The accepted Mem replay rows selected when the accepted witness has mutable-Mem rows. -/
def AcceptedZiskTrace.memReplayRows {n : Nat} (trace : AcceptedZiskTrace n)
    (h_present : MutableMemPresent trace.witness) :
    List (Interaction.MemoryBusEntry FGL) :=
  ZiskFv.AirsClean.FullEnsemble.activeMemReplayRowsOfTable
    (trace.memReplayTable h_present)


end ZiskFv.Compliance.Legacy457
