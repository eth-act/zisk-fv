import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.FullEnsemble.Balance.RowsBridgeFacts
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections

/-!
# Accepted trace

An `AcceptedZiskTrace` is one fully-populated, verifier-accepted run of the RV64IM
circuit for a fixed `program` of `length` instructions.

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

/-- Accepted committed trace for the full RV64IM Clean ensemble.

    `numInstructions` is a **structure parameter** (not a field) so that
    `root_soundness` can share one instruction count across the ZisK and Sail
    sides (issue #144). The `AcceptedZiskTrace.numInstructions` accessor below
    recovers it, so the many `trace.numInstructions` uses keep working
    unchanged. -/
structure AcceptedZiskTrace (numInstructions : Nat) where
  program : ZiskFv.AirsClean.ZiskInstructionRom.Program numInstructions
  witness :
    Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble numInstructions program).ensemble
  constraints_hold : witness.Constraints
  channels_balanced : witness.BalancedChannels
  /-- Guarded concrete mutable-Mem table for nonempty traces.

      This is table/source selection only: it records which witness table is the mutable Mem AIR,
      that it is part of the witness, that it has the mutable-Mem component, and that it is nonempty.
      It does not carry generated Mem facts or read-value agreement. -/
  mem_replay_table : ∀ (_h : 0 < numInstructions),
    { table : Air.Flat.Table FGL //
      table ∈ witness.allTables ∧
        table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus ∧
          0 < table.table.length }
  /-- Guarded raw Mem generated source sidecar for the selected mutable-Mem table.

      This is not a read-soundness predicate and does not carry the accepted replay bridge directly:
      together with `mem_replay_table`, it supplies the sidecar columns plus split generated
      constraint and range facts from which the typed Mem AIR source, replay bridge, and table-order
      replay soundness are derived downstream. The deterministic `SEGMENT_L1` fixed-column shape is
      derived by the bridge rather than carried here. Empty traces do not need or generally have a
      nonempty Mem replay table, so the field is guarded. -/
  mem_replay_source : ∀ (h : 0 < numInstructions),
    ZiskFv.AirsClean.FullEnsemble.MemTableGeneratedRawSourceSidecar
      (mem_replay_table h).1
  /-- Structural source-correlation certificate for the guarded Mem AIR source:
      every mutable-Mem table in the accepted witness is the selected source
      table. This is table identity only, not read-value agreement. It is kept
      separate from the source package so the remaining accepted-trace residue is
      visible per factor. -/
  mem_replay_source_covers : ∀ (h : 0 < numInstructions),
    ∀ table ∈ witness.allTables,
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        table = (mem_replay_table h).1
  /-- The Main AIR's cross-row PC-handshake transition constraint (`main.pil:409-410`) holds on every
      consecutive Main-table row pair. This polynomial transition CANNOT be expressed by the single-row
      Clean `Air.Flat` per-row `Constraints` (which is exactly why it was dropped from the per-row Spec);
      it is declared on the Main component via `Air.Flat.Component.transition` and carried here as a
      verifier-checked certificate, in the same epistemic class as `main_height` — a PIL-faithful,
      constructible accepted-trace obligation. It consolidates the per-opcode cross-world
      `h_nextPC_matches` promises into one in-circuit constraint. See `trust/trusted-base.md`. -/
  transitions_hold : witness.TransitionConstraints
  /-- The Main execution table covers every instruction: any witness table with
      the Main component has a row for each instruction. This is the one genuine
      row-count assumption — the witness pins table count and component, but never
      row count — specialized to the derived `mainTable` by `mainTable_index`. -/
  main_height : ∀ table ∈ witness.allTables,
      table.component =
          ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus numInstructions program →
        ∀ i : Fin numInstructions, i.val < table.table.length
  /-- The Main execution table's `SEGMENT_L1` fixed column is `[1,0,0,...]`
      (`main.pil:19`): the first row is a segment boundary, every later row is
      within-segment. Carried here as a fixed-column constructibility certificate
      in the same `main_height` epistemic class — PIL-faithful and constructible
      (a real ZisK Main witness genuinely carries this deterministic column). Its
      within-segment fact `segment_l1 (i + 1) = 0` is exactly what the Main
      cross-row PC-handshake transition (`mainTransition_to_next_pc`) consumes to
      derive the per-opcode next-PC relation, so it lives ONCE here (uniform with
      `main_height` / `transitions_hold`) rather than as a per-arm `h_fixed`
      binder. Formulated over `witness.allTables` — like `main_height` — because
      the derived `mainTable` is defined after this struct;
      `AcceptedZiskTrace.mainTable_fixed` specializes it to that table. -/
  segment_l1_fixed : ∀ table ∈ witness.allTables,
      table.component =
          ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus numInstructions program →
        (0 < table.table.length →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable program table).segment_l1 0 = 1) ∧
        (∀ idx : Fin table.table.length, 0 < idx.val →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable program table).segment_l1 idx.val = 0)

/-- Recover the instruction count from a parameterized `AcceptedZiskTrace`.
    `numInstructions` is now a structure parameter rather than a field; this
    accessor keeps the many value-level `trace.numInstructions` projections
    working. Type-level uses inside the heavy provider-match lemmas instead
    reference the structure parameter directly (the autobound `numInstructions`
    / `n`), so this accessor never has to unfold into the heavy
    `componentWithRomMemAndOpBus …` subterms during `whnf` (issue #144). -/
def AcceptedZiskTrace.numInstructions {n : Nat} (_ : AcceptedZiskTrace n) : Nat := n

/-- The guarded mutable-Mem table selected for a nonempty accepted trace. -/
def AcceptedZiskTrace.memReplayTable {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions) : Air.Flat.Table FGL :=
  (trace.mem_replay_table h_nonempty).1

/-- The guarded Mem AIR source selected for a nonempty accepted trace, rebuilt
from the split table-selection and raw sidecar fields. -/
def AcceptedZiskTrace.memReplaySource {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions) :
    ZiskFv.AirsClean.FullEnsemble.FullWitnessMemAirSource trace.witness :=
  { table := trace.memReplayTable h_nonempty
    table_mem := (trace.mem_replay_table h_nonempty).2.1
    component := (trace.mem_replay_table h_nonempty).2.2.1
    source := (trace.mem_replay_source h_nonempty).toAirSource }

/-- The accepted Mem replay rows selected for a nonempty accepted trace. -/
def AcceptedZiskTrace.memReplayRows {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions) :
    List (Interaction.MemoryBusEntry FGL) :=
  (trace.memReplaySource h_nonempty).rows

/-- The accepted Mem replay bridge selected for a nonempty accepted trace. -/
def AcceptedZiskTrace.memReplayBridge {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions) :
    ZiskFv.AirsClean.FullEnsemble.FullWitnessMemReplayBridge
      trace.witness (trace.memReplayRows h_nonempty) :=
  (trace.memReplaySource h_nonempty).replayBridge
    (trace.mem_replay_table h_nonempty).2.2.2

end ZiskFv.Compliance
