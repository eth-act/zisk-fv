Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is
gone; load byte agreement now comes from `MemoryTimelineEvidence`, but
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge`, `MemTableGeneratedRangeFacts`, and
`MemTableGeneratedFixedColumnFacts` expose the row/list-position, range, and
fixed-column facts; `FullWitnessMemTableGeneratedRowsBridge` is still the
concrete full-ensemble bridge obligation.
Current sub-gap: discharge the explicit row-0 same-address boundary premise.
Same-address predecessor iteration over positive indices is factored; row 0
needs either first-segment evidence forcing `addr_changes = 1` or a
continuation-aware initial memory.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  and load wrappers consume `MemoryTimelineEvidence`.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  obligation `ActiveMemReplayRowsOfTablePrimaryReadPrefixSound`.
- Latest completed slice factors same-address predecessor replay:
  selected previous rows handle write/read plus replay-neutral dual reads;
  inactive previous rows carry without emitting active replay entries; and the
  combined one-step lemma abstracts that split.
- Current uncommitted slice lifts zero-preload through same-pointer preload
  witnesses, packages split-prefix predecessor carry, and reduces selected
  primary-read prefix soundness to one row-0 same-address boundary input.

Verification: Lean LSP diagnostics are clean for
`ZiskFv.ZiskCircuit.MemTrace` and
`ZiskFv.AirsClean.FullEnsemble.Balance`; both touched target builds pass.
Full `lake build`, both trust gates, and `nix run .#test` pass for the current
uncommitted slice.

Next step: prove or surface the row-0 segment-boundary input, then wire the
reduced primary-read prefix theorem into the active table prefix-read theorem.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
