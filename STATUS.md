Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is
gone; load byte agreement now comes from `MemoryTimelineEvidence`, but
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge`, `MemTableGeneratedRangeFacts`, and
`MemTableGeneratedFixedColumnFacts` expose the row/list-position, range, and
fixed-column facts; `FullWitnessMemTableGeneratedRowsBridge` is still the
concrete full-ensemble bridge obligation.
Current sub-gap: integrate the first-segment row-0 closure. Row 0 is now closed
for segments with `segment.is_first_segment = 1`; concrete full-witness
integration must either expose that selector or use a continuation-aware
initial memory carrying `previous_segment_*`.

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
- Latest committed slice (`6e52f0d7`) lifts zero-preload through same-pointer
  preload witnesses, packages split-prefix predecessor carry, and reduces
  selected primary-read prefix soundness to one row-0 same-address boundary
  input.
- Current uncommitted slice projects `mem.pil:377` to show first-segment row 0
  must have `addr_changes = 1`, closing the same-address boundary for first
  segments and deriving active-table prefix-read soundness under an explicit
  `segment.is_first_segment = 1` input. It also constructs
  `AcceptedMemoryReplayEvidence` for first-segment tables whose accepted row
  list is the active table projection, filling `prefixReadSound` from these
  concrete Mem-table facts.
- Full-witness inspection found no existing source for
  `segment.is_first_segment = 1`; current full-ensemble code selects the Mem
  table but leaves generated-row, range, fixed-column, and segment-selector
  facts as bridge obligations.

Verification: Lean LSP diagnostics are clean for `ZiskFv.Airs.Mem`;
`ZiskFv.Airs.Mem` and `ZiskFv.AirsClean.FullEnsemble.Balance` target builds
pass. New first-segment theorems/constructor have no `sorryAx` in axiom scans
(they carry the existing Clean component axiom class). The combined checkpoint
`nix run .#test` passes for the current uncommitted slice, including full
`lake build`, both trust gates, flake repro, cargo tests, and extraction tests.

Next step: inspect the concrete full-witness Mem segment evidence to decide
whether to expose `segment.is_first_segment = 1` or add the continuation-memory
initial-state theorem.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
