Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is gone;
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge`, `MemTableGeneratedRangeFacts`, and
`MemTableGeneratedFixedColumnFacts` expose the local inputs; the concrete
full-witness bridge still has to provide them.
Current sub-gap: integrate row-0 closure into the concrete full-witness path.
Row 0 is closed for `segment.is_first_segment = 1`, and the continuation
row-0 same-address read now has a local `previous_segment_*` seeded-memory
base theorem. Remaining integration must expose the selector or thread the
continuation initial memory through the table induction with preservation facts.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  and load wrappers consume `MemoryTimelineEvidence`.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  selected-primary-read obligation.
- Commit `6e52f0d7` lifts zero-preload through same-pointer
  preload witnesses, packages split-prefix predecessor carry, and reduces
  selected primary-read prefix soundness to one row-0 same-address boundary
  input.
- Latest committed slice (`15775597`) projects `mem.pil:377` to show first-segment row 0
  must have `addr_changes = 1`, closing the same-address boundary for first
  segments and deriving active-table prefix-read soundness under an explicit
  `segment.is_first_segment = 1` input. It also constructs
  `AcceptedMemoryReplayEvidence` for first-segment tables whose accepted row
  list is the active table projection, filling `prefixReadSound` from these
  concrete Mem-table facts.
- Full-witness inspection found no existing source for
  `segment.is_first_segment = 1`; generated-row/range/fixed/selector facts
  remain explicit bridge obligations.
- Current uncommitted slice adds boundary carry to `previous_segment_*`, defines
  continuation seed memory, proves row-0 same-address read agreement, and
  generalizes predecessor/table induction over arbitrary initial memory.

Verification: Lean LSP diagnostics are clean for `ZiskFv.Airs.Mem`; target
builds for `ZiskFv.Airs.Mem` and `ZiskFv.AirsClean.FullEnsemble.Balance` pass.
New continuation declarations have no `sorryAx` in axiom scans. The full
checkpoint gate `nix run .#test` passes for the current uncommitted slice.

Next step: prove the seeded-memory address-change base, including disjointness
or overwrite behavior for the previous-segment seed.

Context: Phase A is committed at `0c222595`; old `.worktrees/memory-trust-gap`
is salvage reference only until Phase D cleanup.
