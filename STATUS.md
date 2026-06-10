Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is
gone; load byte agreement now comes from `MemoryTimelineEvidence`, but
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge`, `MemTableGeneratedRangeFacts`, and
`MemTableGeneratedFixedColumnFacts` expose the row/list-position, range, and
fixed-column facts; `FullWitnessMemTableGeneratedRowsBridge` is still the
concrete full-ensemble bridge obligation.
Current sub-gap: iterate the same-address one-step predecessor lemma over
arbitrary prior prefixes. The address-change/first-read case is closed under
the explicit fixed-column facts.

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

Verification: Lean LSP diagnostics are clean for
`ZiskFv.AirsClean.FullEnsemble.Balance`; target build, full lake build, both
trust gates, and `nix run .#test` pass for the current slice.

Next step: prove the same-address selected-read prefix case by iterating the
one-step predecessor lemma backward through same-address rows until a selected
write/read or the address-change zero-preload base case.

Context: Phase A is committed at `0c222595`. The old
`.worktrees/memory-trust-gap` branch remains only as salvage reference until
Phase D cleanup.
