Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B Mem-table replay closure. `LoadPromises.mem_read` is gone;
`AcceptedMemoryReplayEvidence.prefixReadSound` is still an assumed field.

Blocking: prove selected primary-read prefix soundness from concrete Mem table
facts. `MemTableGeneratedRowsBridge`, `MemTableGeneratedRangeFacts`,
`MemTableGeneratedFixedColumnFacts`, and a 29-bit previous-segment address range
expose the local inputs; the concrete full-witness bridge still has to provide
them.
Current sub-gap: integrate the first/continuation segment table theorem into the
concrete full-witness path and expose the needed segment selector/range facts.

Latest proof surface:
- Phase C boundary swap is done: the residual Sail timeline is visible once,
  and load wrappers consume `MemoryTimelineEvidence`.
- Phase B has local active-row chronology, adjacent same-address timestamp
  order, write/read carry, read-preserving rows, replay append lemmas, row/table
  fold composition, zero preload, generated row specs, and the named remaining
  selected-primary-read obligation.
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
- Latest committed slice (`3773a889`) adds boundary carry to
  `previous_segment_*`, defines continuation seed memory, proves row-0
  same-address read agreement, and generalizes predecessor/table induction over
  arbitrary initial memory.
- Latest completed slice lifts address-change reads through the seeded memory,
  proves the previous-segment seed is byte-disjoint from address-change reads
  under `segment.previous_segment_addr.val < 2^29`, and constructs continuation
  table prefix soundness plus `AcceptedMemoryReplayEvidence` from that range.

Verification: `lake build ZiskFv.Airs.Mem` and
`lake build ZiskFv.AirsClean.FullEnsemble.Balance` pass. New continuation
declarations have no `sorryAx`; Balance LSP is stale on the new AIR import, but
the compiler target and `lean_run_code` import see it. Full `nix run .#test`
passes for this range-closure slice.

Next step: expose/prove `segment.previous_segment_addr.val < 2^29` from the
PIL/extractor bridge, then choose the first/continuation accepted replay
constructor in the concrete full-witness path.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
