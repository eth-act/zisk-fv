# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP_CLOSURE.md`

Current focus: revised closeout plan has been merged into branch
`memory-trust-gap` in `/home/cody/zisk-fv/.worktrees/memory-trust-gap`. The
large branch still contains useful memory replay/local-load infrastructure, but
the primary theorem still exposes the hard memory premise through active
replay/state-selection source evidence.

Blocking: no local compile blocker known. The real soundness blockers remain
active table-local Mem replay order facts, active prefix-read soundness,
selected envelope Mem-row occurrence, and selected prefix-state equality from
actual accepted execution data.

Next step: stop adding compatibility wrappers. Prove one canonical
`MemoryTraceAgreement` theorem for the selected load from raw accepted
execution data, or introduce a narrower explicit memory-timeline trust boundary
if the selected Sail prefix timeline is not currently available.

Branch-state note:
- Latest committed implementation slice before this plan was
  `e1f8c952 Expose active envelope-row memory source`.
- `trust/scripts/check-all.sh` was already not clean in this worktree because
  broader caller-burden/hypothesis ledgers had shrunk versus baseline and
  Aeneas production extraction artifacts were missing/untracked.
- Latest branch-size audit was `origin/main...HEAD` at 67 files,
  +21,366/-769: roughly +13,044 compliance boundary/wrapper lines, +4,098
  AIR/Mem/full-ensemble lines, +1,351 load replay consumer lines, +2,809
  docs/trust/status lines, and only +63 net extractor lines.

Prior plan note:
- The older `PLAN_MEMORY_TRUST_GAP.md` records the long implementation history.
  The new closure plan is the active plan for deciding what to keep, what to
  prove next, and when to replace the current memory axiom with either a proof
  or a narrower explicit timeline boundary.
