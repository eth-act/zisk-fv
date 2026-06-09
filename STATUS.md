# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP_CLOSURE.md`

Current focus: revised closeout plan has been merged into branch
`memory-trust-gap` in `/home/cody/zisk-fv/.worktrees/memory-trust-gap`. The
large branch still contains useful memory replay/local-load infrastructure, but
the primary theorem still exposes the hard memory premise through active
replay/state-selection source evidence. PR #63's axiom-weakening change is
has been folded in by cherry-picking its merged commit and resolving
load-memory conflicts toward this branch's stronger `MemoryTraceAgreement`
boundary.

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
- The merged `axiom-weakening` worktree/branch was cleaned up after PR #63
  merged. Its false-probe and byte-agreement witness are now being carried into
  this branch's semantic gate; `LoadByteAgreement` is a named byte-fact
  projection derived from `MemoryTraceAgreement`, not a weaker replacement for
  the replay burden.
- Verification after the PR #63 merge-in passed: `lake build`,
  `trust/scripts/check-all-semantic.sh`, `trust/scripts/check-all.sh`, and
  `nix run .#test`. Regenerated anti-laundering ledgers record pre-existing
  branch shrinkage in SLLW/SRAW/SRLW and wrapper burdens.

Prior plan note:
- The older `PLAN_MEMORY_TRUST_GAP.md` records the long implementation history.
  The new closure plan is the active plan for deciding what to keep, what to
  prove next, and when to replace the current memory axiom with either a proof
  or a narrower explicit timeline boundary.
