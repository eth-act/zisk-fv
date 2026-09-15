Stream: Fanout Closeout, Stream 3 / #249 in-repo certificate burn-down.
Coordination checkout: detached HEAD at `b35df9b9`.
Completed #245 and CI-hotfix worktrees are being retired; the next stream will use a fresh
isolated worktree because the base checkout has unrelated changes.
Objective: `/home/cody/.codex/attachments/5970eab3-c151-4565-a67e-587d3a6d1bdd/pasted-text-1.txt`.
Plan: `docs/ai/plan/PLAN_FANOUT_CLOSEOUT.md`.

Current state:
- Broad closeout objective remains active; do not mark complete. Execute one stream at a time.
- #221 Mem-prefix Phase 0 preflight (2026-07-10): #220, #225, and #245 are closed, but #226,
  #242, #243, and #249 remain open. `PLAN_MEM_PREFIX_221.md` stays queued; do not create its
  worktree or begin proof work until fanout closeout lands unless the owner explicitly supersedes
  that sequencing.
- PR #250 (heterogeneous multi-row `root_soundness`) merged at `fbe7abcb`; #220 is closed.
- PRs #236, #244, #246, #247, #248, and #250 are landed on current `origin/main`.
- #118 is already natively blocked by #117; attempting to add the edge returned GitHub's duplicate
  relationship validation. `scripts/update_issue_deps_graph.py --update` reported #173 already up to
  date when run with the authenticated `GITHUB_TOKEN`.
- PR #252 merged at `af1c6f41`; #245 is closed. It split accepted executed-step count from
  committed ROM length without weakening Main's per-row lookup or the `Decode_*` surface.
- #249 is active: derive and delete the Main step-index certificate, hand-pinned within-row
  prev-step chains, and Mem replay range certificates through the in-repo range/fixed-column route.
- #249 audit checkpoint (2026-07-10): static lookups can directly constrain Main/Mem rows, but
  `mem_replay_segment_ranges` is over `ProverData` sidecar values with no modeled source correlation.
  The active worktree awaits an owner decision to add a source-correlated sidecar/component model or
  explicitly retain that field under a signed re-scope; do not add an unlinked range table.
- Root worktree has unrelated dirty state from prior streams: `ZiskFv/AirsClean/RangeTables.lean`,
  `docs/ai/PROJECTS.md`, `trust/proof-tree/index.html`, plus untracked `notes` and `notes.md`.
  Do not revert or absorb that work without explicitly re-entering that stream.

Next step:
- Resolve the #249 segment-sidecar modeling decision, then continue Stream 3 in
  `.worktrees/issue-249-certificate-burndown`.
