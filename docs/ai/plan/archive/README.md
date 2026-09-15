# Archived plans — DONE or superseded

Historical record only. Active plans live one level up in `docs/ai/plan/`; the live
index is `../../PROJECTS.md`. (`ENDGAME_ROADMAP.md` was retired into this directory.) Each file here is either **DONE** (the work merged) or
**SUPERSEDED** (replaced by a current plan). Do not execute anything here.

| File | Status | Notes |
|---|---|---|
| `PLAN_ENDGAME_P1.md` | **DONE** | P1 foundations — merged 2026-06-13 (#79/#80/#89; bucket audit #83). |
| `PLAN_ENDGAME_P3.md` | SUPERSEDED | early P3 plan → superseded by `PLAN_ENDGAME_P3_CLOSEOUT.md`. |
| `PLAN_ENDGAME_P3_PR5_REWORK.md` | SUPERSEDED | P3 PR5 rework → folded into the closeout. |
| `PLAN_ENDGAME_P3_CLOSEOUT.md` | **DONE** | P3 memory *reshape* closed — merged 2026-06-13 (`4456a9e5`). Reshape only; the memory-trust reduction is P4/#76. |
| `PLAN_ENDGAME_P4_SPINE.md` | **DONE** | P4 construction spine (infra + §2 template + §4 invariants + first sound family) — merged via #98/#99. |
| `PLAN_ENDGAME_P4_SWEEP.md` | **DONE** | the 28-family sweep (RV64I ALU/shift/W-ALU) — merged via #99/#102. (+LUI/AUIPC via #106 → 30/63.) |
| `RESEARCH_PR94_CLOSEOUT.md` | historical | the #94/#97 "laundering" closeout research that motivated the SPINE rewrite. |
| `PLAN_ENDGAME_P4_MEMORY.superseded-2026-06-16.md` | SUPERSEDED | the spike-framed #76 plan → replaced 2026-06-17 by `../PLAN_ENDGAME_P4_MEMORY.md` (route Z, store-driven Fold B). |
| `PLAN_ENDGAME_XCAP.superseded-2026-06-16.md` | SUPERSEDED | the `addVm`/`SoundVmEnsemble` XCAP plan — route is a **dead end**; replaced 2026-06-17 by `../PLAN_ENDGAME_XCAP.md` (the `addChannel` route). |
| `PLAN_CLEAN_COMPLETENESS.md` | **DONE** | Clean completeness demotion stream. |
| `PLAN_CLEAN_COMPLETENESS_PROOFS.md` | **DONE** | Clean completeness proofs — all 5 wave PRs (#69–#73) merged 2026-06-12. |
| `PLAN_RV64IM_COMPLETENESS_RESTACK.md` | **DONE** | RV64IM acceptance-completeness restack; `ZiskFv.Completeness.skeletal_root_completeness` landed (the plan's original `Rv64im.rv64im_completeness` was later renamed). |

## Retired from the tracked tree by PR #367 (2026-09-03)

PR #367 deleted `docs/ai/` and `simplification-suggestions.md` from git. The tracked
copies are recoverable with `git show e6f6868b:<path>`; these are the working copies,
kept here so nothing depends on that recovery.

| File | Status | Notes |
|---|---|---|
| `PROJECTS.md` | historical | the project index as of `08db1645`, plus the uncommitted **Build Warnings** section (#361/#362/#363) that the PR-#367 checkout discarded. Six of its seven plan citations were already dead. |
| `PHASE2_PER_OP_SPEC.md` | **DONE** | already archived; the tracked copy was byte-identical. |
| `PLAN_AENEAS_BRIDGE_111.md` | **DONE** | already archived; the tracked copy was byte-identical. |
| `lean4lean-scouting.md` | historical | lean4lean scouting for open #78. Also relocated to that issue as a dated snapshot. |
| `simplification-suggestions.md` | historical | May 2026 ranked refactor backlog; its "Shipped" section is all merged. |
| `find-unused-README.md` | SUPERSEDED | `tools/find-unused/`'s README. Superseded by `lake exe trust-gate find-unused`. |
| `aeneas-proof-reference/` | SUPERSEDED | 12 rc2-typechecked reference proof bodies for #111, since ported into `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/`. |

`PLAN_RV64IM_COMPLETENESS_RESTACK.md` was refreshed from the tracked copy: the
archived version predated the `rv64im_completeness` -> `skeletal_root_completeness`
rename and named the old endpoint in two places.
