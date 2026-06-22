Stream: Architecture Clarification (legibility refactor of the two public theorems
+ their support tree). Plan: docs/ai/plan/PLAN_ARCH_CLARIFICATION.md.

Base: worktree `.worktrees/arch-clarify`, branch `arch-clarify`, on
`origin/issue-114-extraction` = main + PR #121 (8834dec1). Rebase onto origin/main
when #121 merges. Warm `.lake` + symlinked `build/` reused from the #121 worktree.

Goal: one entry point (`ZiskFv/Top.lean`), parallel honest names
(`zisk_riscv_soundness` / `zisk_riscv_completeness`), fuse the cosmetic Equivalence
layer, present hypotheses as named conditional assumptions (stop echoing them in
conclusions), make the 54/63 scope + trust residuals build-visible. Clarity only —
discharges nothing, does NOT merge the two theorems (no Lean edge between them).

Progress: S0 baseline green · S1 front door `Top.lean` (fcf15bed) · S2 honesty
docstrings (fcf15bed) · S3 completeness renames done (rv64im_completeness →
zisk_riscv_completeness; SoundnessInput → RowInput; field ziskRowInputAvailable +
INFORMAL-edge docstring). All builds + gate L1/L2 green; completeness confirmed
gate-free (no baseline regen). Next: S4 low-risk semantic renames (PackedBitVec→
Bits, Trusted→RowShape, NoKnownDefect→OutsideKnownDefectRegion, OpEnvelope fields)
— first step needing caller-burden ledger regen.

Checklist + gate-coupling map: see the plan file.
