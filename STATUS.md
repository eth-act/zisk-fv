Stream: #111 — discharge `aeneasBridgeTrust` from the real Aeneas extraction.
Branch: aeneas-bridge-111 (off origin/main @ 6ffb31e5).
Plan: docs/ai/plan/PLAN_AENEAS_BRIDGE_111.md   Issue: eth-act/zisk-fv#111

Goal: replace the *asserted* Main-row decode pins (the `mainRowProvenance_of_pins`
fabrication in the live root_soundness → stepStrong_* path) with proof terms about the
real extracted lowerer in trust/aeneas/ProductionM2.lean, IN the main lake build, without
adding trust. Keep Lean 4.28.0.

Route: keep Lean 4.28.0; pin aeneas back to a2fcf1923d (last v4.28.0-rc1 commit) — import
is GO per spike. Trust R1 (sound, no native_decide); R2 only as CODEOWNER fallback. Scope:
static row-mode pins first; value pins (Phase 3) deferrable; dynamic conjuncts out of scope.

Status: SETUP done. Worktree + build/ symlinks + cache get done; tracking files written.
Next: Phase 0a (verify flake aeneas/charon structure), then Phase 0b (bump pin + regen).

Checklist:
- [x] Setup: worktree, build/ symlinks, lake exe cache get, tracking files.
- [ ] Phase 0a: verify flake aeneas/charon structure (transitive charon? current/target pin).
- [ ] Phase 0b: bump flake.lock aeneas ac9f1bc5 → a2fcf1923d; regenerate ProductionM2.
- [ ] Phase 0c: vendor aeneas-lean; hand-edit manifest (NEVER lake update); require aeneas + probe; lake build green.
- [ ] Phase 0d: update boundary gates; verify #eval LUI pins + no sorryAx on probe.
- [ ] Phase 1 (MAKE-OR-BREAK): LUI sound-discharge tractability (progress/scalar_tac, no native_decide).
      Spike 2026-06-19 found plain decide/rfl/simp = NO-GO. DECISION POINT here.
- [ ] Phase 1: AeneasBridgeTrust/Extraction.lean + LUI pilot.
- [ ] Phase 2: uniform static pins across 63 ops.
- [ ] Wiring swap + verification + residual docs.

Key reference: spike memory
~/.claude/projects/-home-cody-zisk-fv/memory/project_aeneas_discharge_blocked.md
— full reproducible Phase-0 recipe + the R1 NO-GO-via-cheap-tactics warning.

Env note: build/ subdirs symlinked to /home/cody/zisk-fv/build (shared, never committed).
