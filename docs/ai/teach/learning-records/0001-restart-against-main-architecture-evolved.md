# Restart against latest main — architecture evolved a new trace-level top

Workspace regenerated from scratch against `main @ e731db56` (2026-06-22), after
`git fetch` + fast-forward (local main was 9 commits behind). v1 of the course
(built against older main `236449c9`) is archived on the `review` branch. Mission
unchanged: understand the architecture to re-architect it (proofs first, then
build/CI). User redoes from Lesson 1.

**Prior knowledge (carried):** expert in Lean 4, FV, RISC-V/zkVM; primary author
of the repo; completed v1 lessons 1–3 (territory map, ADD end-to-end, RHS stack).
Don't re-teach fundamentals.

**The architecture delta that drove the restart (validated against source):**
The recent commits (#106/#110/#112/#121) added a **new top** to the proof tower
that did NOT exist in v1:
- `ZiskFv/Compliance/Construction*.lean` — 20 modules of per-opcode
  `construction_<op>_sound` theorems that **construct** the inputs.
- `ZiskFv/Soundness.lean:21` —
  `root_soundness (trace : AcceptedTrace) (binding)
  (rowData : ∀ i, StrongRowConstructionData …) (h_known_bugs) : ∀ i,
  StepComplianceStrong …`. Given an accepted trace, it builds the `OpEnvelope`
  per row INSIDE — **no caller-supplied envelope**. Covers all 63 archetypes via
  three routes (env-constructed 22 ALU arms; direct-lift 27 control/U/load/store/
  unsigned-M; defect-narrowed 7 signed-M + FENCE). Still **0 project axioms**
  (`baseline-strong-export-closure.txt` empty).

**Why it matters:** this directly discharges the gap v1 Lesson 02 flagged — the
old `zisk_riscv_compliant_program_bus` (`Compliance.lean:95`, still present)
*assumes* an `OpEnvelope`; the new top *derives* it from a trace. The headline is
shifting "assume → construct." Residual moved to: an accepted trace + per-row
`StrongRowConstructionData` classification + `h_known_bugs`.

**Process facts (re-recorded):** README.md and CLAUDE.md are STALE — both still
cite only the old global theorem and are silent on the new top. Validate against
the tree, not the prose. RTK truncates long idents in ripgrep output — use Read.

**Implication for the curriculum:** Lesson 03 should now be a dedicated dive on
the construction + trace-level export layer (the biggest, most mission-relevant
change), ahead of or alongside the RHS-stack lesson.
