# Completeness is a co-equal axis — not a footnote

**Date:** 2026-06-22. **Trigger:** user correction mid-session — *"the
completeness effort is brushed off but it's just as important as the soundness
effort."*

## What changed
The v2 curriculum (NOTES lesson plan 0002–0005) was soundness-only: opcode
end-to-end, the new construction/trace-export top, the RHS circuit stack, then
build/CI. Completeness got a single line in NOTES ("don't drop the 2nd axis")
and **no dedicated lesson**. That under-weights it and contradicts the mission.

## Why it's co-equal (validated against `main @ e731db56`)
`ZiskFv/Completeness/` is a full second arc, ~6k lines, with its own structure:
- `Rv.Interface` (`Completeness/Rv.lean:23`) abstracts ZisK's
  decode/lower/materialize surface.
- Its predicate algebra: `LoweringComplete`, `RowMaterializationComplete`,
  `OpcodeCoverageComplete`, `SailExecutableContainedIn`, `SoundnessInputComplete`,
  `knownGap` (`Rv.lean:35–150`).
- A ladder of per-family "shape completeness" theorems climbs to the headline
  `root_completeness (iface) (h_sail_subset) (h_supported) (h_lower) (h_rows)
  (h_opcode) (h_soundness) : Rv64imCompletenessWithSoundnessInputAvoidingKnownDecodeBugs`
  (`Completeness/Rv64im.lean:5919`).

## The key architectural distinction
The two arcs have **different shapes**:
- **Soundness** ("accept ⇒ Sail agrees") is fully in-tree; `lake build` proves it.
- **Completeness** ("every Sail-executable RV64IM word is covered by ZisK's
  decode/lower/materialize/soundness-input surface, modulo recorded gaps + known
  bugs") is **interface-mediated**: `Rv64im.lean:7–13` states the concrete
  generated predicates live OUTSIDE the repo in the reproducible extraction
  workspace; the `iface` hypotheses are discharged by the **Aeneas harness** (the
  ~1h31m CI bottleneck, see memory `project_ci_bottleneck`).
- The two arcs **do not cross-reference in code** (NOTES architecture-delta note).
  That decoupling is itself a re-architecture finding to examine, not assume-good.

## Consequence for the curriculum
Rebalanced lesson plan (NOTES.md updated): completeness gets dedicated lessons
co-equal with soundness, and the one-opcode lesson traces BOTH axes. Mission
success criteria rewritten to name both axes as co-equals.
