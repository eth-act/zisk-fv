# OpenVM `Circuit F ExtF C` retirement — baseline snapshot

Captured at commit `0f7aad9` (branch `clean-full-phase-3-binaryadd`,
tag `phase-6-leanzk-drop-clean-full`), at Phase 0 entry.

Used as the audit baseline for the OpenVM Circuit retirement plan
(`/home/cody/.claude/plans/ok-i-will-let-humble-reddy.md`). Each
phase's exit commits its baseline deltas; reviewers diff against this
file.

## Numerical state

| Metric | Value |
|---|---|
| Total axioms (`baseline-axioms.txt`) | 104 |
| Shrinkage floor (`trust/.shrinkage-floor`) | 104 |
| `lake build` jobs | 8614 |
| Files importing `ZiskFv.Circuit` | 56 (in `ZiskFv/` + `build/extraction/Extraction/`) |
| `Circuit.*` accessor calls (all methods) | 1475 |
| — `Circuit.main` | 1532 (project-wide grep earlier; ZiskFv-only ≈ 1473 + handful in defs) |
| — `Circuit.preprocessed` | 2 (Main `segment_l1` line 103, MemAlign line 135) |
| — `Circuit.{buses,challenge,exposed,permutation,public_values}` | 0 — dead code |
| `Circuit.{last_row,isFirstRow,isLastRow,isTransitionRow}` | only in `ZiskFv/Circuit.lean` itself |
| `[Circuit FGL FGL C]` declaration sites | 33 across ZiskFv/ |
| `Valid_<AIR>` records | 10 (BinaryAdd, Main, Mem, MemAlign, MemAlignByte, MemAlignReadByte, Binary, BinaryExtension, ArithMul, ArithDiv) |
| `_def` constraint fields across all records | 244 |
| `_def` proof-site references | 321 total |
| Clean Component ports complete | 1 (BinaryAdd) |
| Clean Component ports skeletal | 8 (Mem, MemAlignReadByte, MemAlignByte, MemAlign, Binary, BinaryExtension, ArithMul, ArithDiv) |
| `Air.Flat.Component` PoC | works (see `ZiskFv/AirsClean/BinaryAdd/`) |

## Phase 0 spike outcome

- Lookup-channel API is **usable**. `Clean.Circuit.Lookup` + `Clean.Circuit.LookupCircuit`
  + `Clean.Circuit.Provable` + `Clean.Circuit.Basic` compose without
  collisions when imported narrowly.
- Known caveat: `Clean.Air.FlatComponent` umbrella pulls
  `Clean.Utils.Misc` which collides with `Batteries.Data.Fin.Fold`'s
  `Fin.foldl_eq_foldl_finRange`. Per-AIR ports must use narrow imports
  (precedent: `ZiskFv/AirsClean/BinaryAdd/Constraints.lean`).
- A6/A7/A8 lookup-channel path is **viable**; no axiom-fallback needed
  upfront.

## Per-AIR algebraic gap (Phase A scope)

For each AIR, the gap between the skeleton port and the full algebraic
Component:

| AIR | Skeleton has | Need to add |
|---|---|---|
| Mem | 6 boolean Spec clauses + Bridge | Cross-row adjacency clauses; Constraints.lean |
| MemAlignReadByte | 1 algebraic clause sketch | Complete linear-recombination Spec; Constraints.lean |
| MemAlignByte | 5-clause Spec (partial) | Full 5-byte staging algebra; Constraints.lean |
| MemAlign | Boolean skeleton (6 selectors) | 25 F-typed clauses + register chain; Constraints.lean; possibly Air.Flat.Table |
| Binary | 5 boolean Spec clauses | 25+ ALU clauses, carry chain; Constraints.lean; BinaryTable lookup |
| BinaryExtension | 3 boolean Spec clauses | Extension relation; Constraints.lean; BinaryExtensionTable lookup |
| ArithMul | 9 boolean Spec clauses | 4-limb mul-relation carry chain; Constraints.lean; ArithTable lookup |
| ArithDiv | 9 boolean Spec clauses | 4-limb div-relation + signed cases; Constraints.lean; ArithTable lookup |
| Main (Phase B) | NOT STARTED | Full Component port + cross-row PC handshake adjacency |

## Reference template

`ZiskFv/AirsClean/BinaryAdd/Soundness.lean` — 229 LOC, the per-AIR
algebraic Soundness reference. Every Phase A port's Soundness.lean
mirrors this structure:
- Parameter list: row + Assumptions hypotheses
- Body: `refine ⟨?_, …⟩` per Spec clause; each goal proved via
  `linear_combination` against the constraint hypotheses
- No axioms; all `Field FGL` algebra
