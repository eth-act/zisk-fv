# Task: Phase 3 pilot — Clean `Spec` becomes the interface for BinaryAdd; delete its bridge

## Situation

**The tree delivered with this prompt is the current source of truth.** If it arrived as a
tarball attached to a continue prompt, replace your entire working tree with the tarball's
contents before doing anything else — your prior local repository state (including your own
earlier commits) is outdated and must not be trusted.

Sandbox limitations, pre-acknowledged: no git branch history; no `zisk` submodule, so trust
check 13 cannot run for you — defer exactly that check, every other gate is mandatory. Do
not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`, `flake.lock`, or
`ZiskFv/Audit.lean`.

## Context

Phase 2 is closed at its natural T0 boundary (your blocker analysis was accepted: the
remaining wrapper shrinks fold into Phase 4's `OpEnvelope` restructure). This turn begins
Phase 3 of `docs/refactor/FINAL-PLAN.md` (§5.1, roadmap 3.1–3.2): make the Clean
`GeneralFormalCircuit.Spec` the interface the equivalence layer consumes, retiring the
legacy `Airs/` record model family by family. Pilot family: **BinaryAdd** (full Clean
component exists under `ZiskFv/AirsClean/BinaryAdd/{Spec,Row,Constraints,Circuit,
Soundness,Bridge}.lean`; `Valid_BinaryAdd` is currently consumed by 16 files;
`Bridge.lean` provides `rowAt` / `soundness_of_valid`).

Standing decision from your own T4 analysis: do NOT change `OpEnvelope` constructor
arities this turn — that exhaustive-pattern restructure is Phase 4's, done once.

## Numbered work order

1. **Q2 constraint-agreement spot-check — do this FIRST.** Verify that the
   `Valid_BinaryAdd` constraint predicates exactly mirror the Clean BinaryAdd component's
   constraints (`AirsClean/BinaryAdd/Constraints.lean` vs the `Airs/` record model).
   Produce a per-constraint correspondence table in your summary. If ANY divergence is
   found: stop this family immediately and report the divergence precisely — it is a
   potential soundness gap and must never be papered over by choosing either side.
2. **Generic row-view lemma.** One lemma (or a small lemma family stated once, not
   per-consumer copies) establishing that `Valid_BinaryAdd` facts about row `r` are
   equivalent to the Clean `Spec` of the row projection (`rowAt`-view), in the direction(s)
   consumers actually need. Derivation side: `AcceptedZiskTrace` already yields the Clean
   `Spec` per table row (`spec_holds` / `witness_spec_of_constraints`), so the Clean side
   is the supply and the record side is the demand being retired.
3. **Rewire the BinaryAdd-family consumers.** Move the BinaryAdd-specific consumers of
   `Valid_BinaryAdd` (EquivCore bridge lemmas, construction/StepStrong feeds, the
   `add_via_binaryadd` route) onto the Clean `Spec` interface. You MAY restate EquivCore
   hypotheses from record-model facts to Clean-`Spec` facts — that is this phase's point —
   but the Sail-space `execute = bus_effect` conclusion shapes and the promise discipline
   must be preserved, and no hypothesis may be weakened or added.
4. **Delete `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`** once it is consumer-free. If a
   consumer genuinely cannot be rewired this turn, blocker-note it precisely and leave the
   bridge in place — never delete with live consumers.
5. **Delete `Valid_BinaryAdd`** (its definition and its `Airs/` constraint predicates) if
   and only if consumer-free after items 3–4; otherwise report the remaining consumer
   list verbatim.
6. **Final sweep.** Report `Valid_BinaryAdd` consumer count before/after and bridge
   status; `trust/generated/` byte-for-byte unchanged; full `lake build`,
   `trust/scripts/check-all.sh` (minus check 13), `trust/scripts/check-all-semantic.sh`
   all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified blocker
note. A clean build or a committed chunk is a checkpoint, not a stop condition: after
finishing an item, proceed immediately to the next. Committing and reporting with items
silently unattempted is a failed turn. If an item is blocked, skip it, document the precise
blocker (file, theorem, error), and continue with the next item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched and passing.
- Item 1's outcome gates items 3–5: no bridge or record-model deletion is sound unless the
  constraint sets agree exactly.
- Every rewired hypothesis must be **proved** from the Clean `Spec`/accepted-trace supply —
  never weakened, never moved to a broader premise, never replaced by a new caller
  obligation. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`. No file under `trust/generated/` may change; no baseline created.
- No `OpEnvelope` constructor-arity changes.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` with: the per-item status table for
items 1–6; the Q2 per-constraint correspondence table; the `Valid_BinaryAdd` consumer
count before/after with the remaining-consumer list if nonzero; and exact gate results.
