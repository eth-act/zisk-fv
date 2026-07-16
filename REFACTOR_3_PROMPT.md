# Task: Phase 2.3 + 2.4 — shrink the wrapper parameter surfaces across ALL families

## Situation

**The tree delivered with this prompt is the current source of truth.** If it arrived as a
tarball attached to a continue prompt, replace your entire working tree with the tarball's
contents before doing anything else — your prior local repository state (including your own
earlier commits) is outdated and must not be trusted.

Sandbox limitations, pre-acknowledged: the snapshot has no git branch history and no `zisk`
submodule, so trust check 13 (`check-aeneas-production-boundary`) cannot run for you — the
operator runs it locally. Defer exactly that check; every other gate is mandatory for you.
Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`, `flake.lock`, or
`ZiskFv/Audit.lean` (its `#guard_msgs` golden tests are the tripwire for root drift; if
they fail, your change is wrong, not the tests).

## Done vs. remaining

Done at the ensemble seam (`ZiskFv/Compliance/AcceptedZiskTrace/DerivedRowFacts.lean`):
`opProviderRowFacts` (generic 4-branch provider classification),
`staticBinarySubProviderRowFacts`, `staticBinaryLogicProviderRowFacts`,
`registerWriteLanes`, `mainRowPins`/`mainRowPinsOfEq`. `StepStrongAluArith.lean` already
consumes them for SUB and the six AND/OR/XOR paths.

Remaining — this turn: Phase 2.3+2.4 of `docs/refactor/FINAL-PLAN.md`. The per-opcode
wrapper lemmas (`ZiskFv/Compliance/Wrappers/<Op>.lean`, e.g. `equiv_ADD` in
`Wrappers/Add.lean`) still take the seam-derivable binders as caller-supplied parameters:
`providerTable`, `providerRow`, `h_provider_row`, `h_component`, `h_table_spec`,
`h_match`, `h_lane_rd`, and `pins : MainRowPins …`. Those are now proved once at the seam,
so the wrappers' parameter surfaces must shrink, family by family, until callers supply
only genuine per-opcode data (inputs, decode facts, promises) — never provider/lane/pin
facts an accepted trace already yields.

## Design latitude (choose, then document)

You may either (a) have each family's wrapper consume the corresponding
`DerivedRowFacts` conclusion as a single hypothesis (the ∃-package), or (b) restate the
wrapper at trace level (`trace : AcceptedZiskTrace n`, `i : Fin n` + decode facts) and
derive the package internally. Pick per family for minimal diff, state the choice in your
summary. Two things are NOT in scope: the `EquivCore/<Op>.lean` core theorems (they are
the trace-agnostic Sail-space seam — do not change their statements; Phase 3 owns that
layer), and the legacy `m : Valid_Main` parameter (Phase 3 removes the record model —
leave it).

## Numbered work order

For each family below: (i) add any missing family-level provider specialization to
`DerivedRowFacts.lean` (same style as the SUB/logic ones — generic balance from
`opProviderRowFacts`, only impossibility eliminations local); (ii) shrink every wrapper
lemma in the family; (iii) update its `StepStrong*` / `Dispatch/` callers; (iv) build
green, commit, proceed to the next item. Acceptance per item: every listed binder removed
from each wrapper in the family (or a precise blocker note naming file, theorem, and the
failing derivation), zero new caller-supplied hypotheses, before/after parameter counts
recorded per theorem.

1. RTYPE family (`Dispatch/RTYPE.lean` scope: add/sub/logic/compare register forms).
2. ITYPE family (immediate forms).
3. Shift family (add the BinaryExtension `shiftStaticLookupComponent` specialization).
4. ADD_RTYPEW family (add the BinaryAdd specialization).
5. DIVU family (add the ArithMul specialization).
6. Remaining family (`Dispatch/Remaining.lean` — the M-extension and other ops routed
   there; reuse the ArithMul specialization where applicable).
7. Misc family.
8. NoMemOrSimple family.
9. Branch family — wrapper layer only; branches' EquivCore nextPC seam must stay exactly
   as is.
10. LDSD family — loads/stores touch the memory timeline; any binder genuinely not
    seam-derivable gets a precise blocker note and stays. Do not force it.
11. Cleanup: delete `main_request_*` balance-rebuild lemmas that became consumer-free
    (verify zero consumers first; keep any that still have one).
12. Final sweep: per-family before/after parameter-count table in your summary;
    `trust/generated/` byte-for-byte unchanged; full `lake build`,
    `trust/scripts/check-all.sh` (minus check 13), `trust/scripts/check-all-semantic.sh`
    all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified blocker
note. A clean build or a committed chunk is a checkpoint, not a stop condition: after
finishing an item, proceed immediately to the next. Committing and reporting with items
silently unattempted is a failed turn. If an item is blocked, skip it, document the precise
blocker (file, theorem, error), and continue with the next item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- Everything is T0: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched and passing.
- Every removed binder must be **proved** from accepted-trace facts via the seam — never
  moved into a broader premise, a strengthened validator, or a new caller-supplied
  hypothesis elsewhere. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`,
  `partial`, `@[implemented_by]`. No file under `trust/generated/` may change, and no
  baseline may be created.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` with: a per-item status table
(done / blocked+why / not reached) for items 1–12; the per-theorem before/after parameter
counts; which design (a)/(b) each family used; and the exact gate results.
