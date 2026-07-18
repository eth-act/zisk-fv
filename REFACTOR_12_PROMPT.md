# Task: Phase 3 — projection layer over the completed Arith mirrors; finish migration and deletion

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: your T10 turn landed verbatim — `mainComplete` for both
Arith families in `ZiskFv/AirsClean/ArithCompleteConstraints.lean`, the `inv_sum_all_bs`
row column, and the updated Q2 tables).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

Your T10 blocker analysis was accepted: extending the live circuit's conjunction breaks
positional destructurings in consumers (`ArithMul/ConsumerFacts.lean`,
`Compliance/SharedBundles.lean` were your first verified failures). The fix you proposed
is this turn's work order: a NAMED projection layer over `mainComplete`, so consumers
take named facts instead of destructuring conjunction positions — the same
named-projection pattern the whole refactor uses (`DerivedRowFacts`,
`Binary/ConsumerFacts`). Then the blocked migration and deletions from your committed
`REFACTOR_10_REPORT.md` map proceed. Known blast-radius files for the circuit swap:
`AirsClean/Arith{Mul,Div}/ConsumerFacts.lean`, `AirsClean/ArithTableProjections.lean`,
`Compliance/SharedBundles.lean`, `Compliance/ConstructionMulhu.lean`,
`AirsClean/FullEnsemble/ArithBalance.lean` and the `FullEnsemble/Balance/*` layer.

## Numbered work order

1. **Named projection layer — ALREADY DONE; verify and use, do not redo.** The tree
   you received contains the completed layer: named spec bundles (`ArithMul.ModeSpec`;
   `ArithDiv.{ModeSpec, BoundarySpec, InverseSumSpec, ScopeSpec, C46Spec, WModeSpec,
   CompleteLocalSpec}`) and PROVEN projection theorems
   `complete_local_specs_of_const_soundness` in both families' `ConsumerFacts.lean`.
   Consume these named facts everywhere; no consumer should ever destructure
   `mainComplete`'s raw conjunction. If a consumer needs a projection variant (e.g.
   general `input_var` instead of `constVar`), add it beside the existing theorem in
   the same style.
2. **Swap the live supply to `mainComplete`** wherever the ensemble/static-table/
   construction layer currently uses the incomplete circuit. Witness/row builders must
   genuinely satisfy the added constraints — e.g. `inv_sum_all_bs` must be the actual
   inverse of the divisor-chunk sum on live division rows (the current `arithDivRowOf`
   default of `0` is only valid where the div flags are all zero). If a builder cannot
   honestly supply a constraint, that is a blocker to report, never a constraint to
   drop.
3. **Migrate the consumers** per your committed `REFACTOR_10_REPORT.md` map (mul, div,
   carry-chain/bus-res, balance/table, exports/wrappers/constructions), committing per
   green group, consuming the item-1 named projections. Retained semantics move into
   the Clean families as moves, not rewrites. Restate record-model hypotheses to
   Clean-`Spec`-side facts; Sail-space conclusions and `OpEnvelope` arities untouched;
   zero new caller obligations.
4. **Delete the legacy surfaces** — `Airs/Arith/Mul.lean`, `Div.lean`,
   `CarryChain.lean`, `CarryChainCompleteness.lean`, `BusRes1.lean` — as each reaches
   reference count 0; import updates in the same commit.
5. **Final sweep.** Reference counts before/after; deleted-file list; net line delta;
   `trust/generated/` byte-unchanged; full `lake build`, `trust/scripts/check-all.sh`
   (minus check 13), `trust/scripts/check-all-semantic.sh` all green.

Prioritization: ArithMul end-to-end (projections → swap → migrate → delete `Mul.lean` +
its satellites) beats both families half-done. ArithDiv's builder work (real
`inv_sum_all_bs` witnesses, boundary constraints on live rows) is the deepest — do it
after ArithMul lands.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- The constraint set is FROZEN at T10's audited list: no new constraints beyond the
  cited generated mirrors, and none of them dropped or weakened. The projection layer
  only names and routes what `mainComplete` already asserts.
- **The DIV/REM defect boundary survives unchanged**: `ArithDivDynamicWitnessShape`,
  `h_known_bugs` exclusions, and `Compliance/Defects.lean` semantics stay intact; any
  retargeting of legacy references there must preserve statement meaning exactly. If
  boundary-constraint routing would alter what the defect gate excludes, stop and
  report.
- Every restated hypothesis proved from the Clean supply — never weakened, broadened,
  or pushed to callers. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`,
  `partial`, `@[implemented_by]`. No `trust/generated/` change; no baseline; no
  `OpEnvelope` arity change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_12_REPORT.md`):
per-item status for 1–5; the projection-lemma list; the builder-witness changes; per
family reference counts before/after; deleted files; net line delta; exact gate results.
