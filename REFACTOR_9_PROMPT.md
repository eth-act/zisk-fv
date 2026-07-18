# Task: Phase 3 — finish the Binary family (the last static-lookup family)

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: the BinaryAdd and BinaryExtension families are fully on
the Clean spine with their legacy surfaces deleted).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

Your T7 turn deleted BinaryExtension using the pattern now proven twice: migrate the
shared consumers group-by-group, relocate retained semantics into the Clean family
(`PackedCorrect`/`Ranges` moves, not rewrites), retire the bridge as a `ConsumerFacts`
module of direct canonical-row projections, then delete. Your own
`REFACTOR_8_REPORT.md` contains the declaration-level consumer map for Binary: a
3,848-line bridge (`EquivCore/Bridge/Binary.lean`) plus 59 legacy-path references across
compare, logic, arithmetic-input, and shared balance facts. This turn applies the
BinaryExtension recipe to Binary — the largest static-lookup family and the last one.

## Numbered work order

1. **Refresh the consumer map** from the current tree (your T7 migration may have moved
   some references); commit it to `REFACTOR_9_REPORT.md`.
2. **Migrate the shared balance/static-table consumers** of the legacy Binary model onto
   canonical Clean rows / `AirsClean/Binary/Interface.lean`.
3. **Migrate `EquivCore/Bridge/Binary.lean` group-by-group** (compare, logic,
   arithmetic-input, remaining), committing per green group. Retained semantic proofs
   move into the Clean family (`AirsClean/Binary/PackedCorrect.lean`, `Ranges.lean`,
   `Trace.lean` as needed) as moves, not rewrites. Restate record-model hypotheses to
   Clean-`Spec` facts; Sail-space conclusions and `OpEnvelope` arities untouched; zero
   new caller obligations.
4. **Retire the bridge**: replace `AirsClean/Binary/Bridge.lean` (and what remains of
   `EquivCore/Bridge/Binary.lean`) with a `ConsumerFacts.lean` of direct canonical-row
   projections, mirroring BinaryExtension's.
5. **Delete the Binary legacy surfaces** — `Airs/Binary/Binary.lean`,
   `Airs/Binary/BinaryPackedCorrect.lean`, and any other legacy Binary model files —
   when the reference count is 0; root import updates in the same commit.
6. **Final sweep.** Reference counts before/after; deleted-file list; net line delta;
   `trust/generated/` byte-unchanged; full `lake build`, `trust/scripts/check-all.sh`
   (minus check 13), `trust/scripts/check-all-semantic.sh` all green.

If the full migration cannot finish, the prioritization rule stands: a smaller consumer
group fully migrated and committed beats a broad half-migration — but this family is the
turn's only target, so spend the entire budget on it.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- The T6 Binary Q2 audit gates the deletion; if the deep migration exposes any
  constraint it missed, stop and report precisely.
- Every restated hypothesis proved from the Clean supply — never weakened, broadened, or
  pushed to callers. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`,
  `partial`, `@[implemented_by]`. No `trust/generated/` change; no baseline; no
  `OpEnvelope` arity change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_9_REPORT.md`):
per-item status for 1–6; the refreshed consumer map; reference counts before/after;
deleted files; net line delta; exact gate results.
