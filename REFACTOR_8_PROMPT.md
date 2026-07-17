# Task: Phase 3 roll, part 2 — migrate the shared Binary-family machinery; unlock the deletions

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: the BinaryAdd pilot deletion and your five T6 family
Interfaces + Q2 audits are landed and verified).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.

Housekeeping: your repository has accumulated committed submission tarballs
(`refactor-*.tar.gz` at the root). `git rm` any such files in your first commit; never
commit an attached tarball again.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

Your T6 blocker analysis was accepted: the Binary and BinaryExtension deletions are gated
on their SHARED consumers — the balance/static-table layer and the `EquivCore/Bridge`
machinery — not on per-opcode surfaces (already migrated in Phase 2). This turn migrates
that shared machinery onto the Clean interfaces so the prepared deletions unlock. The
MemAlign trio and the Arith*/Mem/Main families stay out of scope (data-memory slice
comes later).

## Numbered work order

1. **Map the surviving consumers.** For `Airs/Binary/*` (legacy model + packed
   correctness) and `Airs/BinaryExtension/*`: produce the exact consumer list (file +
   declaration) grouped into (a) `EquivCore/Bridge/Binary.lean` /
   `EquivCore/Bridge/BinaryExtension.lean`, (b) the `AirsClean/FullEnsemble/Balance/*`
   and `BinaryFamily/Balance` layer, (c) constructions/dispatch, (d) anything else.
   Commit the map into your run report before migrating.
2. **Migrate group (b)** — the balance/static-table layer — onto the Clean row
   projections and `Interface` APIs. These files reason about table membership and
   emissions; the Clean `Table`/`Spec` side already carries that data.
3. **Migrate group (a)** — the `EquivCore/Bridge` machinery. This is the large one
   (`Bridge/Binary.lean` alone is ~190K). Work theorem-family by theorem-family
   (compare, logic, shift, arith-input bridges), committing per green family. Restate
   record-model hypotheses to Clean-`Spec` facts; Sail-space conclusions and
   `OpEnvelope` arities untouched; no new caller obligations.
4. **Migrate group (c)** and any stragglers.
5. **Delete Binary legacy surfaces** — `Airs/Binary/` model + packed-correctness files
   and `AirsClean/Binary/Bridge.lean` — when reference count is 0; root import updates in
   the same commit if needed.
6. **Delete BinaryExtension legacy surfaces** — same criterion, same discipline.
7. **Final sweep.** Reference counts before/after per family; deleted-file list; net
   line delta; `trust/generated/` byte-unchanged; full `lake build`,
   `trust/scripts/check-all.sh` (minus check 13), `trust/scripts/check-all-semantic.sh`
   all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

If the full group-(a) migration cannot finish in this turn, prioritize: complete enough
of (a)+(b) that at least ONE of the two families' deletions (items 5–6) actually lands —
a turn that deletes one family beats a turn that half-migrates both.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- The T6 Q2 audits gate the deletions; if deeper migration exposes any constraint the
  audits missed, stop that family and report precisely.
- Every restated hypothesis proved from the Clean supply — never weakened, broadened, or
  pushed to callers. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`,
  `partial`, `@[implemented_by]`. No `trust/generated/` change; no baseline; no
  `OpEnvelope` arity change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (and mirror in
`REFACTOR_8_REPORT.md`): per-item status table for 1–7; the consumer map; per-family
reference counts before/after; deleted files; net line delta; exact gate results.
