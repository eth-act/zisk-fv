# Task: Phase 3 roll, part 1 — Binary, BinaryExtension, and the MemAlign trio

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work; your completed BinaryAdd pilot — Interface, Q2 report,
bridge/model deletion — is landed and verified).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; do NOT delete
`.lake` or any build artifacts (Lake is content-addressed; only real deltas rebuild). If
your build is cold anyway, run `lake exe cache get` first. After installing, every tracked
file's content must exactly match the tarball. Your command window is ~22 minutes and
build progress persists across invocations — size build commands to complete within it
and re-invoke; a window cutoff is never a proof error.

Sandbox limitations, pre-acknowledged: no git branch history; no `zisk` submodule → defer
exactly trust check 13, every other gate is mandatory. Do not touch `lakefile.toml`,
`lake-manifest.json`, `flake.nix`, `flake.lock`, or `ZiskFv/Audit.lean`.

## Context

The BinaryAdd pilot established the family template: **(a)** consumer-facing
`Interface.lean` stated purely in Clean row/`Spec` terms; **(b)** Q2 per-constraint
correspondence report, which GATES deletion; **(c)** rewire consumers; **(d)** delete the
`AirsClean/<F>/Bridge.lean`, the family's `EquivCore/Bridge/` machinery where it becomes
consumer-free, and the legacy `Airs/` model, atomically with the root import. Apply that
template to the next families. Do not touch the Arith*, Mem (data memory), or Main
families this turn — they are the next slice.

## Numbered work order

Per family, the acceptance criteria are the pilot's: written Q2 table (in the family
Interface docstring + your summary), zero new caller obligations, conclusions and
`OpEnvelope` arities untouched, `Valid_<AIR>` reference count → 0 before its deletion,
build green per item, commit per green item.

1. **Binary family — Q2 + Interface.** `AirsClean/Binary/` vs the legacy `Airs/` Binary
   model: write the correspondence table; add `AirsClean/Binary/Interface.lean` with the
   Clean-row consumers' API (op-bus projection and the row-fact lemmas the equivalence
   layer needs; the evidence packages in `SharedBundles.lean` already point the way).
2. **Binary family — rewire.** Move the logic/compare/RTYPE/ITYPE consumer surface
   (EquivCore lemmas, `EquivCore/Bridge/Binary.lean` users, constructions) onto the
   Interface. `EquivCore/Bridge/Binary.lean` is large; migrate what the family deletion
   needs and blocker-note any survivor with its consumer list.
3. **Binary family — delete.** `AirsClean/Binary/Bridge.lean`, the legacy `Airs/` Binary
   model and its packed-correctness files, when consumer-free; root import in the same
   commit.
4. **BinaryExtension family — Q2 + Interface** (shifts; `shiftProviderRowFacts` and
   `ShiftProviderEvidence` already exist at the seam).
5. **BinaryExtension family — rewire** (shift EquivCore consumers,
   `EquivCore/Bridge/BinaryExtension.lean`).
6. **BinaryExtension family — delete** (`AirsClean/BinaryExtension/Bridge.lean` + legacy
   model) when consumer-free.
7. **MemAlign trio** (`MemAlign`, `MemAlignByte`, `MemAlignReadByte` — small bridges):
   same template, all three, or precise blocker notes where their facts are coupled to
   the data-memory family (which is out of scope this turn — do not force it).
8. **Final sweep.** Per-family: Q2 tables, `Valid_<AIR>` reference counts before/after,
   bridge files deleted vs surviving-with-reasons; net line delta; `trust/generated/`
   byte-unchanged; full `lake build`, `trust/scripts/check-all.sh` (minus check 13),
   `trust/scripts/check-all-semantic.sh` all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified blocker
note. A clean build or a committed chunk is a checkpoint, not a stop condition: after
finishing an item, proceed immediately to the next. Committing and reporting with items
silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue with the next item. Commit after
each green item so a cancellation loses nothing.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched; `ZiskFv.lean` may gain exactly the family Interface
  imports named above, nothing else.
- Each family's Q2 outcome gates its deletion: any divergence between a legacy predicate
  and the Clean constraints is a potential soundness gap — stop that family and report
  it precisely; never paper over by picking a side.
- Every rewired hypothesis proved from the Clean `Spec`/accepted-trace supply — never
  weakened, broadened, or replaced by a caller obligation. Zero new `axiom`, `sorry`,
  `admit`, `native_decide`, `opaque`, `partial`, `@[implemented_by]`. No
  `trust/generated/` change; no baseline created. No `OpEnvelope` arity changes.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` with: the per-item status table for
items 1–8; each family's Q2 table; per-family `Valid_<AIR>` counts before/after and the
deleted-file list; net line delta; and exact gate results.
