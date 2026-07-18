# Task: Phase 3 — the Arith family group, plus one consistency relocation

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: BinaryAdd, BinaryExtension, and Binary are fully on the
Clean spine with their legacy surfaces deleted; your T8 Binary turn landed verbatim).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

The family recipe is proven three times over (BinaryAdd, BinaryExtension, Binary): Q2
constraint-correspondence audit → `Interface.lean` Clean-row API → migrate consumers
group-by-group → retire bridges as `ConsumerFacts`/`ConsumerTheorems` (moves, not
rewrites) → delete legacy at refcount 0. Your T8 turn's `AirsClean/Binary/` layout
(`Interface`, `Trace`, `ConsumerFacts`, `ConsumerTheorems`, `PackedCorrect`) is the
exemplar; `AirsClean/Binary/Interface.lean` carries the model "## Q2 constraint
correspondence" docstring section.

This turn's target is the Arith family group — the largest remaining bridge surface:
`EquivCore/Bridge/Arith.lean` (123.3K, 24 importing files), legacy `Airs/Arith/`
(`Mul.lean`, `Div.lean`, `CarryChain.lean`, `CarryChainCompleteness.lean`,
`BusRes1.lean`; 52 files reference the legacy paths), and the two Clean-side
compatibility bridges `AirsClean/ArithMul/Bridge.lean` and
`AirsClean/ArithDiv/Bridge.lean`. Unlike Binary, no `Interface.lean` exists yet for
ArithMul/ArithDiv — items 2 builds them, and their Q2 audits GATE the deletions.

## Numbered work order

1. **Refresh the consumer map** from the current tree for the whole Arith group: legacy
   `Airs/Arith/*`, `EquivCore/Bridge/Arith.lean`, `AirsClean/Arith{Mul,Div}/Bridge.lean`
   — file + declaration, grouped (mul, div, carry-chain, bus-res, balance/table,
   exports/wrappers/constructions). Commit it to `REFACTOR_10_REPORT.md` before
   migrating.
2. **Q2 audits + Interfaces.** For ArithMul and ArithDiv: write
   `AirsClean/ArithMul/Interface.lean` and `AirsClean/ArithDiv/Interface.lean` with the
   canonical-row API and a "## Q2 constraint correspondence" docstring auditing every
   legacy-model constraint against the Clean `Constraints`/`Spec` supply (mirror
   `AirsClean/Binary/Interface.lean`). If any legacy constraint has no Clean counterpart,
   stop that family's deletion and report precisely.
3. **Migrate consumers group-by-group** (mul, then div, then carry-chain/bus-res, then
   remaining), committing per green group. Retained semantic proofs move into the Clean
   families as moves, not rewrites (`Trace.lean`/`PackedCorrect`-style modules as
   needed). Restate record-model hypotheses to Clean-`Spec` facts; Sail-space conclusions
   and `OpEnvelope` arities untouched; zero new caller obligations.
4. **Retire the bridges**: `AirsClean/Arith{Mul,Div}/Bridge.lean` become
   `ConsumerFacts.lean`; `EquivCore/Bridge/Arith.lean` moves into the Clean families as
   `ConsumerTheorems` module(s), mirroring the Binary treatment.
5. **Delete the legacy surfaces** — `Airs/Arith/*` files — as each reaches reference
   count 0; import updates in the same commit.
6. **Consistency relocation (small, independent).** `EquivCore/Bridge/BinaryExtension.lean`
   is already Clean-fed (it imports only `AirsClean/BinaryExtension/*` for family data)
   but was never relocated. Move it to `AirsClean/BinaryExtension/ConsumerTheorems.lean`
   exactly as T8 did for Binary: namespace retarget, retitle, zero semantic change,
   update its importers. If blocked anywhere in items 1–5, do this item during the
   blockage instead of stopping.
7. **Final sweep.** Reference counts before/after; deleted-file list; net line delta;
   `trust/generated/` byte-unchanged; full `lake build`, `trust/scripts/check-all.sh`
   (minus check 13), `trust/scripts/check-all-semantic.sh` all green.

Prioritization: the ArithMul family fully migrated, retired, and deleted beats both
families half-migrated. Div's extra depth (defect boundary below) makes Mul the opening
move.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- **The DIV/REM defect boundary is part of the theorem claim and must survive
  unchanged**: every use of `ArithDivDynamicWitnessShape` (in
  `Compliance/TraceLevelExport*`) and the `h_known_bugs` exclusions keep their exact
  semantic content. Signed-operation scope holds stay as-is. If a migration step would
  alter what the defect gate excludes, stop that step and report.
- The Q2 audits gate the deletions; a legacy constraint without a Clean counterpart
  blocks that family's item 5 — report it, never paper over it.
- Every restated hypothesis proved from the Clean supply — never weakened, broadened, or
  pushed to callers. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`,
  `partial`, `@[implemented_by]`. No `trust/generated/` change; no baseline; no
  `OpEnvelope` arity change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_10_REPORT.md`):
per-item status for 1–7; the consumer map; the two Q2 audit outcomes; reference counts
before/after; deleted files; net line delta; exact gate results.
