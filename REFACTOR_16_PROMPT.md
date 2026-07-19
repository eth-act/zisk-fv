# Task: Phase 4 PILOT — collapse the static-Binary shape families into parametric proofs (the mass-deletion test)

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it
integrates all of your prior accepted work: the Binary, BinaryExtension, BinaryAdd, and
Arith families are fully on the Clean spine; the Arith live provider is complete and the
Div wrapper bundles are derived).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context — this turn is a GO/NO-GO experiment

The refactor's owner will drop the entire stack unless it demonstrates large net line
deletion. This pilot is the test: collapse the per-opcode proof towers of the
**logic, compare, and shift** opcode classes (22 opcodes: AND/OR/XOR + I-variants,
SLT/SLTU/SLTI/SLTIU, SLL/SRL/SRA + I/W/IW variants) into **one parametric proof per
shape class plus per-opcode instance rows**. These 22 opcodes' `EquivCore/*.lean` files
total 5,461 lines and their `Compliance/Wrappers/*.lean` files 1,550 — the deletion
target. The parametrization precedents already exist: `ZiskFv/Tactics/
{ALURTypeArchetype,ALUITypeArchetype,ShiftArchetype,RTypeWArchetype}.lean` (shape-level
circuit predicates + bus-match lemmas) and the consolidated `ZiskFv/EquivCore/
WriteValueProofs/{BinaryLogic,BinaryCompare,BinaryShift}.lean` (the per-class semantic
cores). **Success = ≥5,000 net lines deleted with all gates green.** An honest partial
that fully collapses ONE class beats three half-collapsed classes.

## Numbered work order

1. **Shape inventory map.** For each of the three classes, list the per-opcode
   `EquivCore/<Op>.lean` + `Wrappers/<Op>.lean` declarations and factor them: what is
   genuinely per-opcode data (opcode literal, table row constants, Sail spec function,
   sign/width mode pins) vs. shared proof shape. Commit the map to
   `REFACTOR_16_REPORT.md` before migrating.
2. **Parametric core per class.** For each class, define the shape statement (a
   structure or explicit parameter list carrying the per-opcode data) and prove ONE
   parametric `equiv` theorem consuming: the class archetype (`Tactics/*Archetype`),
   the consolidated WriteValueProofs core, and the Clean family supply
   (`AirsClean/Binary*`, `DerivedRowFacts`, `SharedBundles` witnesses). The parametric
   theorem's conclusion must be the EXACT existing per-opcode conclusion shape —
   `Equivalence/<Op>.lean` public statements stay byte-identical and become thin
   instantiations.
3. **Instance table per class.** One small instances file per class: per opcode, the
   data record + the instantiation lemma(s) that `Equivalence/<Op>.lean` and
   `Compliance/Dispatch`/`TraceLevelExport` consumers need. Rewire those consumers to
   the instances.
4. **Delete** each per-opcode `EquivCore/<Op>.lean` and `Wrappers/<Op>.lean` as its
   reference count reaches 0; root import updates in the same commits.
5. **Final sweep.** NET LINE DELTA is the headline number — report it precisely
   (added vs deleted, excluding reports). Reference counts before/after; deleted-file
   list; full `lake build`, `trust/scripts/check-all.sh` (minus check 13),
   `trust/scripts/check-all-semantic.sh` all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document
the precise blocker (file, theorem, error), and continue. Commit after each green item
— one class fully collapsed and deleted per commit is the ideal granularity.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- **`Equivalence/<Op>.lean` public theorem STATEMENTS byte-identical** — their proof
  bodies may become instantiations of the parametric theorem, but every statement,
  name, and signature stays exactly as-is. `Compliance/Defects.lean` byte-unchanged.
- `OpEnvelope` arities untouched; no new caller obligations anywhere; the parametric
  hypotheses must be exactly the union of what the per-opcode proofs already consume —
  never broader.
- Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`. No `trust/generated/` change; no baseline.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_16_REPORT.md`):
per-item status; the factoring map; per-class before/after file+line inventory; the
precise net line delta; exact gate results.
