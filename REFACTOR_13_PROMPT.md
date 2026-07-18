# Task: Phase 3 — derive the Arith record predicates from the Clean supply; remove caller obligations

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: `Airs/Arith/` is dissolved, the record models live in
`AirsClean/Arith{Mul,Div}/Semantics.lean` under their original namespaces, and the
`Arith{Mul,Div}TableWitness` bundles in `Compliance/SharedBundles.lean` now carry
`mainComplete` soundness with constructors proving the appended constraints from static
table membership).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

The Arith supply chain is complete and live: `mainComplete` (all generated constraints,
cited), the named projection layer (`complete_local_specs_of_const_soundness`,
`mode_spec_of_arith_table`, `base_soundness_of_complete_const_soundness`), and the
witness swap at `SharedBundles`. What remains is the consumption side: several surfaces
still take `Valid_ArithMul`/`Valid_ArithDiv` constraint predicates as caller-supplied
hypotheses instead of deriving them from that supply — e.g. `mul_circuit_holds` in
`ZiskCircuit/Mul.lean` embeds `mul_mode_booleans v r_arith` as a conjunct, and the same
pattern appears across `ZiskCircuit/{Div,Divu,MulH,MulHSU,MulHU,MulW,Rem,...}.lean` and
the `Tactics/{MulArchetype,ArithSMArchetype}.lean` archetype definitions. This is the
same seam-derived-binder removal already completed in Phase 2 for the static families:
a caller-supplied hypothesis that the ensemble can prove is a trust cost, not plumbing.

## Numbered work order

1. **Audit map.** Enumerate every declaration that consumes a `Valid_ArithMul` /
   `Valid_ArithDiv` constraint predicate (`mul_mode_booleans`, `main_mul_div_disjoint`,
   `boolean_*`, `div_by_zero_forces_*`, `div_overflow_forces_*`, `w_mode_bus_*`,
   `div_by_zero_inverse_sum`, `bus_res1`-related, carry-chain predicates) as a
   hypothesis, structure field, or `circuit_holds`-style conjunct. Classify each:
   (a) derivable from the Clean supply at the point of use, (b) derivable only at the
   dispatcher/StepStrong level, (c) genuinely irreducible (say why). Commit the map to
   `REFACTOR_13_REPORT.md` before changing anything.
2. **Derive and remove, family by family (Mul first).** For every class-(a)/(b) site:
   source the predicate from the witness/projection supply
   (`Arith{Mul,Div}TableWitness`, `mode_spec_of_arith_table`,
   `complete_local_specs_of_const_soundness`) at the appropriate level and delete the
   caller obligation — signature parameter, structure field, or `circuit_holds`
   conjunct. Report per-family before/after counts of caller-supplied Arith constraint
   hypotheses. Sail-space conclusions and `OpEnvelope` arities untouched; `Equivalence/`
   and root statements byte-identical.
3. **Interface tidy (small).** Fix the ArithMul `Interface.lean` Q2 table rows that
   attribute the ModeSpec constraints to `mainWithArithTable` (the supply is
   `mainComplete`); make both families' Q2 tables name their true suppliers.
4. **Final sweep.** Remaining caller-supplied Arith constraint hypotheses (target: only
   class-(c) with justifications); net line delta; `trust/generated/` byte-unchanged;
   full `lake build`, `trust/scripts/check-all.sh` (minus check 13),
   `trust/scripts/check-all-semantic.sh` all green.

Prioritization: the ArithMul family's consumers fully discharged beats both families
half-done. Do not touch `Compliance/Defects.lean` at all — its `Valid_ArithDiv`-typed
defect shapes are the frozen claim boundary and are exempt from this sweep.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- **`Compliance/Defects.lean` byte-unchanged** — the DIV/REM defect boundary is exempt
  from this sweep entirely.
- Removal only, never replacement: a deleted hypothesis must be DERIVED at the supply
  point, not renamed, weakened, broadened, or moved to a different caller. The
  constraint set stays frozen at the T10 audited list.
- Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`. No `trust/generated/` change; no baseline; no `OpEnvelope` arity
  change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_13_REPORT.md`):
per-item status for 1–4; the audit map with classifications; per-family before/after
caller-supplied-hypothesis counts; net line delta; exact gate results.
