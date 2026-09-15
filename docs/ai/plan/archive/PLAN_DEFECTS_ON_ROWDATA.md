# PLAN: lift the known-defect predicates off `OpEnvelope` onto row data

## Goal

Make `hAvoidKnownBugs` / `StepNoKnownDefect` self-documenting by stating the three
known defects **directly over the row data** (`Inputs_<op>` arith witness) instead
of over the legacy `OpEnvelope` interface. This collapses two "no-defect" notions
into one, deletes the per-op selector boilerplate and the old-sum scaffolding, and
makes the headline hypothesis readable in one `match`.

Subsumes the four ad-hoc cleanups raised in review:
- #1 delete the `StepNoKnownDefect → …On` pass-through — falls out (the redesigned
  `StepNoKnownDefect` is direct).
- #2 collapse the 55 selector matchers — gone entirely (one wildcard `=> True`).
- #3/#4 rename `EnvNoKnownDefectFor` / `Defects.NoKnownDefect` — moot; only one
  predicate survives, so there is nothing to disambiguate.

## Why

`Defects.NoKnownDefect` (`Defects.lean:162`) and the three shape predicates
(`MaliciousSignedMulWitnessShape` `Defects.lean:71`, `ArithDivDynamicWitnessShape`
`:123`, `FenceKnownGoodShape` `:41`) all `match` on `OpEnvelope` constructors —
the 63-arm sum the *old* global theorem `zisk_riscv_compliant_program_bus`
dispatches on. `EnvNoKnownDefectFor` (`Base.lean:66`) wraps that in a
`∀ env, sel env → NoKnownDefect env` so the 55 non-defect arms can avoid building
an env. The defect is genuinely a property of the **arith witness**
(`v.na/nb/np`, the remainder chunks) which now lives in `inputsAgree` — so the
`OpEnvelope` detour is a vestige, not a necessity.

## Target end state

`root_soundness` signature — unchanged except `hAvoidKnownBugs` drops `(rowDecodes i)`
(a forge is a witness property, not a decode fact):
```lean
(hAvoidKnownBugs : ∀ i, StepNoKnownDefect ziskTrace sailTrace i (ziskStep i) (inputsAgree i))
```

`StepNoKnownDefect` — one screen, no `OpEnvelope`:
```lean
def StepNoKnownDefect … (zs : ZiskStep …) (ia : InputsAgree … zs) : Prop :=
  match zs with
  | .mul _ | .mulh _ | .mulhsu _        => ¬ SignedMulForge ia
  | .div _ | .rem _ | .divw _ | .remw _ => ¬ DivRemForge ia
  | .fence _                            => FenceKnownGood ia
  | _                                   => True
```
where `SignedMulForge`/`DivRemForge`/`FenceKnownGood` are the three shapes from
`Defects.lean` re-expressed over the `Inputs_<op>` witness fields.

Deleted: `EnvNoKnownDefectFor`, `<op>EnvOf`-for-the-defect-check coupling at this
layer, `toFull`, `StrongRowConstructionData`, `StepNoKnownDefectOn`, the 55
selector arms.

## Work breakdown

- [ ] **A. Row-data shapes.** In `Defects.lean`, add `SignedMulForge`/`DivRemForge`/
  `FenceKnownGood` as predicates over the `Inputs_<op>` arith fields (same
  conditions: `(na=1∧nb=0∧np=0)∨(na=0∧nb=1∧np=0)`; `divisor≠0 ∧ |rem|=|divisor|`;
  `fm=0∧rs=x0∧rd=x0`). Keep the existing `OpEnvelope` shapes for now.
- [ ] **B. Bridge lemmas.** `signedMulForge_iff : SignedMulForge ia ↔ MaliciousSignedMulWitnessShape (mulEnvOf … (toRowData …))`
  and div/fence analogues. These must be PROVED (the witness fields are the same
  values); they are the audit that the re-statement is faithful, not a weakening.
- [ ] **C. Redefine `StepNoKnownDefect`** over `(ziskStep)(inputsAgree)` as the
  8-arm + wildcard `match` above. Delete `EnvNoKnownDefectFor`, `toFull`,
  `StrongRowConstructionData`, `StepNoKnownDefectOn`, and the pass-through.
- [ ] **D. Per-op proofs.** The 8 defect `stepStrong_<op>` proofs still build an
  `OpEnvelope` and feed `zisk_riscv_compliant_program_bus`; update them to consume
  the new predicate via the bridge lemmas (they take `rowDecodes` from its own
  binder to build the env). Check whether the 55 non-defect `stepStrong_<op>`
  need any change now that their obligation is `True` (open question — likely they
  re-derive `NoKnownDefect` locally; confirm at build time).
- [ ] **E. root_soundness + gate.** Drop `(rowDecodes i)` from `hAvoidKnownBugs`;
  regenerate `baseline-strong-export-binders.txt` (binder type change only);
  V1 (incl. partition check 16) + V2; confirm `baseline-equiv-axiom-deps.txt` +
  `baseline-axioms.txt` **byte-unchanged**.
- [ ] **F.** Update `dead-code-entry-points.txt` (drop `StrongRowConstructionData`)
  and the `TraceLevelExport.lean` doc that describes the old sum.

## Guardrails

- **Not a discharge — a re-expression.** The trust footprint must be byte-identical
  (`equiv-axiom-deps` + `axioms` unchanged). The bridge lemmas (step B) are the
  proof that the row-data shapes are exactly the old `OpEnvelope` shapes — no
  weakening, no new vacuity. No `axiom`/`sorry`/`decide`.
- Honest exceptions: if `StepNoKnownDefect` genuinely still needs `rowDecodes` or
  `sailTrace` for some arm, keep it and say so rather than forcing the clean shape.

## Relationship to the Dispatcher metaprogramming experiment

Orthogonal but synergistic. This redesign **removes** `StepNoKnownDefectOn` /
`toFull` / `StrongRowConstructionData` and the 55 selector arms — i.e. it deletes
most of what the macro experiment would otherwise have to generate. Sequence:
land this redesign first, THEN metaprogram the residual uniform 63-arm blocks
(`ZiskStep`/`RowDecode`/`InputsAgree`/`stepFaithful_of_evidence`). `StepFaithful`'s
non-uniform per-op equalities are untouched by either and remain the irreducible
core.
