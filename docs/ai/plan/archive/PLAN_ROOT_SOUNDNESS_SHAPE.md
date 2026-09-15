# PLAN: root_soundness signature refactor — legible 3-way split

## Goal

Make `root_soundness` (ZiskFv/Soundness.lean) read as three honest, named
per-step inputs instead of one opaque `rowData`, surfacing the trust map in the
signature. Motivated by issue #141 (the per-row facts are *assumed*, not derived
from the Main AIR).

Target:

```lean
theorem root_soundness
    (ziskTrace    : AcceptedZiskTrace)
    (sailTrace    : SailTrace ziskTrace)
    (ziskStep     : ∀ i, ZiskStep    ziskTrace          i)
    (rowDecodes   : ∀ i, RowDecode   ziskTrace          i (ziskStep i))
    (inputsAgree  : ∀ i, InputsAgree  ziskTrace sailTrace i (ziskStep i))
    (h_known_bugs : ∀ i, StepNoKnownDefect ziskTrace sailTrace i (ziskStep i) (rowDecodes i) (inputsAgree i)) :
    ∀ i, StepFaithful ziskTrace sailTrace i (ziskStep i) :=
  fun i => stepFaithful_of_evidence ziskTrace sailTrace i (ziskStep i) (rowDecodes i) (inputsAgree i) (h_known_bugs i)
```

## The three concepts (from the design conversation)

- **`ziskStep i`** — what the ZisK machine did at step i: which op, on which
  operand/dest registers, via which committed bus row (`execRow`). Purely
  ZisK-side (no `sailTrace`). Carries the per-op classification (63 arms).
- **`rowDecodes i`** — the row genuinely decodes to / is wired as that op:
  op-column pins, exec-row shape, destination index. Circuit-checkable
  (`sailTrace`-free). DISCHARGEABLE from the Main AIR (#141); currently assumed.
- **`inputsAgree i`** — the circuit's inputs equal Sail's register/PC/memory
  state for what this step reads. The lone genuinely cross-world assumption
  (needs `sailTrace`). Also carries the cross-world `nextPC` fact.

`StepFaithful` (conclusion) = the ZisK step's effect equals Sail's; needs only
the claim. `StepNoKnownDefect` = not a known forge; takes the evidence (see
Decisions).

## Decisions (confirmed)

1. **`StepNoKnownDefect` takes the evidence**, not the claim alone. The 8
   signed-M/FENCE defect arms (`mul mulh mulhsu div rem divw remw fence`) build
   their env from arith-witness/operand fields (`mulEnvOf` consumes `mul_input`,
   `arith_table`, ranges, `h_rs1_value`, …). Claim-only is an *endpoint*
   property — reachable once the forge-defects are discharged and the predicate
   is `True` everywhere — not now.
2. **`nextPC` lives in `inputsAgree`.** `h_nextPC_matches` compares the circuit
   column to a *spec-computed* value, so it is cross-world. Keeping it out of
   `rowDecodes` makes `rowDecodes` `sailTrace`-free. Making nextPC circuit-only
   (so it can migrate into `rowDecodes`) is a #141-flavored follow-up.

## Stages

- [x] **A — conclusion/derivation rename** (no binder/type change → no baseline
  regen). `StepComplianceStrong → StepFaithful`,
  `stepComplianceStrong_of_rowData → stepFaithful_of_evidence`. 3+3 refs +
  doc-comment + `trust/dead-code-entry-points.txt` comment. Build, commit.
- [x] **B — structural split.** Introduce `ZiskStep` (claim, 63 arms),
  `RowDecode` / `InputsAgree` (by cases on `ziskStep`). KEEP the 63
  `stepStrong_<op>` proofs untouched by realizing the split at the type +
  dispatcher boundary — either each `RowData_<op>` `extends Claim/Decode/Inputs`
  (field access via inheritance survives), or a flat `RowData_<op>` plus a
  `toRowData : Claim → Decode → Inputs → RowData_<op>` assembly used inside the
  dispatcher. Redefine `StepFaithful` over the claim, `StepNoKnownDefect` over
  claim+evidence, `stepFaithful_of_evidence` to assemble and dispatch. Rewrite
  `root_soundness`.
- [x] **C — gate + docs.** Regenerate `baseline-strong-export-binders.txt`
  (binders change), run V1 (`check-all.sh`) + V2 (`check-all-semantic.sh`),
  update the doc comments / `trust/dead-code-entry-points.txt` /
  `docs/.../TraceLevelExport.lean`. Confirm 0 axioms, no equiv-baseline drift.

## Guardrails

- 0 project axioms must hold; canonical `equiv_<OP>` axiom-deps baseline must not
  drift (this refactor is above that layer — it should not).
- Anti-laundering: this is a *re-presentation* of the existing `rowData`
  hypothesis, not a discharge. We are NOT folding `rowDecodes` into `ziskTrace`
  (that is #141 and requires proving `AcceptedZiskTrace → rowDecodes`). The
  binder stays visible as the honest IOU.
- One branch, incremental commits (no stacked PRs).

## Review Pass: PR Stack #143 -> #145 -> #146

- [x] Review #143 incremental diff against `main`: root_soundness split and trust
  baselines.
- [x] Review #145 incremental diff against `clarity/root-soundness-shape`:
  `AcceptedZiskTrace` parameterization and `mainOfTable` opacity change.
- [x] Review #146 incremental diff against `clarity/numinstr-param`: slim
  `RowData_<op>` bundles and field redirection in step proofs.
- [x] Run targeted verification or record why local verification was not run.
- [x] Deliver code-review findings with file/line references.

## Review Pass 2: Updated PR #146 Response

- [x] Inspect the response delta `d71da7ee..559bff1b`.
- [x] Confirm previous finding 1 (`RowDecode`/`Decode_*` SailTrace dependency)
  is fixed at the exported signature and helper layers.
- [x] Confirm previous finding 2 (unsigned-M decode pins bucketed under
  `Inputs_*`) is fixed.
- [x] Run appropriate verification on the updated #146 tip.
- [x] Deliver follow-up review findings.
