Stream: lift known-defect predicates off OpEnvelope onto row data.
Branch: clarity/defects-on-rowdata. Plan: docs/ai/plan/PLAN_DEFECTS_ON_ROWDATA.md

Goal: re-express the three known-defect predicates over the Inputs_<op>/Claim_<op>
row data instead of the legacy OpEnvelope sum, collapsing StepNoKnownDefect to one
8-arm + wildcard `match`. Semantics-preserving re-expression — trust footprint
byte-identical (NOT a discharge).

Status: COMPLETE. Committed 97b3841e, pushed origin/clarity/defects-on-rowdata
(no PR). Steps A–F all done.

- A Defects.lean: SignedMulForge / DivRemForge / DivRemForgeW / FenceKnownGood
  (same conditions as the OpEnvelope shapes).
- B EnvOf.lean: 8 PROVED `Iff.rfl` bridge lemmas (faithfulness audit).
- C Dispatcher.lean: StepNoKnownDefect = direct `match zs, ia`; deleted
  EnvNoKnownDefectFor / envNoKnownDefectFor_of_nondefect / toFull /
  StrongRowConstructionData / StepNoKnownDefectOn + 55 selector arms.
  Base.lean: added general `noKnownDefect_of_shapes` helper.
- D 63 stepStrong rewired: 55 non-defect take (_h_known : True) + build
  NoKnownDefect locally; 8 defect consume row-data forge-negation via the helper.
- E Soundness.lean: h_known_bugs drops (rowDecodes i). Sole sanctioned baseline
  churn = the h_known_bugs binder line in baseline-strong-export-binders.txt.
- F TraceLevelExport.lean module doc + dead-code-entry-points.txt comment refreshed.

Verification: lake build green (8760); V1 (incl. RowData-partition check 16) +
V2 both PASS; 0 project axioms; no axiom/sorry/native_decide/bare decide added.
baseline-equiv-axiom-deps.txt + baseline-axioms.txt byte-identical to origin/main.

Open questions (resolved empirically):
- 55 non-defect proofs needed no content change beyond binder/`have` rewiring —
  noKnownDefect_of_shapes closes the vacuous shapes definitionally.
- Dropping rowDecodes from h_known_bugs threads cleanly through the 8 defect
  proofs (they take rowDecodes from their own `d` binder to build the env).

Blocking: none. Next: the metaprogramming/macro pass is a separate later phase.

Env note: build/ symlinked to /home/cody/zisk-fv/build; zisk submodule inited.
Both are env-only, never committed.
