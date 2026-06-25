Stream: re-root known-defect predicates onto ziskTrace (drop inputsAgree) + rename trio.
Branch: clarity/defects-trace-local (off clarity/defects-on-rowdata = PR #149).
Plan: docs/ai/plan/PLAN_DEFECTS_TRACE_LOCAL.md

Goal: make the per-step defect predicate row-local (read the forge witness off
ziskTrace, not inputsAgree), drop inputsAgree/sailTrace from the defect path, and
apply the rename trio.

Status: PARTIAL. Step 3 (renames) DONE; steps 1/2 (trace projection, drop
inputsAgree) DEFERRED — genuine blocker, see below.

Done (step 3 — decl renames, pure):
- StepNoKnownDefect    → RowOutsideDefectRegion
- StepFaithful         → StepSound
- stepFaithful_of_evidence → stepSound_of_evidence
- root_soundness binder hAvoidKnownBugs → rowsOutsideDefects
  Files: Dispatcher.lean, Soundness.lean, Defects.lean (doc), TraceLevelExport.lean
  (doc), EnvOf.lean (doc), StepStrongSignedM.lean (doc), dead-code-entry-points.txt.
  Sole baseline churn: baseline-strong-export-binders.txt line 6 (binder/type rename;
  still retains sailTrace+inputsAgree → confirms the deferred removal).

DEFERRED (steps 1/2 — drop inputsAgree/sailTrace from the defect path): BLOCKED.
The forge shapes read v.na/nb/np (signed-MUL) and v.nr/v.d_* (DIV/REM) — committed
Arith WITNESS columns that are NOT carried on the operation-bus message. See
ZiskFv/Airs/Arith/Mul.lean:199-242 (opBus_row_Arith / opBus_row_ArithMulSecondary
expose only op, a/b/c lanes, mult, flag — no na/nb/np). So h_match_primary /
h_match_secondary (op-bus matches_entry) cannot pin na/nb/np. Further, NO
main_request_<op>_provided / exists_arithMul_provider_row_matches_* derivation
exists for the 7 defect ops (only the 6 non-defect M-ext ops mulw/mulhu/divu/
divuw/remu/remuw — OpBusProviderMatch.lean / ArithBalance.lean), and
Inputs_<op>.h_match_* is a caller-supplied field. Bridging a trace-projected
witness's ¬shape back to the env's caller-supplied ia.v (as stepStrong_<op> needs)
would require an Arith-provider-table accessor reading the committed sign columns
PLUS a uniqueness argument the op bus does not supply — i.e. exactly the
Arith-fidelity / na=MSB infrastructure the plan declares out of scope and
footprint-neutral. The plan's premise ("values already tied to the matched Arith
row by h_match_*") is false for the na/nb/np / nr portion.

Verification: lake build green (8768); V1 16/16 (incl. partition check 16) + V2
13/13 PASS; 0 project axioms; no axiom/sorry/native_decide/bare decide added.
baseline-equiv-axiom-deps.txt + baseline-axioms.txt byte-identical to
origin/clarity/defects-on-rowdata (footprint-neutral, as intended).

Env note: build/ symlinked to /home/cody/zisk-fv/build; zisk submodule inited.
Both env-only, never committed.

Next: steps 1/2 require building the defect-op Arith provider-match derivations
+ an Arith-provider-table witness accessor (committed na/nb/np), which is the
#114-cat-D / arith-fidelity workstream — not footprint-neutral. Re-scope before
attempting.
