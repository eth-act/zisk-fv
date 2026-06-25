Stream: root_soundness signature refactor (legible 3-way split).
Branch: clarity/root-soundness-shape. Plan: docs/ai/plan/PLAN_ROOT_SOUNDNESS_SHAPE.md

Goal: replace root_soundness's single `rowData` hypothesis with three named,
honest binders — ziskStep / rowDecodes / inputsAgree — and rename the conclusion
(StepComplianceStrong→StepFaithful) and derivation (…_of_rowData→
stepFaithful_of_evidence). The split surfaces, in the signature itself, the
dischargeable circuit facts (rowDecodes, owed by #141) vs the fundamental
cross-world assumption (inputsAgree).

Target signature:
  (ziskStep    : ∀ i, ZiskStep    ziskTrace          i)
  (rowDecodes  : ∀ i, RowDecode   ziskTrace          i (ziskStep i))
  (inputsAgree : ∀ i, InputsAgree ziskTrace sailTrace i (ziskStep i))
  (h_known_bugs: ∀ i, StepNoKnownDefect ziskTrace sailTrace i (ziskStep i) (rowDecodes i) (inputsAgree i))
  : ∀ i, StepFaithful ziskTrace sailTrace i (ziskStep i)

Decisions:
- StepNoKnownDefect TAKES THE EVIDENCE (user-confirmed). The 8 signed-M/FENCE
  defect arms build their env from arith-witness/operand data (see mulEnvOf), so
  claim-only is an endpoint property (defects→empty), not achievable now.
- nextPC fact is cross-world → lives in inputsAgree, keeping rowDecodes
  sailTrace-free. Circuit-only nextPC (→ rowDecodes) is a #141 follow-up.

Stages:
- A (rename): StepComplianceStrong→StepFaithful, …_of_rowData→
  stepFaithful_of_evidence. DONE — committed 4555d095, pushed, build+V1 green.
- B (structural split): DONE. RowDataSplit.lean (63× Claim/Decode/Inputs/
  toRowData, workflow wwvvvytoj). Dispatcher rewritten: ZiskStep inductive +
  RowDecode/InputsAgree + toFull; StrongRowConstructionData kept internal; old
  StepNoKnownDefect body kept verbatim as StepNoKnownDefectOn; new
  StepNoKnownDefect routes through toFull; StepFaithful transformed d→c over the
  claim; stepFaithful_of_evidence dispatches to the UNTOUCHED stepStrong_<op>.
  root_soundness rewritten with the 3 binders. 63 stepStrong proofs unchanged.
- C: DONE. baselines regenerated; full build 8760; V1 15/15; V2 13/13; 0 axioms.
  KEY: baseline-equiv-axiom-deps.txt + baseline-axioms.txt UNCHANGED → trust
  footprint byte-identical (pure re-packaging, no proof-strategy change).

Blocking: none.
Next step: commit + push Stage B; then update #141 / docs as wanted.

Digression: motivated by issue #141 (placement assumed, not derived from Main AIR).
Note: a prior GitHub-issue-refresh (codex) stream's uncommitted STATUS/PLAN
notes were reset by this branch switch; per user, discarded (not restored).
