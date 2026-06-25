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
- A (rename, no binder/type change): StepComplianceStrong→StepFaithful,
  …_of_rowData→stepFaithful_of_evidence. No baseline regen. ← in progress.
- B (structural split): introduce ZiskStep/RowDecode/InputsAgree; keep the 63
  stepStrong_<op> proofs untouched (realize split at the types + dispatcher via
  struct-inheritance or a toRowData assembly); rewrite root_soundness.
- C: regenerate baseline-strong-export-binders.txt; V1+V2 gate; docs (#141).

Blocking: none.
Next step: build+commit Stage A.

Digression: motivated by issue #141 (placement assumed, not derived from Main AIR).
Note: a prior GitHub-issue-refresh stream's uncommitted STATUS/PLAN notes were
reset by this branch switch; recovery stub in scratchpad.
