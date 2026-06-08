Active plan: docs/ai/plan/PLAN_EXPLICIT_TRUST_BOUNDARY_REPAIR.md
Current focus: explicit trust-boundary repair complete; PR branch in progress.
Blocking: none.
Next step: open PR for `restore-explicit-trust-axioms`.

Recent state:
- User clarified the goal is not to close trust gaps or add an
  accepted-execution theorem layer.
- The desired repair is to restore explicit axioms where PR #55/#56/#58 moved
  trust into harder-to-spot hypotheses or `OpEnvelope` fields.
- Clean completeness placeholders have been restored and the affected
  components point at them again.
- `aeneas_bridge_trust` has been restored and made a conjunct of
  `OpEnvelope.exec_eq`.
- Trust allowlists, tolerated completeness entries, generated ledgers, and
  trust docs now record 8 source axioms and 2 global-closure axioms.
- `lake build ZiskFv`, `trust/scripts/check-all.sh`,
  `trust/scripts/check-all-semantic.sh`, and the global closure print all
  passed; the closure is exactly `aeneas_bridge_trust` plus
  `row_models_sail_state_load`.
