Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: Phase 3 generated-proof bridge manifest is implemented and
verified.
Blocking: none.
Next step: commit the generated-bridge manifest slice, then continue Phase 3
with provider source-lane export feasibility.

Recent state:
- Opcode-family slices through MUL and DIV/REM are committed.
- `OpEnvelope.aeneasBridgeTrust` is exhaustive, and the broad
  `ZiskFv.Compliance.aeneas_bridge_trust` axiom is retired from the global
  theorem boundary.
- W-shift structural cleanup committed as `2aa77fa4`; canonical rows dropped
  1104 -> 1062, wrapper rows dropped 1165 -> 1123, and `bus_shape` dropped
  27 -> 0.
- U/control wrapper ledger correction committed as `2c521c67`; wrapper rows
  dropped 1123 -> 1117 and wrapper `row_shape` dropped 28 -> 22.
- Load/store and provider-family audits found no honest local reductions:
  residual promises/bridges need generated/full-ensemble proof integration.
- Phase 2 provider-family audit committed as `cebda3cd`.
- Added `trust/aeneas-generated-bridge-manifest.txt` plus a trust-gate check
  that keeps generated Aeneas bridge predicates/examples aligned with the
  generator template and generated output when present.
- Verification for the manifest slice passed:
  `lake build ZiskFv.Compliance`, `trust/scripts/regenerate.sh`,
  `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
  `nix run .#aeneas-production-extract`.
