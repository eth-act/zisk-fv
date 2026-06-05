Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: W-shift structural caller-burden reduction is implemented and
verified.
Blocking: none.
Next step: commit the W-shift reduction, then continue Phase 2 with the
U/control-flow residual row-shape/promise audit.

Recent state:
- Opcode-family slices through MUL and DIV/REM are committed.
- `OpEnvelope.aeneasBridgeTrust` now has explicit `fence`, `auipc_x0`, and
  `jal_x0` cases and no wildcard branch.
- Removed `env.aeneasBridgeTrust` from `OpEnvelope.exec_eq` and deleted the
  broad `ZiskFv.Compliance.aeneas_bridge_trust` axiom.
- `lake build ZiskFv.Compliance` passed after the axiom-removal edit.
- `trust/scripts/regenerate.sh` passed and rewrote the axiom baseline to 7
  entries.
- `trust/scripts/check-all.sh` passed with 7 axioms.
- `trust/scripts/check-all-semantic.sh` passed with the global closure matching
  the 7-axiom baseline.
- `nix run .#aeneas-production-extract` passed.
- Remaining caller-burden ledgers still show bridge=119, row_shape=27/37, and
  bus_shape=27. The broad trust axiom is gone, but these are still ordinary
  canonical/wrapper obligations.
- Plan file is being expanded so `PLAN_OP_ENVELOPE_GAP.md` tracks the full
  remaining acceptance work, not only the completed opcode-family slices.
- W-shift (`SLLW`/`SRLW`/`SRAW`) wrapper and canonical signatures now consume
  the existing `RTypePromises` bundle instead of 15 individual structural
  state/bus/row-shape binders.
- Caller-burden diff after W-shift cleanup: total canonical rows 1104 -> 1062,
  wrapper rows 1165 -> 1123, bus_shape 27 -> 0, canonical row_shape 27 -> 18,
  wrapper row_shape 37 -> 28, bridge 119 -> 122 because the three W-shift
  promise bundles are now classified as bridge.
- `lake build ZiskFv.Compliance.Dispatch.Remaining` passed.
- `lake build ZiskFv.Compliance` passed.
- `trust/scripts/regenerate.sh` passed.
- `trust/scripts/check-all.sh` passed.
- `trust/scripts/check-all-semantic.sh` passed.
- `nix run .#aeneas-production-extract` passed.
