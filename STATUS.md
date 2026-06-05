Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: broad `aeneas_bridge_trust` axiom retired from the global boundary.
Blocking: none.
Next step: audit remaining caller-burden acceptance criteria or review/merge this completed reduction slice.

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
- Remaining caller-burden bridge/row_shape/bus_shape/promises fields are still
  ordinary `OpEnvelope`/wrapper obligations; generated Aeneas Lean is still not
  imported into main Lake.
