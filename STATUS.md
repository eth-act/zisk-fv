Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: final hardening of `OpEnvelope.aeneasBridgeTrust` complete.
Blocking: none.
Next step: review or merge the completed worktree branch.

Recent state:
- Opcode-family slices through MUL and DIV/REM are committed.
- `OpEnvelope.aeneasBridgeTrust` now has explicit `fence`, `auipc_x0`, and
  `jal_x0` cases and no wildcard branch.
- Focused `lake build ZiskFv.Compliance.AeneasBridgeTrust` passed.
- Full `lake build ZiskFv.Compliance`, trust regeneration/checks, semantic
  trust checks, and `nix run .#aeneas-production-extract` passed.
- The global `ZiskFv.Compliance.aeneas_bridge_trust` axiom still remains; this
  slice narrows the local predicate but does not import generated Aeneas
  evidence into main Lake.
