Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: completion audit cleanup is verified.
Blocking: none.
Next step: none for this plan; continue only if starting the next
generated/full-ensemble provider-row export stream.

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
- Generated row-shape facts are guarded by the manifest. Provider source-lane
  and memory witness facts are explicitly deferred until generated/full-ensemble
  artifacts export provider/Mem row values into the main boundary.
- Final Phase 4 verification passed: `lake build ZiskFv.Compliance`,
  `trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
  `trust/scripts/check-all-semantic.sh`, and
  `nix run .#aeneas-production-extract`.
- Final docs record 7 source trust declarations, 1 global-closure project
  axiom, zero `bus_shape` caller burden, and remaining bridge/row-shape/promise
  entries as generated/full-ensemble integration boundaries.
- Final boundary docs committed as `163dfc39`.
- Completion audit found and fixed stale README/module-doc wording that still
  described the retired broad Aeneas bridge boundary as active. Verification
  passed again: `lake build ZiskFv.Compliance`, `trust/scripts/regenerate.sh`,
  `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
  `nix run .#aeneas-production-extract`, and the generated-bridge manifest
  gate after extraction.
