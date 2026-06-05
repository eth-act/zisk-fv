Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: U/control-flow wrapper ledger now tracks active row-provenance
wrappers for LUI/AUIPC/JAL.
Blocking: none.
Next step: commit the U/control wrapper-ledger correction, then audit
load/store residual `LoadPromises`/`StorePromises` and `LoadCleanWitness`
obligations.

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
- W-shift reduction committed as `2aa77fa4 Consolidate W-shift caller burden`.
- Renamed the active row-provenance LUI/AUIPC/JAL wrappers to `equiv_LUI`,
  `equiv_AUIPC`, and `equiv_JAL`; the older pin-based compatibility wrappers
  are now `_of_main_pins`.
- Wrapper caller-burden ledger now measures the active row-provenance surface
  for LUI/AUIPC/JAL. Wrapper total rows dropped 1123 -> 1117 and wrapper
  row_shape dropped 28 -> 22. Canonical caller-burden stayed unchanged.
- `lake build ZiskFv.Compliance` passed after the wrapper rename.
- `trust/scripts/regenerate.sh` passed.
- `trust/scripts/check-all.sh` passed.
- `trust/scripts/check-all-semantic.sh` passed.
- `nix run .#aeneas-production-extract` passed.
