Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: DIV/DIVU/DIVW/DIVUW/REM/REMU/REMW/REMUW ArithDiv slice complete.
Blocking: none.
Next step: audit remaining OpEnvelope gap acceptance criteria and trust-axiom retirement state.

Recent completed slices:
- LUI/AUIPC/JAL/JALR/FENCE row-mode/control-pin slices are committed.
- ADD/ADDI/ADDW, SUB/SUBW/ADDIW, R-type and I-type logic/comparison, and
  BinaryExtension shift slices are committed through
  `a0e3cfea Add immediate W shift bridge slice`.
- Store and zero-extension load slices are committed.
- Signed LB/LH/LW load slice is committed as
  `32360574 Add signed load bridge slice`.
- Branch slice is committed as `db9f0f2f Add branch bridge slice`.

Current slice notes:
- MUL/MULH/MULHU/MULHSU lower to external ArithMul opcodes with `m32 = 0`.
- MULW lowers to external `OP_MUL_W` with `m32 = 1`.
- All MUL-family rows should have register/register sources, register store,
  `store_pc = 0`, `set_pc = 0`, and fall-through `jmp_offset1/2 = 4`.
- Added MUL-family provenance helpers for opcode pins and row controls.
- Added `aeneasBridgeTrust` MUL-family cases plus extracted-shape constructors
  and bridge theorems.
- Added staged extraction checks for MUL-family row shape, external routing,
  register/register sources, register store, no PC controls, fall-through
  jumps, and MULW-only `m32`.
- Updated extraction docs for the MUL-family slice.
- `nix run .#aeneas-production-extract` passed for the new staged checks.
- `lake build ZiskFv.Compliance` passed.
- `trust/scripts/regenerate.sh` passed.
- `trust/scripts/check-all.sh` passed; generated trust diff is only the
  expected `aeneas_bridge_trust` line-number shift.
- `trust/scripts/check-all-semantic.sh` passed.
- Final `nix run .#aeneas-production-extract` passed.
- `trust/scripts/check-all.sh` passed; generated trust diff is only the
  expected `aeneas_bridge_trust` line-number shift.
- `trust/scripts/check-all-semantic.sh` passed.
- Final `nix run .#aeneas-production-extract` passed.

Current slice notes:
- DIV/DIVU/REM/REMU lower to external ArithDiv opcodes with `m32 = 0`.
- DIVW/DIVUW/REMW/REMUW lower to external W ArithDiv opcodes with `m32 = 1`.
- This slice should derive only Main opcode/control facts from row-shape
  provenance; dynamic ArithDiv provider, range, overflow, and operand facts
  remain explicit.
- Added DIV/REM-family provenance constants and pin/control helpers.
- Added explicit `aeneasBridgeTrust` cases for all DIV/REM-family arms.
- Added `DIV` and `DIVU` extracted-shape constructors/bridge theorems; focused
  `lake build ZiskFv.Compliance.AeneasBridgeTrust` passed.
- Added `DIVW`, `DIVUW`, `REM`, `REMU`, `REMW`, and `REMUW`
  extracted-shape constructors/bridge theorems; focused
  `lake build ZiskFv.Compliance.AeneasBridgeTrust` passed.
- Added staged extraction checks for all DIV/REM-family row shapes; `nix run
  .#aeneas-production-extract` passed.
- Updated extraction docs for the DIV/REM-family slice.
- `lake build ZiskFv.Compliance` passed.
- `trust/scripts/regenerate.sh` passed.
