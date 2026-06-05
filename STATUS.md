Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: MUL/MULH/MULHU/MULHSU/MULW ArithMul slice complete.
Blocking: none.
Next step: enter the next remaining OpEnvelope gap slice.

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
