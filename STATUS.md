Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: LB/LH/LW signed-load BinaryExtension slice complete.
Blocking: none.
Next step: continue to the next planned opcode group.

Recent completed slices:
- LUI/AUIPC/JAL/JALR/FENCE row-mode/control-pin slices are committed.
- ADD/ADDI/ADDW, SUB/SUBW/ADDIW, R-type and I-type logic/comparison, and
  BinaryExtension shift slices are committed through
  `a0e3cfea Add immediate W shift bridge slice`.
- Store and zero-extension load slices are committed.

Current slice notes:
- LB/LH/LW lower to external sign-extension opcodes 39/40/41 with
  `ind_width` 1/2/4.
- The BinaryExtension static lookup/match side remains explicit; this slice
  derives the Main pins, width, and Clean `store_pc` facts from extracted shape.
- Added signed-load Main pin helpers, `aeneasBridgeTrust` branches,
  extracted-shape constructors, bridge theorems, and staged row-shape checks.
- `lake build ZiskFv.Compliance` passed for this slice.
- `trust/scripts/regenerate.sh` passed; generated trust diff is the expected
  `aeneas_bridge_trust` line-number shift.
- `trust/scripts/check-all.sh` passed.
- `trust/scripts/check-all-semantic.sh` passed.
- `nix run .#aeneas-production-extract` passed: 68 starts, 201 declarations.
