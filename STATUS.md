Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: BEQ/BNE/BLT/BGE/BLTU/BGEU branch slice complete.
Blocking: none.
Next step: continue to the next planned opcode group.

Recent completed slices:
- LUI/AUIPC/JAL/JALR/FENCE row-mode/control-pin slices are committed.
- ADD/ADDI/ADDW, SUB/SUBW/ADDIW, R-type and I-type logic/comparison, and
  BinaryExtension shift slices are committed through
  `a0e3cfea Add immediate W shift bridge slice`.
- Store and zero-extension load slices are committed.
- Signed LB/LH/LW load slice is committed as
  `32360574 Add signed load bridge slice`.

Current slice notes:
- Branches lower to external EQ/LT/LTU opcodes with `m32 = 0`,
  `set_pc = 0`, and `store_pc = 0`.
- BEQ/BLT/BLTU use `jmp_offset2 = 4`; BNE/BGE/BGEU are negated and use
  `jmp_offset1 = 4`.
- Added branch provenance helpers for EQ pins, branch controls, and
  fall-through jump offsets.
- Added `aeneasBridgeTrust` branch cases plus extracted-shape constructors and
  bridge theorems for all six branch opcodes.
- Added staged Aeneas branch row-shape checks; production extraction confirmed
  the expected row snapshots.
- Updated extraction/trust docs for the branch route.
- `lake build ZiskFv.Compliance` passed for this slice.
- `trust/scripts/regenerate.sh` passed; generated trust diff is the expected
  `aeneas_bridge_trust` line-number shift.
- `trust/scripts/check-all.sh` passed.
- `trust/scripts/check-all-semantic.sh` passed.
- `nix run .#aeneas-production-extract` passed: 68 starts, 201 declarations.
- Dynamic branch immediates remain outside this slice because branch
  `OpEnvelope` arms do not carry a Main-row provenance field.
