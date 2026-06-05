Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: SB/SH/SW/SD store-family extracted-shape slice is implemented and verified; preparing commit.
Blocking: none.
Next step: review the diff and commit the completed store slice.

Recent completed slices:
- LUI/AUIPC/JAL/JALR/FENCE row-mode/control-pin slices are committed.
- ADD/ADDI/ADDW, SUB/SUBW/ADDIW, R-type and I-type logic/comparison, and
  BinaryExtension shift slices are committed through
  `a0e3cfea Add immediate W shift bridge slice`.

Current slice notes:
- Added store `OP_COPYB` pin/width/store-pc provenance helpers.
- Added SB/SH/SW/SD extracted-shape constructors and bridge theorems.
- Added staged Aeneas generated row-shape checks for SB/SH/SW/SD.
- First Aeneas run caught that store row `store_offset` carries the sample
  immediate, not zero; corrected the staged checks.
- Generated trust diffs are only the expected `aeneas_bridge_trust` line-number
  shift.

Verification passed:
- `lake build ZiskFv.Compliance`
- `trust/scripts/regenerate.sh`
- `trust/scripts/check-all.sh`
- `trust/scripts/check-all-semantic.sh`
- `nix run .#aeneas-production-extract`
