Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: LD/LBU/LHU/LWU zero-extension load slice complete.
Blocking: none.
Next step: commit the passing slice and continue to the next planned opcode group.

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

Current slice notes:
- Aeneas probe showed LD/LBU/LHU/LWU lower to internal `OP_COPYB` with
  `ind_width` 8/1/2/4.
- Added LD/LBU/LHU/LWU `aeneasBridgeTrust` branches, extracted-shape
  constructors, and bridge theorems using existing `OP_COPYB`, width, and Clean
  `store_pc` helpers.
- Added staged Aeneas row-shape checks for the zero-extension load route.
- Signed LB/LH/LW lower to external sign-extension opcodes 39/40/41 and are a
  separate provider slice.

Verification passed:
- `lake build ZiskFv.Compliance` passed.
- `trust/scripts/regenerate.sh` passed.
- `trust/scripts/check-all.sh` passed.
- `trust/scripts/check-all-semantic.sh` passed.
- `nix run .#aeneas-production-extract` passed.
