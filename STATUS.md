Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: AND/OR/XOR/SLT/SLTU Binary provider-route slice verified; preparing commit.
Blocking: none.
Next step: commit the AND/OR/XOR/SLT/SLTU slice, then continue with the I-type logic/comparison immediates.

Notes:
- Existing branch already contains the explicit `aeneas_bridge_trust` boundary.
- This slice does not import generated Aeneas Lean into main Lake or shrink wrapper signatures yet.
- Added `MainRowProvenance.luiRowMode_of_extracted_shape` and a staged LUI row-mode Aeneas check.
- Added `OpEnvelope.luiOfExtractedShape` plus `OpEnvelope.aeneasBridgeTrust_luiOfExtractedShape`, so the derived row-mode proof now fills a real LUI envelope field and proves the LUI bridge predicate without using the axiom.
- `lake build ZiskFv.Compliance` passed.
- `trust/scripts/regenerate.sh` passed.
- `trust/scripts/check-all.sh` passed.
- `trust/scripts/check-all-semantic.sh` passed.
- First `nix run .#aeneas-production-extract` attempt failed before Lean because the app runtime lacked `riscv64-unknown-elf-ld`; adding the same embedded RISC-V toolchain used by the dev shell.
- Second Aeneas attempt exposed a `ziskfloat.elf` Cargo scheduling race; prebuilding the ELF in the extraction script.
- The Nix cross toolchain is prefixed `riscv64-none-elf-*`; adding temporary `riscv64-unknown-elf-*` shims for the upstream Makefile.
- `nix run .#aeneas-production-extract` passed; staged `GeneratedChecks` built.
- Dirty tree was audited and found to be one related workstream: explicit Aeneas bridge boundary plus the first LUI proof slice.
- Baseline committed as `5c10cdc1 Expose Aeneas bridge trust boundary`.
- Added AUIPC equivalents: `MainRowProvenance.auipcRowMode_of_extracted_shape`,
  `OpEnvelope.auipcOfExtractedShape`, staged `auipcRowModeEvidenceMatches`, and
  `OpEnvelope.aeneasBridgeTrust_auipcOfExtractedShape`.
- `lake build ZiskFv.Compliance` passed for the AUIPC slice.
- `trust/scripts/regenerate.sh` passed for the AUIPC slice.
- `trust/scripts/check-all.sh` passed for the AUIPC slice.
- `trust/scripts/check-all-semantic.sh` passed for the AUIPC slice.
- `nix run .#aeneas-production-extract` passed for the AUIPC slice.
- AUIPC slice committed as `cf245ab3 Add AUIPC row-mode bridge slice`.
- Added JAL equivalents: `MainRowProvenance.jalRowMode_of_extracted_shape`,
  `OpEnvelope.jalOfExtractedShape`, staged `jalRowModeEvidenceMatches`, and
  `OpEnvelope.aeneasBridgeTrust_jalOfExtractedShape`.
- `lake build ZiskFv.Compliance` passed for the JAL slice.
- `trust/scripts/regenerate.sh` passed for the JAL slice.
- `trust/scripts/check-all.sh` passed for the JAL slice.
- `trust/scripts/check-all-semantic.sh` passed for the JAL slice.
- `nix run .#aeneas-production-extract` passed for the JAL slice.
- JAL slice committed as `8d18277d Add JAL row-mode bridge slice`.
- Added JALR equivalents: `MainRowProvenance.jalrPins_of_extracted_shape`,
  `MainRowProvenance.jalrControl_of_extracted_shape`, staged
  `jalrControlEvidenceMatches`, `OpEnvelope.jalrOfExtractedShape`, and
  `OpEnvelope.aeneasBridgeTrust_jalrOfExtractedShape`.
- `lake build ZiskFv.Compliance` passed for the JALR slice.
- `trust/scripts/regenerate.sh` passed for the JALR slice.
- `trust/scripts/check-all.sh` passed for the JALR slice.
- `trust/scripts/check-all-semantic.sh` passed for the JALR slice.
- `nix run .#aeneas-production-extract` passed for the JALR slice.
- JALR slice committed as `82386cc7 Add JALR control-pin bridge slice`.
- Added FENCE equivalents: `MainRowProvenance.fencePins_of_extracted_shape`,
  staged `fencePinsEvidenceMatches`, `OpEnvelope.fenceOfExtractedShape`, and
  `OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape`.
- `lake build ZiskFv.Compliance` passed for the FENCE slice.
- `trust/scripts/regenerate.sh` passed for the FENCE slice.
- `trust/scripts/check-all.sh` passed for the FENCE slice.
- `trust/scripts/check-all-semantic.sh` passed for the FENCE slice.
- `nix run .#aeneas-production-extract` passed for the FENCE slice.
- FENCE slice committed as `2b5765d5 Add FENCE pin bridge slice`.
- Regular extraction probes show ADD/ADDI lower to external `OP_ADD`; ADDW
  lowers to external `OP_ADD_W`.
- Added `MainRowProvenance.addPins_of_extracted_shape` and
  `MainRowProvenance.addwPins_of_extracted_shape`.
- Added ADD/ADDI/ADDW `OpEnvelope.*OfExtractedShape` constructors and bridge
  theorems, plus staged external provider-route row-shape checks.
- `lake build ZiskFv.Compliance` passed for the ADD/ADDI/ADDW slice.
- `trust/scripts/regenerate.sh` passed for the ADD/ADDI/ADDW slice.
- `trust/scripts/check-all.sh` passed for the ADD/ADDI/ADDW slice.
- `trust/scripts/check-all-semantic.sh` passed for the ADD/ADDI/ADDW slice.
- First `nix run .#aeneas-production-extract` failed on the new ADDI full
  row-shape check; actual production row has `b_use_sp_imm1 = 0` and
  `b_offset_imm0 = 4096`, so the staged expectation was corrected.
- `nix run .#aeneas-production-extract` passed for the ADD/ADDI/ADDW slice.
- ADD/ADDI/ADDW slice committed as `caf568df Add ADD provider-route bridge slice`.
- Production probes show SUB lowers to external `OP_SUB`, SUBW lowers to
  external `OP_SUB_W`, and ADDIW lowers to external `OP_ADD_W` with immediate
  columns `b_use_sp_imm1 = 0`, `b_offset_imm0 = 4096` for the sample row.
- Added SUB/SUBW pin helpers, extended `aeneasBridgeTrust`, added
  SUB/SUBW/ADDIW `OpEnvelope.*OfExtractedShape` constructors and bridge
  theorems, and staged production row-shape checks.
- First full build caught a skipped `pins` field in the new SUB
  `aeneasBridgeTrust` pattern; fixed it and reran successfully.
- `lake build ZiskFv.Compliance` passed for the SUB/SUBW/ADDIW slice.
- `trust/scripts/regenerate.sh` passed for the SUB/SUBW/ADDIW slice.
- `trust/scripts/check-all.sh` passed for the SUB/SUBW/ADDIW slice.
- `trust/scripts/check-all-semantic.sh` passed for the SUB/SUBW/ADDIW slice.
- `nix run .#aeneas-production-extract` passed for the SUB/SUBW/ADDIW slice.
- SUB/SUBW/ADDIW slice committed as `f1b594c6 Add SUB provider-route bridge slice`.
- Added AND/OR/XOR/SLT/SLTU pin helpers, bridge predicates, constructors,
  bridge theorems, and staged production row-shape checks.
- `lake build ZiskFv.Compliance` passed for the AND/OR/XOR/SLT/SLTU slice.
- `trust/scripts/regenerate.sh` passed for the AND/OR/XOR/SLT/SLTU slice.
- `trust/scripts/check-all.sh` passed for the AND/OR/XOR/SLT/SLTU slice.
- `trust/scripts/check-all-semantic.sh` passed for the AND/OR/XOR/SLT/SLTU slice.
- `nix run .#aeneas-production-extract` passed for the AND/OR/XOR/SLT/SLTU slice.
- Generated trust diffs are only the expected `aeneas_bridge_trust` line-number shift.
