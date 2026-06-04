Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: U/J/control-flow bridge slices through JALR are complete and committed.
Blocking: none.
Next step: review whether FENCE has bridge evidence to derive or whether the next depth-first target should move to ADD/ADDI/ADDW provider evidence.

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
