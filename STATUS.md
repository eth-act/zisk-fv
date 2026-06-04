Active plan: docs/ai/plan/PLAN_OP_ENVELOPE_GAP.md
Current focus: first depth-first stopping point complete and verified.
Blocking: none.
Next step: commit the explicit bridge boundary plus first LUI proof slice, then continue to the next depth-first slice.

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
