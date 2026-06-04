# RV ADD Completeness Progress

## Target

Prove the narrow RV completeness slice for ADD:

For every raw 32-bit instruction word that the generated Sail model decodes
and encodes as `instruction.RTYPE (..., rop.ADD)`, the production ZisK path
extracted by Aeneas accepts it, lowers it, materializes a row, maps it to
covered opcode id `6`, and is outside known ZisK gaps.

This is a split target while the checked-in Sail Lean tree and the generated
Aeneas Lean workspace use different Lean toolchains:

- checked-in Lean proves Sail ADD raw words are exactly in the ADD raw shape;
- generated Aeneas Lean checks every ADD raw shape is covered by production
  ZisK decode/lower/materialize/opcode predicates.

## Checklist

- [x] Recover and branch the RV completeness work.
- [x] Initialize the pinned ZisK extraction submodule locally.
- [x] Populate local generated dependencies with `nix run .#populate`.
- [x] Add checked-in `AddRawShape`.
- [x] Prove Sail ADD executable raw words are in `AddRawShape`.
- [x] Add checked-in abstract ADD completeness theorem.
- [x] Add generated Aeneas ADD coverage check.
- [x] Run targeted checked-in Lean build.
- [x] Run targeted Aeneas extraction check.

## Commands

```sh
git submodule update --init zisk
nix run .#populate
nix develop . --command lake build ZiskFv.Completeness.SailDecode
nix develop . --command lake build ZiskFv.Completeness.Rv64im
AENEAS_CHECK_RV_COMPLETENESS=1 nix run .#aeneas-production-extract
```

## Current Notes

- The checked-in Lean build completed successfully with
  `nix develop . --command lake build ZiskFv.Completeness.SailDecode
  ZiskFv.Completeness.Rv64im ZiskFv.Completeness.Fence`.
- `AENEAS_CHECK_RV_COMPLETENESS=1 nix run .#aeneas-production-extract`
  completed successfully. The generated check includes
  `allAddRawShapesCircuitCovered_ok`, an exhaustive 32 x 32 x 32 raw ADD
  shape coverage check over the extracted production decoder/lowering path.
- The extraction app now includes the RISC-V cross toolchain in its Nix
  runtime inputs. Without it, the ZisK `lib-float` build could call
  `riscv64-unknown-elf-ld` outside the app environment.
- The ZisK extraction helper now restores
  `extract_transpile_rv64im_materializes_raw`; the generated Lean checks
  already expected this wrapper for row-materialization coverage.
- The ADD proof must not introduce a second hand-written ZisK decoder. The
  ZisK side must use `extract_decode_rv64im_raw` and
  `extract_transpile_rv64im_materializes_raw` from the Aeneas extraction
  harness.
