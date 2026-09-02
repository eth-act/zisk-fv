# ZisK AIR Inventory

This note is a maintainer-facing map of the AIRs present in the flake-built
`build/zisk.pilout`, used when checking whether a proof path is drawing from
the expected generated circuit surface. It is intentionally kept outside
[`../../trust/`](../../trust/README.md): trust classes, axiom counts, closure
rationale, and CI gates live only under `trust/`.

Regenerate the pilout with:

```bash
nix run .#populate
```

List AIRs with the `air` subcommand's `--list` flag:

```bash
cargo run --manifest-path tools/pil-extract/Cargo.toml -- \
  air --pilout build/zisk.pilout --list
```

## AIRs

The pilout declares **35** AIRs in one group `Zisk` (see
[`extractor-notes.md`](extractor-notes.md) "Pilout structure observations"; the
10 extracted ones are listed in `nix/extracted-lean.nix` and cross-checked in
both directions by `tools/pilout-roundtrip/check.py`'s `DECLARED_AIRS`). The
table below covers the first 22 — the RV64IM-relevant span plus the precompile
and table AIRs adjacent to it. Indices `#22`–`#34` are not yet transcribed here;
read them off `--list`.

| #    | AIR               | RV64IM role                                        | Extraction status                                             |
| ---: | ---               | ---                                                | ---                                                           |
| 0    | Main              | Central decoded-instruction and operation-bus row. | Extracted; wrapped by `ZiskFv/Airs/Main/`.                    |
| 1    | Rom               | Program storage.                                   | Not on the current per-opcode equivalence path.               |
| 2    | Mem               | Memory state machine.                              | Partially modeled through memory-row and bus bridges.         |
| 3    | RomData           | ROM data section.                                  | Not on the current per-opcode equivalence path.               |
| 4    | InputData         | Public-input infrastructure.                       | Out of current per-opcode scope.                              |
| 5    | MemAlign          | Memory alignment.                                  | Extracted/wrapped where needed for current load/store proofs. |
| 6    | MemAlignByte      | Memory byte alignment.                             | Extracted/wrapped where needed for current load/store proofs. |
| 7    | MemAlignReadByte  | Memory read-byte alignment.                        | Extracted/wrapped where needed for current load/store proofs. |
| 8    | MemAlignWriteByte | Memory write-byte alignment.                       | Extracted/wrapped where needed for current load/store proofs. |
| 9    | Arith             | MUL/DIV/REM family.                                | Extracted; wrapped by `ZiskFv/Airs/Arith/`.                   |
| 10   | Binary            | Boolean, comparison, and packed binary relations.  | Extracted; wrapped by `ZiskFv/Airs/Binary/`.                  |
| 11   | BinaryAdd         | ADD/SUB carry chains.                              | Extracted; wrapped by `ZiskFv/Airs/Binary/BinaryAdd.lean`.    |
| 12   | BinaryExtension   | Shifts and extension paths.                        | Extracted; wrapped by `ZiskFv/Airs/Binary/`.                  |
| 13   | Add256            | Precompile/internal family.                        | Out of RV64IM scope.                                          |
| 14   | ArithEq           | Precompile/internal family.                        | Out of RV64IM scope.                                          |
| 15   | ArithEq384        | Precompile/internal family.                        | Out of RV64IM scope.                                          |
| 16   | Keccakf           | Precompile.                                        | Out of RV64IM scope.                                          |
| 17   | Sha256f           | Precompile.                                        | Out of RV64IM scope.                                          |
| 18   | U256Delegation    | ZisK-internal operation.                           | Out of RV64IM scope.                                          |
| 19   | SpecifiedRanges   | Range-check lookup table.                          | Used through range/table proof infrastructure.                |
| 20   | VirtualTable0     | Internal lookup table.                             | Used through table proof infrastructure where relevant.       |
| 21   | VirtualTable1     | Internal lookup table.                             | Used through table proof infrastructure where relevant.       |

## MemAlignWriteByte reads the MemAlignByte template

`MemAlignWriteByte` (#8) is not modelled on its own terms. The reading this note
records, and which `ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean` machine-checks,
is that its generated polynomials are the `ZiskFv.Airs.MemAlignByte` predicates
read at the *WriteByte* column layout — the same PIL template with the
`mem_write_values` columns shifted. There is no `MemAlignWriteByte` mirror
anywhere under `ZiskFv/` and no `MemAlignWriteByte` component in
`fullRv64imSoundEnsemble`, so the welds check generated text against this
documented reading without protecting any live proof.

## Shared generated files

Beyond the per-AIR constraint files, the extraction emits:

| file | role |
| --- | --- |
| `Circuit.lean` | the four-field `Extraction.Circuit` class shim every per-AIR file is typed over |
| `LookupWiring.lean` | the constraint-linked lookup-wiring manifest, plus an `AirStatus` row for every pilout AIR |
| `MemAlignRom.lean` | MemAlignRom's PIL fixed columns |
| `MemGeneratedArtifact.lean` | the typed Mem generated-artifact contract |
| `MemGeneratedConstraintBridge.lean` | the bridge from `Extraction.Mem` to ProverData-backed Mem sources |
| `MemAirFacts.md` | the Mem AIR facts audit report |
| `ArithTable.lean` | the finite state-machine table used by Arith lookup proofs; its historical trust-shape audit is now in [`../../trust/trusted-base.md`](../../trust/trusted-base.md) |
| `Buses.lean`, `MemoryBuses.lean` | bus-emission specs. **No consumer:** `BusEmissionSpec` is unreferenced under `ZiskFv/`, and neither module is in `lakefile.toml`'s `Extraction` globs. |

`nix/extracted-lean.nix` is the authoritative list of what is emitted and how.
