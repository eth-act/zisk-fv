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

All **35** AIRs of the pilout's single `Zisk` group, as reported by `--list`
against the flake-built `build/zisk.pilout`. Ten are extracted; the other 25 are
not. The extracted set is declared in `nix/extracted-lean.nix` and cross-checked
in both directions by `tools/pilout-roundtrip/check.py`'s `DECLARED_AIRS`.

**Indices move.** They are positions in `air_groups[0].airs`, not stable ids: the
twelve `Dma*` AIRs at `#0`–`#11` displaced everything after them relative to an
earlier pilout. Re-read them from `--list` after any `nix run .#populate`; do not
cite them from memory.

|    # | AIR                    | RV64IM role                                          | Extraction status |
| ----: | ---------------------- | ---------------------------------------------------- | --- |
|    0 | Dma                    | DMA engine.                                          | Out of RV64IM scope. |
|    1 | DmaMemCpy              | DMA memcpy path.                                     | Out of RV64IM scope. |
|    2 | DmaInputCpy            | DMA input-copy path.                                 | Out of RV64IM scope. |
|    3 | Dma64Aligned           | 64-bit aligned DMA.                                  | Out of RV64IM scope. |
|    4 | Dma64AlignedInputCpy   | 64-bit aligned DMA input copy.                       | Out of RV64IM scope. |
|    5 | Dma64AlignedMemSet     | 64-bit aligned DMA memset.                           | Out of RV64IM scope. |
|    6 | Dma64AlignedMem        | 64-bit aligned DMA memory path.                      | Out of RV64IM scope. |
|    7 | Dma64AlignedMemCpy     | 64-bit aligned DMA memcpy.                           | Out of RV64IM scope. |
|    8 | DmaUnaligned           | Unaligned DMA.                                       | Out of RV64IM scope. |
|    9 | DmaPrePost             | DMA pre/post fixup.                                  | Out of RV64IM scope. |
|   10 | DmaPrePostMemCpy       | DMA pre/post memcpy.                                 | Out of RV64IM scope. |
|   11 | DmaPrePostInputCpy     | DMA pre/post input copy.                             | Out of RV64IM scope. |
|   12 | Main                   | Central decoded-instruction and operation-bus row.   | **Extracted**; wrapped by `ZiskFv/Airs/Main/`. |
|   13 | Rom                    | Program storage.                                     | Not on the current per-opcode equivalence path. |
|   14 | Mem                    | Memory state machine.                                | **Extracted**; welded by `ZiskFv/AirsClean/MemMirrorWeld.lean`. |
|   15 | RomData                | ROM data section.                                    | Not on the current per-opcode equivalence path. |
|   16 | InputData              | Public-input infrastructure.                         | Out of current per-opcode scope. |
|   17 | MemAlign               | Memory alignment.                                    | **Extracted**; wrapped for current load/store proofs. |
|   18 | MemAlignByte           | Memory byte alignment.                               | **Extracted**; Clean component + mirror weld. |
|   19 | MemAlignReadByte       | Memory read-byte alignment.                          | **Extracted**; Clean component. |
|   20 | MemAlignWriteByte      | Memory write-byte alignment.                         | **Extracted**, but no mirror or component — see below. |
|   21 | Arith                  | MUL/DIV/REM family.                                  | **Extracted**; wrapped by `ZiskFv/Airs/Arith/`. |
|   22 | Binary                 | Boolean, comparison, and packed binary relations.    | **Extracted**; wrapped by `ZiskFv/Airs/Binary/`. |
|   23 | BinaryAdd              | ADD/SUB carry chains.                                | **Extracted**; wrapped by `ZiskFv/Airs/Binary/BinaryAdd.lean`. |
|   24 | BinaryExtension        | Shifts and sign-extension paths.                     | **Extracted**; wrapped by `ZiskFv/Airs/Binary/`. |
|   25 | Add256                 | Precompile/internal family.                          | Out of RV64IM scope. |
|   26 | ArithEq                | Precompile/internal family.                          | Out of RV64IM scope. |
|   27 | ArithEq384             | Precompile/internal family.                          | Out of RV64IM scope. |
|   28 | Keccakf                | Precompile.                                          | Out of RV64IM scope. |
|   29 | Sha256f                | Precompile.                                          | Out of RV64IM scope. |
|   30 | Poseidon2              | Precompile.                                          | Out of RV64IM scope. |
|   31 | Blake2br               | Precompile.                                          | Out of RV64IM scope. |
|   32 | SpecifiedRanges        | Range-check lookup table.                            | Used through range/table proof infrastructure. |
|   33 | VirtualTable0          | Internal lookup table.                               | Used through table proof infrastructure where relevant. |
|   34 | VirtualTable1          | Internal lookup table.                               | Used through table proof infrastructure where relevant. |

Constraint totals: 4095 across all 35 AIRs, of which 355 are in the 10 extracted
ones — the denominator both round-trip gates work against.

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
