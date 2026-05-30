# ZisK AIR Inventory

This is an inventory of AIRs in the flake-built `build/zisk.pilout`. It is not
the trust ledger. Trust classes, axiom counts, and closure rationale live only
under [`../../trust/`](../../trust/README.md).

Regenerate the pilout with:

```bash
nix run .#populate
```

List AIRs with:

```bash
tools/pil-extract -- --pilout build/zisk.pilout --list
```

## AIRs

| # | AIR | RV64IM role | Extraction status |
| ---: | --- | --- | --- |
| 0 | Main | Central decoded-instruction and operation-bus row. | Extracted; wrapped by `ZiskFv/Airs/Main/`. |
| 1 | Rom | Program storage. | Not on the current per-opcode equivalence path. |
| 2 | Mem | Memory state machine. | Partially modeled through memory-row and bus bridges. |
| 3 | RomData | ROM data section. | Not on the current per-opcode equivalence path. |
| 4 | InputData | Public-input infrastructure. | Out of current per-opcode scope. |
| 5 | MemAlign | Memory alignment. | Extracted/wrapped where needed for current load/store proofs. |
| 6 | MemAlignByte | Memory byte alignment. | Extracted/wrapped where needed for current load/store proofs. |
| 7 | MemAlignReadByte | Memory read-byte alignment. | Extracted/wrapped where needed for current load/store proofs. |
| 8 | MemAlignWriteByte | Memory write-byte alignment. | Extracted/wrapped where needed for current load/store proofs. |
| 9 | Arith | MUL/DIV/REM family. | Extracted; wrapped by `ZiskFv/Airs/Arith/`. |
| 10 | Binary | Boolean, comparison, and packed binary relations. | Extracted; wrapped by `ZiskFv/Airs/Binary/`. |
| 11 | BinaryAdd | ADD/SUB carry chains. | Extracted; wrapped by `ZiskFv/Airs/BinaryAdd/`. |
| 12 | BinaryExtension | Shifts and extension paths. | Extracted; wrapped by `ZiskFv/Airs/Binary/`. |
| 13 | Add256 | Precompile/internal family. | Out of RV64IM scope. |
| 14 | ArithEq | Precompile/internal family. | Out of RV64IM scope. |
| 15 | ArithEq384 | Precompile/internal family. | Out of RV64IM scope. |
| 16 | Keccakf | Precompile. | Out of RV64IM scope. |
| 17 | Sha256f | Precompile. | Out of RV64IM scope. |
| 18 | U256Delegation | ZisK-internal operation. | Out of RV64IM scope. |
| 19 | SpecifiedRanges | Range-check lookup table. | Used through range/table proof infrastructure. |
| 20 | VirtualTable0 | Internal lookup table. | Used through table proof infrastructure where relevant. |
| 21 | VirtualTable1 | Internal lookup table. | Used through table proof infrastructure where relevant. |

The extractor also emits shared files such as `Buses.lean`,
`MemoryBuses.lean`, and `ArithTable.lean`. `ArithTable.lean` is the finite
state-machine table used by Arith lookup proofs; its historical trust-shape
audit is now in
[`../../trust/arith-table-axiom-audit.md`](../../trust/arith-table-axiom-audit.md).
