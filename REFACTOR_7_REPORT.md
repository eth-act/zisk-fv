# Refactor 7 run report

`ARISTOTLE_SUMMARY.md` was intentionally left unchanged as requested by the
handoff instruction. This standalone report supplies the work-order report.

## Authoritative overlay

The authoritative archive was extracted over the existing tree without
removing `.lake` or build artifacts. A SHA-256 comparison of every regular
file in the archive reported zero mismatches immediately after extraction.
The overlay itself is checkpointed separately from the changes below.

## Numbered work-order status

| Item | Status | Result |
|---|---|---|
| 1. Binary Q2 + Interface | Done | Added `AirsClean/Binary/Interface.lean`, a Clean-row operation-bus API and the complete Q2 table. |
| 2. Binary rewire | Precisely blocked | The legacy bridge is still imported by 15 direct consumers, including the shared Binary-family/full-ensemble balance implementation, `Compliance/SharedBundles.lean`, `Compliance/Instantiation/ConcreteRowReductions.lean`, and `EquivCore/Bridge/Binary.lean`. Exact `Valid_Binary` usage remains 43 files / 173 occurrences. Extracting static-table facts into a bridge-free module was tested, but the root build exposed duplicate declarations whenever the still-required bridge was imported; completing the move requires atomically migrating the balance and EquivCore consumers, not adding an adapter. No caller obligation was added and no consumer was falsely claimed rewired. |
| 3. Binary delete | Precisely blocked | Gated by item 2. `AirsClean/Binary/Bridge.lean`, `EquivCore/Bridge/Binary.lean`, `Airs/Binary/Binary.lean`, and `BinaryPackedCorrect.lean` survive because the above consumers remain. |
| 4. BinaryExtension Q2 + Interface | Done | Added `AirsClean/BinaryExtension/Interface.lean` with the per-interaction Q2 table and the existing Clean row/static-component consumer seam. |
| 5. BinaryExtension rewire | Precisely blocked | `StaticCircuit.lean` itself imports `Bridge.lean` for static-table fact declarations. Twelve shift EquivCore modules (`Sll*`, `Srl*`, `Sra*`) directly import the bridge, and the full-ensemble balance modules do likewise. Exact `Valid_BinaryExtension` use remains 56 files / 151 occurrences. Breaking this cycle requires moving the shared static-table fact block and atomically migrating the shift/balance users. No new premise was introduced. |
| 6. BinaryExtension delete | Precisely blocked | Gated by item 5. The bridge, `EquivCore/Bridge/BinaryExtension.lean`, legacy model, packed-correctness, and range files remain load-bearing. |
| 7. MemAlign trio | Q2 done; deletion precisely blocked | Added one Interface/Q2 module per family. MemAlign has nine cross-row constraints intentionally outside row-local Clean `main`; they are coupled to the out-of-scope data-memory/cross-row layer. MemAlignByte and MemAlignReadByte range witnesses remain consumed by LBU/LHU/LWU and are assembled through `SharedBundles`/`LoadDerivation`, also in the out-of-scope data-memory layer. No deletion or caller obligation was forced. |
| 8. Final sweep | Done, with mandated check-13 deferral | Full build passed; checks 1–12 and 14–16 passed; check 13 alone failed because the authoritative tree has no `zisk` submodule; all 16 semantic checks passed; generated hashes and protected roots are unchanged. |

## Q2 correspondence tables

### Binary

| Legacy constraint/interaction | Clean counterpart |
|---|---|
| `boolean_mode32` | `assertZero (mode32 * (1 - mode32))` |
| `boolean_carry_7` | `assertZero (carry_7 * (1 - carry_7))` |
| `boolean_result_is_a` | `assertZero (result_is_a * (1 - result_is_a))` |
| `boolean_use_first_byte` | `assertZero (use_first_byte * (1 - use_first_byte))` |
| `boolean_c_is_signed` | `assertZero (c_is_signed * (1 - c_is_signed))` |
| `b_op_or_sext_def_holds` | `assertZero (b_op_or_sext - (mode32 * (c_is_signed + 512 - b_op) + b_op))` |
| `mode32_and_c_is_signed_def_holds` | `assertZero (mode32_and_c_is_signed - mode32 * c_is_signed)` |
| Eight BinaryTable permutation rows | `lookupMessage0` … `lookupMessage7`, as channel pulls or direct static lookups |
| Operation-bus permutation row | `OpBusChannel.push (opBusMessageExpr row)` |

Outcome: no semantic divergence. Algebraic constraints are one-for-one; the
legacy table/op-bus obligations and Clean interactions carry identical tuples.

### BinaryExtension

| Legacy constraint/interaction | Clean counterpart |
|---|---|
| No F-typed row constraints | No `assertZero` in `BinaryExtension.main` |
| BinaryExtensionTable rows for byte indices 0…7 | Eight byte-indexed channel pulls/direct static lookups |
| Operation-bus permutation row | `OpBusChannel.push (opBusMessageExpr row)` |
| Shift-only `b_0 : bits(24)` | `rangeTable24` lookup in the shift-only static component |

Outcome: no semantic divergence. The family is table-driven, and the shift
range is correctly restricted to shift rows.

### MemAlign

| Legacy constraints | Clean counterpart |
|---|---|
| `wr`, `reset`, up/down selectors, and `sel_0`…`sel_7` booleanity | First twelve `assertZero` operations |
| `boot_pc_zero`, `sel_prove_disjoint` | Next two assertions |
| `value_0_reconstruction`, `value_1_reconstruction` | Final two row-local assertions |
| Memory-bus interaction | `MemBusChannel.push (memBusMessageExpr row)` |
| `delta_addr_definition` and eight `down_to_up_continuity_N` | Deliberately outside row-local `main`; assigned to `CrossRow`/data-memory integration |

Outcome: row-local constraints correspond, but deletion is gated by the nine
cross-row constraints; dropping them would be a soundness gap.

### MemAlignByte

| Legacy constraints/interactions | Clean counterpart |
|---|---|
| Nine row predicates | Nine `assertZero` operations in the same order |
| `bus_byte : bits(8)`, `byte_value : bits(8)`, `is_write : bits(1)` | Direct `rangeTable8`, `rangeTable8`, and `rangeTable1` lookups |
| Memory-bus interaction | `MemBusChannel.push (memBusMessageExpr row)` |

Outcome: no semantic divergence; deletion is blocked only by the data-memory
consumer coupling described above.

### MemAlignReadByte

| Legacy constraints/interactions | Clean counterpart |
|---|---|
| Three selector booleans and composed-value identity | Four `assertZero` operations in the same order |
| `byte_value : bits(8)` | Direct `rangeTable8` lookup |
| Memory-bus interaction | `MemBusChannel.push (memBusMessageExpr row)` |

Outcome: no semantic divergence; deletion is blocked only by the data-memory
consumer coupling described above.

## Counts and deleted-file accounting

Exact whole-word counts are unchanged because blocked migrations were not
papered over:

| Family | Before | After | Deleted files |
|---|---:|---:|---|
| Binary | 43 files / 173 occurrences | 43 / 173 | none (blocked) |
| BinaryExtension | 56 / 151 | 56 / 151 | none (blocked) |
| MemAlign | 9 / 59 | 9 / 59 | none (cross-row blocker) |
| MemAlignByte | 7 / 49 | 7 / 49 | none (data-memory blocker) |
| MemAlignReadByte | 7 / 47 | 7 / 47 | none (data-memory blocker) |

Net source delta from the authoritative overlay checkpoint: **+195 lines**
(195 added, 0 deleted), comprising five Interface modules and five root
Interface imports.

## Verification

- `lake exe cache get`: passed; cache already populated.
- `lake build ZiskFv`: passed, **9014 jobs**.
- `trust/scripts/check-all.sh`: checks **1–12 and 14–16 passed**. Check 13
  alone was deferred/failed exactly because `zisk/core/src/aeneas_extract.rs`
  is unavailable with the omitted `zisk` submodule.
- `trust/scripts/check-all-semantic.sh`: **all 16 checks passed**.
- Zero-sorry gate: passed for every non-generated `ZiskFv` source.
- `trust/generated/`: SHA-256 manifest byte-identical before/after.
- `ZiskFv/Soundness.lean`, `ZiskFv/Completeness.lean`, and
  `ZiskFv/Audit.lean`: byte-identical to the authoritative overlay.
- No new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`, or
  `@[implemented_by]`; no `OpEnvelope` arity or theorem conclusion changed.
