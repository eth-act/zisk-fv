# Refactor 8 report

## Status

| Item | Status |
|---|---|
| 1. Map surviving consumers | Done; map below. |
| 2. Migrate balance/static-table layer | Done for BinaryExtension. The FullEnsemble balance files now import the Clean `ConsumerFacts` API; `binaryExtensionOfTable` is directly a trace of canonical `BinaryExtensionRow`s. Binary remains unchanged. |
| 3. Migrate EquivCore bridges | Done for BinaryExtension: its bridge and all theorem families now use the Clean namespace and canonical-row trace. Binary remains unchanged. |
| 4. Constructions/dispatch/stragglers | Done for BinaryExtension across compliance wrappers, construction, trace exports, operation-bus code, equivalence, and load/shift consumers. |
| 5. Delete Binary legacy surfaces | Blocked/not attempted after prioritizing one complete family as directed. Its 3,848-line bridge and 59 remaining legacy-path references still cover compare, logic, arithmetic-input and shared balance facts; deleting it would leave half-migrated consumers. |
| 6. Delete BinaryExtension legacy surfaces | Done. The legacy model was deleted, packed correctness/ranges moved into the Clean family, and `Bridge.lean` was retired as `ConsumerFacts.lean`. |
| 7. Final sweep | Done. Full build and all applicable trust gates pass; check 13 is deferred because the authoritative tree has no `zisk` submodule. |

## Consumer map before migration

The exact declaration-level scan was grouped as follows.

### (a) EquivCore / bridge

- `EquivCore/Bridge/Binary.lean`: `byte_ranges_at`, chain range/carry helpers, static table slot and carry facts, compare chain families, W-mode families, 64-bit byte-chain families, logic output families, packed input families, and `itype_imm_subset_binary_row_of_main`.
- `EquivCore/Bridge/BinaryExtension.lean`: `project_match_op_clo_chi`, packed low/high input facts, 64/32-bit packed-input facts, register/immediate shift-pin facts, and sign-extension lane matching.
- Binary downstream declarations: `EquivCore/{Add,Addi,Addiw,Addw,And,Andi,Or,Ori,Slt,Slti,Sltiu,Sltu,Sub,Subw,Xor,Xori}.lean`, `Bridge/{Arith,BranchFlag}.lean`, and `WriteValueProofs/{Arith,BinaryCompare,BinaryLogic}.lean`.
- BinaryExtension downstream declarations: `EquivCore/{Sll,Slli,Slliw,Sllw,Sra,Srai,Sraiw,Sraw,Srl,Srli,Srliw,Srlw,Lb,Lh,Lw}.lean`, `Promises/BinaryExtensionHelpers.lean`, and `WriteValueProofs/BinaryShift.lean`.

### (b) balance/static-table

- `AirsClean/BinaryFamily/Balance.lean`: Binary static core/spec projections and Binary/BinaryExtension operation-bus row extraction.
- `AirsClean/FullEnsemble/Balance/{Classification,CounterpartClassification,EmbeddedInTrace,MemBusRowBridges,MemRowReplayProjections,OpBusRowBridges,RowExtraction,RowsBridgeFacts,SidecarColumns,TableProjections,TimelineEvidence}.lean`.
- The declaration-level record-model consumers were `binaryOfTable`, `binaryExtensionOfTable`, `rowAt_binaryExtensionOfTable`, and the associated operation-bus/table projections.

### (c) constructions/dispatch

- `Compliance/Construction{Load,Shift,Sub}.lean`, `Compliance/Instantiation/ConcreteRowReductions.lean`, `Compliance/OpEnvelope.lean`, `Compliance/SharedBundles.lean`.
- `Compliance/Wrappers/` for Binary logic/compare/arithmetic and BinaryExtension shift/load families.
- `Compliance/AeneasBridgeTrust/{BinaryRType,ImmediateAlu,Loads}.lean` and `Compliance/Dispatch/RTYPE.lean`.
- `Compliance/TraceLevelExport/{Base,ProgramDecode,RomDecodeBindingOps,RowDataArithMem}.lean`.

### (d) other

- `Airs/OperationBus/{OperationBus,Consolidated}.lean` (row encodings/permutation surfaces).
- `Airs/Tables/{BinaryTable,BinaryExtensionTable}.lean` and `Airs/Arith/Div.lean` (transitive/model imports).
- `Equivalence/` opcode exports for the corresponding Binary and BinaryExtension families.
- `ZiskCircuit/{SextLoadBridge,Shift}.lean`, plus the shift/load tactics and compatibility documentation.

## BinaryExtension migration and deletion

- Added `AirsClean/BinaryExtension/Trace.lean`: a trace is `ℕ → BinaryExtensionRow F`; named projections preserve readable theorem statements while making the Clean row the sole model.
- Moved the semantic table proofs to `AirsClean/BinaryExtension/PackedCorrect.lean` and static range projections to `Ranges.lean`.
- Renamed the compatibility bridge to `ConsumerFacts.lean`; its `rowAt` and `validOfRow` are now direct canonical-row operations.
- Rewired operation-bus, FullEnsemble balance, EquivCore shift/load, construction, wrappers, and exported equivalence consumers to this Clean namespace.
- Deleted:
  - `ZiskFv/Airs/Binary/BinaryExtension.lean`
  - `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean`
  - `ZiskFv/Airs/Binary/BinaryExtensionRanges.lean`
  - `ZiskFv/AirsClean/BinaryExtension/Bridge.lean`

## Reference counts and size

Counts are matching source lines for legacy module/namespace/bridge paths.

| Family | Before | After |
|---|---:|---:|
| BinaryExtension | 343 | 0 (the sole textual match is documentation referring to `Airs.BinaryExtensionTable`, not the deleted family) |
| Binary | 116 | 59 |

Diff from the authoritative installed checkpoint: 394 added lines, 602 deleted lines, net **-208 lines**. The apparent additions mostly reflect moving retained packed-correctness proofs into the Clean family; Git recognized those as 99%/92% renames.

## Verification

- Authoritative archive overlay: every archive file matched byte-for-byte immediately after installation.
- Submission tarballs removed and not committed.
- `lake build ZiskFv`: passed, 9014 jobs.
- Trust checks 1–12 and 14–16: all passed.
- Trust check 13: deferred exactly because the `zisk` submodule is absent.
- `trust/scripts/check-all-semantic.sh`: all 16 checks passed.
- Non-generated zero-sorry gate: passed.
- `trust/generated/`: byte-unchanged.
- `ZiskFv/Soundness.lean`, `ZiskFv/Completeness.lean`, and `ZiskFv/Audit.lean`: byte-identical to the authoritative checkpoint.
- No new forbidden constructs and no `OpEnvelope` arity changes.

`ARISTOTLE_SUMMARY.md` was intentionally left unchanged, following the direct instruction accompanying this continuation request.
