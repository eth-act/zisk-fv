# Summary of changes for run b030a945-bee6-4328-9643-cfc6edd87816
Completed the Refactor 10 work order to the verified Q2 boundary and documented all results in `REFACTOR_10_REPORT.md` (leaving `ARISTOTLE_SUMMARY.md` unchanged as requested).

Key results:
- Installed the authoritative tarball non-destructively and verified all 828 archived files byte-for-byte.
- Produced a declaration-level Arith consumer map.
- Added canonical-row interfaces and full Q2 correspondence audits for ArithMul and ArithDiv.
- Found verified deletion blockers in both families: the current Clean circuits omit required flag/disjointness and constraint-46 facts; ArithDiv additionally lacks boundary, inverse-witness, W-mode, and scope constraints.
- Preserved the DIV/REM defect boundary unchanged and retained all five legacy Arith files rather than weakening claims or adding caller obligations.
- Relocated the Arith compatibility surfaces to `ConsumerFacts.lean` and the shared theorem surface to `AirsClean/ArithMul/ConsumerTheorems.lean`.
- Relocated BinaryExtension’s theorem surface to `AirsClean/BinaryExtension/ConsumerTheorems.lean`.
- Eliminated all references to the old bridge module paths.
- Kept `Soundness.lean`, `Completeness.lean`, `Audit.lean`, and `trust/generated/` byte-unchanged.

Verification:
- `lake build ZiskFv` passed (9,014 jobs).
- All 16 semantic trust checks passed.
- Trust checks 1–12 and 14–16 passed; check 13 was deferred exactly as directed because the supplied tree lacks the `zisk` submodule.
- The non-generated zero-sorry gate passed.
- All retained changes were committed and pushed.

# Summary of changes for run fd33428b-7bde-44f5-9bb6-48040853a08b
Completed the Refactor 9 Binary-family work order.

- Installed the authoritative archive non-destructively and verified all 826 archived files byte-for-byte.
- Migrated Binary’s shared balance/static-table, compare, logic, arithmetic/input, wrappers, constructions, trace exports, and equivalence consumers to canonical Clean rows.
- Added `AirsClean/Binary/Trace.lean` and moved retained semantics into `PackedCorrect.lean`, `ConsumerFacts.lean`, and `ConsumerTheorems.lean` under the Clean Binary family.
- Deleted the legacy Binary model, packed-correctness path, and old bridge surfaces.
- Confirmed zero remaining legacy Binary imports or qualified references.
- The migration commit changed 87 files: 895 lines added, 1,141 deleted, net −246 lines.
- Added the full consumer map, per-item status, deletion list, reference counts, and gate results to `REFACTOR_9_REPORT.md`.
- Left `ARISTOTLE_SUMMARY.md` unchanged as explicitly requested.

Verification:
- `lake build ZiskFv` passed (9,014 jobs).
- All 16 semantic trust checks passed.
- Trust checks 1–12 and 14–16 passed; check 13 was deferred because the supplied tree lacks the `zisk` submodule.
- The non-generated zero-sorry gate passed.
- `trust/generated/`, `Soundness.lean`, `Completeness.lean`, and `Audit.lean` remain byte-unchanged.
- All retained work was committed and pushed.

# Summary of changes for run 244ce64a-5440-418e-907a-b64e2e64a156
Completed Refactor 8 with one family fully migrated and deleted, following the work order’s prioritization rule.

- Installed the authoritative archive non-destructively and verified every archived file byte-for-byte.
- Removed accumulated root submission tarballs without committing them.
- Produced the declaration-level consumer map in `REFACTOR_8_REPORT.md`.
- Fully migrated BinaryExtension consumers to canonical Clean rows across balance/static-table, EquivCore shift/load bridges, operation-bus code, constructions, wrappers, and equivalence exports.
- Added `AirsClean/BinaryExtension/Trace.lean`, making traces families of `BinaryExtensionRow` values.
- Moved retained semantic proofs into the Clean family as `PackedCorrect.lean` and `Ranges.lean`.
- Replaced the old compatibility `Bridge.lean` surface with `ConsumerFacts.lean` using direct canonical-row projections.
- Deleted all BinaryExtension legacy model files and its old bridge surface.
- Left Binary intact rather than half-migrating it; the report records its precise remaining blockers and references.
- Net change from the authoritative checkpoint: 394 lines added, 602 deleted, net −208 lines.

Verification completed:
- `lake build ZiskFv` passed (9014 jobs).
- Trust checks 1–12 and 14–16 passed; check 13 was deferred because the supplied tree lacks the `zisk` submodule.
- All 16 semantic trust checks passed.
- The non-generated zero-sorry gate passed.
- `trust/generated/` is unchanged.
- `Soundness.lean`, `Completeness.lean`, and `Audit.lean` remain byte-identical.
- No forbidden proof constructs or `OpEnvelope` arity changes were introduced.

Full details, consumer map, reference counts, deleted-file list, blockers, and gate results are in `REFACTOR_8_REPORT.md`. `ARISTOTLE_SUMMARY.md` was left unchanged as requested. All retained work was committed and pushed.

# Summary of changes for run 44985a2a-c8cf-4f3a-aef0-d20b61119b16
Completed the Refactor 7 work order to the extent permitted by verified architectural blockers.

- Installed `refactor-7-0c17fd05.tar.gz` non-destructively over the existing tree and verified every archive file by SHA-256 with zero mismatches.
- Added Clean consumer interfaces and detailed Q2 correspondence audits for:
  - Binary
  - BinaryExtension
  - MemAlign
  - MemAlignByte
  - MemAlignReadByte
- Added only the five corresponding Interface imports to `ZiskFv.lean`.
- Precisely documented why the remaining rewiring/deletion work cannot safely be completed in this slice:
  - Binary and BinaryExtension remain coupled to their shared balance, static-table, and EquivCore consumers.
  - MemAlign retains nine cross-row constraints owned by the out-of-scope data-memory integration.
  - MemAlignByte and MemAlignReadByte range witnesses remain coupled to the out-of-scope load/data-memory trace layer.
- Preserved all legacy models and bridges where deletion would otherwise discard constraints or break active consumers; no obligations were moved to callers.
- Left `ARISTOTLE_SUMMARY.md` unchanged as explicitly requested. The complete item-by-item report, all five Q2 tables, exact reference counts, surviving bridge consumer lists, net line delta, and gate results are in `REFACTOR_7_REPORT.md`.

Verification:
- `lake build ZiskFv` passed (9014 jobs).
- Trust checks 1–12 and 14–16 passed.
- Trust check 13 was deferred exactly because the authoritative tree omits the `zisk` submodule.
- All 16 semantic trust checks passed.
- The non-generated zero-sorry gate passed.
- `trust/generated/` remained byte-identical.
- `ZiskFv/Soundness.lean`, `ZiskFv/Completeness.lean`, and `ZiskFv/Audit.lean` remained byte-identical.
- No forbidden trust constructs, theorem conclusion changes, or `OpEnvelope` arity changes were introduced.

All retained work was committed and pushed.

# Summary of changes for run 29d64c61-0c93-4149-b3eb-666c5304a0cc
Completed the full Refactor 6 BinaryAdd pilot work order.

- Installed and byte-compared the authoritative tarball overlay with zero mismatches.
- Added the Q2 legacy-to-Clean constraint correspondence report to `ZiskFv/AirsClean/BinaryAdd/Interface.lean` and `REFACTOR_6_REPORT.md`; no semantic divergence was found.
- Rewired ADD/ADDI consumers to direct Clean `BinaryAddRow`, `ComponentSpecFacts`, arithmetic, and op-bus APIs without changing `OpEnvelope` constructor arities or Sail-space conclusions.
- Deleted the obsolete BinaryAdd bridge, legacy `Valid_BinaryAdd` model and predicates, packed-correctness implementation, and obsolete compatibility surfaces.
- Reduced `Valid_BinaryAdd` usage from 16 files / 49 occurrences to zero.
- Added the required `BinaryAdd.Interface` import to `ZiskFv.lean` while leaving `ZiskFv/Audit.lean` and both root theorem statements unchanged.
- Confirmed `trust/generated/` is byte-for-byte unchanged.
- Full `lake build ZiskFv` passed (9009 jobs).
- Trust checks 1–12 and 14–16 passed; check 13 was precisely deferred because the authoritative tree omits the `zisk` submodule, as anticipated by the work order.
- All 16 semantic trust checks passed, including root and axiom-closure checks.
- The zero-sorry gate passed for all non-generated ZiskFv sources.
- Prepended the required detailed status and verification report to `ARISTOTLE_SUMMARY.md`, with a standalone copy in `REFACTOR_6_REPORT.md`.

All retained changes were committed and pushed.

# Summary of changes for refactor 6 BinaryAdd pilot completion (2026-07-17)

# Refactor 6 run report

## Work-order status

| Item | Status | Result |
|---|---|---|
| 1. Q2 correspondence report | Done | Added the correspondence table and range/op-bus accounting to `ZiskFv/AirsClean/BinaryAdd/Interface.lean`. No constraint divergence was found. |
| 2. Rewire BinaryAdd consumers | Done | ADD/ADDI EquivCore, write-value proofs, wrappers, dispatch, and construction/StepStrong feeds now consume `BinaryAddRow`, `ComponentSpecFacts`, `binary_add_chunks_eq_bv_add_of_component_spec`, and the Clean op-bus projection directly. Sail-space conclusions and `OpEnvelope` constructor arities are unchanged. |
| 3. Delete bridge and expose interface | Done | Deleted `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`; `ZiskFv.lean` now imports `ZiskFv.AirsClean.BinaryAdd.Interface`. |
| 4. Delete `Valid_BinaryAdd` | Done | Deleted the legacy definition, predicates, packed-correctness file, obsolete EquivCore bridge, operation-bus legacy arm/projection, and unused witness/compositional compatibility surfaces. No consumers remain. |
| 5. Final sweep | Done, with mandated check-13 deferral | Full build and every runnable trust gate passed. Check 13 was not run because the supplied tree has no `zisk` submodule, as pre-acknowledged in the work order. |

## Q2 constraint correspondence

The four legacy predicates and four Clean assertions agree exactly after projecting the same ten row columns. The only syntactic difference after elaboration is subtraction (`x - y = 0`) versus addition of a negation (`x + -y = 0`).

| Legacy predicate | Clean assertion in `BinaryAdd.main` |
|---|---|
| `boolean_cout_0` | `assertZero (cout_0 * (1 - cout_0))` |
| `carry_chain_0` | `assertZero ((a_0 + b_0) - (cout_0 * 2^32 + c_chunks_1 * 2^16 + c_chunks_0))` |
| `boolean_cout_1` | `assertZero (cout_1 * (1 - cout_1))` |
| `carry_chain_1` | `assertZero ((a_1 + b_1 + cout_0) - (cout_1 * 2^32 + c_chunks_3 * 2^16 + c_chunks_2))` |

The Clean circuit additionally performs eight static lookups: 32-bit lookups for `a_0`, `a_1`, `b_0`, and `b_1`, and 16-bit lookups for `c_chunks_0` through `c_chunks_3`. On the legacy side these were the separate `a_chunks_in_range`, `b_chunks_in_range`, and `c_chunks_in_range` predicates supplied by range-table soundness rather than included in `core_every_row`.

The Clean `OpBusChannel.push (opBusMessageExpr row)` corresponds to the legacy BinaryAdd operation-bus projection and permutation/balance proof. It likewise was separate from the four legacy algebraic predicates. Therefore the constraint sets do not diverge: Clean makes explicit the same range and operation-bus obligations previously carried in separate layers.

## Consumer sweep

- Before: 16 Lean files and 49 textual occurrences of `Valid_BinaryAdd`.
- After: 0 files and 0 occurrences.
- Remaining consumers: none.
- `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`: deleted.
- Legacy `ZiskFv/Airs/Binary/BinaryAdd.lean`: deleted.
- Legacy `ZiskFv/Airs/Binary/BinaryAddPackedCorrect.lean`: deleted.
- Obsolete `ZiskFv/EquivCore/Bridge/BinaryAdd.lean`: deleted.

## Verification

- Authoritative tarball installation: all 819 regular tarball files were compared byte-for-byte immediately after overlay; 0 mismatches.
- `lake exe cache get`: completed; cache already present.
- `lake build ZiskFv`: passed (9009 jobs).
- `trust/scripts/check-all.sh`, excluding only check 13: checks 1–12 and 14–16 all passed.
- Check 13 (`check-aeneas-production-boundary.py`): precisely deferred because the supplied tree omits the `zisk` submodule.
- `trust/scripts/check-all-semantic.sh`: all 16 semantic checks passed.
- `trust/generated/`: byte-for-byte unchanged (pre/post SHA-256 manifests compare equal).
- `ZiskFv/Audit.lean`: unchanged; SHA-256 before and after is `28d8be7076d710fbc9e5a2a11f82a04b0ded176852ca954cd7c48dcef5376ad6`.
- `root_soundness` and `root_completeness`: statements remain byte-for-byte identical to the installed authoritative tree.
- Zero-sorry gate: passed for every non-generated ZiskFv Lean source.


# Summary of changes for run 38ee2eb7-8349-4552-b0c5-ec050cae6128
You’re right—the direct answer is:

## Recommended top-level API

Keep exactly two advertised endpoints, collected in `ZiskFv/Audit.lean`:

1. **`root_soundness`** — the unconditional soundness result over an `AcceptedZiskTrace`.
2. **`root_completeness`** — explicitly conditional on one named `ZiskCompletenessObligations` record until each construction obligation is proved.

For `root_soundness`, preserve the theorem’s meaning and bundle only premises that are already explicit root binders, such as input agreement, boot-memory seed, and scope/defect exclusions. Do **not** add channel balance, Aeneas-bridge evidence, or memory-timeline evidence as new root assumptions: channel balance is already part of `AcceptedZiskTrace`, while the other evidence is derived internally. Adding it to the root would weaken the theorem.

The old `zisk_riscv_compliant_program_bus` theorem should remain an internal per-operation implementation lemma, not a second public soundness endpoint. Freeze both root statements and their axiom closures in `Audit.lean`, so accidental API or trust changes fail the build.

## Recommended proof architecture

The target dependency structure should be:

```text
Sail semantics + PIL constraints
          ↓
Clean component Specs
          ↓
Clean FormalEnsemble / channel balance / table soundness
          ↓
AcceptedZiskTrace-derived row and lane facts
          ↓
~12 instruction-shape theorems
          ↓
thin generated opcode instances
          ↓
root_soundness
```

The key changes are:

- **Make Clean `Spec`s the canonical circuit model.** The legacy `Airs/Valid_*` records should become generated compatibility views and ultimately disappear. Equivalence proofs should consume Clean component specifications directly rather than translating each opcode through bespoke `Bridge.lean` files.
- **Derive facts once at the accepted-trace seam.** Provider-row existence, component identity, row membership, exact entry matching, register lanes, pins, and memory rows should follow from ensemble soundness and channel balance. They should not be repeated as caller-supplied “promises” in every opcode theorem.
- **Factor by instruction shape, not opcode.** Create reusable families for R-type arithmetic, I-type arithmetic, shifts, branches, loads, stores, binary logic, multiplication, division, and similar shapes. Each family gets one evidence record and one canonical parametric theorem; individual opcode theorems become small instantiations.
- **Separate evidence from semantics.** A family evidence package should contain only trace-derived structural facts. The canonical family theorem combines that package with the relevant Clean `Spec` to prove the architectural transition. This makes dependencies visible and prevents large positional hypothesis lists.
- **Keep wrappers one-way and thin.** Compatibility wrappers may project old hypotheses into a family evidence package during migration, but canonical theorems must never depend on wrappers. Delete wrappers once callers move.
- **Treat caller-burden reduction as the progress metric.** A migration is complete only when premises have been derived from accepted-trace invariants—not merely renamed or bundled.

## Assessment of current Clean usage

The low-level Clean components are substantially idiomatic: they use `GeneralFormalCircuit`, `ProvableStruct`, `assertZero`, lookups, channel pushes, `FormalEnsemble`, and `TableSoundness`. The main divergence is **above** that layer: Clean facts are translated into a parallel legacy AIR model, then reconstructed through per-opcode bridges and large promise surfaces. Thus the best refactor is not to rewrite the circuits; it is to make their `Spec`s the proof spine.

The local Clean fork should also be reconciled deliberately with upstream work, especially zero-multiplicity channel handling and VM/ordered-channel soundness. The bespoke adjacent-row transition extension should either use Clean’s `InductiveTable` abstraction or be upstreamed rather than remain an undocumented fork divergence.

## Safe migration order

1. Keep the root theorem frozen and retain statement/axiom golden tests.
2. Add generic accepted-trace derivation lemmas at the ensemble seam.
3. Introduce one evidence package and canonical theorem per instruction shape.
4. Migrate opcode callers family by family, measuring removed explicit parameters.
5. Make Clean `Spec`s canonical and demote the legacy `Valid_*` model.
6. Remove obsolete bridges, wrappers, `OpEnvelope` duplication, and trust-ledger entries.
7. Only after the lower architecture stabilizes, optionally repackage existing root binders behind a proved old/new equivalence theorem.

The detailed, self-contained version is in `docs/refactor/FINAL-PLAN.md`; `docs/refactor/01-architecture-map.md` through `07-root-stability-and-upstream-clean.md` contain the supporting analysis. Some of this redesign is already implemented: the audit surface and completeness obligations record exist, and accepted-trace row/lane derivations plus several family migrations have begun. The remaining Shift, arithmetic, and load/store migrations require richer typed provider evidence rather than more opcode-specific premises.

# Summary of changes for run af154c69-dade-4a18-bbcf-9d542b3fdfc7
Installed the supplied source-of-truth snapshot and attempted all nine work-order items.

Implemented and verified:
- Added `ShiftProviderEvidence` in `ZiskFv/Compliance/SharedBundles.lean`.
- Proved `AcceptedZiskTrace.shiftProviderRowFacts` from the generic accepted-trace provider seam in `ZiskFv/Compliance/AcceptedZiskTrace/DerivedRowFacts.lean`.
- Preserved `root_soundness`, `root_completeness`, `ZiskFv/Audit.lean`, and every file under `trust/generated/` byte-for-byte.
- Confirmed the full build passes (9012 jobs).
- Confirmed source trust checks 1–12 and 14–16 pass; check 13 was deferred because the supplied snapshot omits the `zisk` submodule.
- Confirmed all semantic trust checks pass, running the final long witness groups separately after the aggregate script exceeded its execution window.
- Confirmed modified Lean sources contain no prohibited proof placeholders or declarations.

Prepending to `ARISTOTLE_SUMMARY.md`, I recorded:
- A status for every numbered item.
- Precise architectural blockers for unfinished family migrations.
- Before/after theorem-parameter counts covering prior RTYPE/ITYPE work and every family inspected here.
- Evidence-package design decisions and exact verification results.

The complete wrapper/canonical rollout was not achieved. Shift now has its evidence package and seam specialization, but its surface migration remains coupled to numerous exhaustive `OpEnvelope` consumers. ADD/ADDI require a typed Binary/BinaryAdd provider sum; arithmetic families require provider variants capable of deriving their dependent ArithMul/ArithDiv rows and primary/secondary matches; load/store routes remain tied to their Clean memory witnesses. No theorem was weakened and no new caller premise was introduced.

# Refactor 4 Phase 2.3/2.4 remainder — run summary (2026-07-17)

The supplied source-of-truth snapshot was installed before work began. This run attempted all nine numbered items. It added the BinaryExtension evidence shape and the accepted-trace provider specialization needed by the Shift family, but did not complete the requested wrapper/canonical migration. The remaining statuses below are deliberately reported as blocked/incomplete rather than overstated.

## Per-item status

| # | Family / task | Status | Result / precise blocker |
|---|---|---|---|
| 1 | Shift | **Blocked after seam/package implementation** | Added `ShiftProviderEvidence` in `ZiskFv/Compliance/SharedBundles.lean` and proved `AcceptedZiskTrace.shiftProviderRowFacts` in `ZiskFv/Compliance/AcceptedZiskTrace/DerivedRowFacts.lean`, selecting `shiftStaticLookupComponent` from `opProviderRowFacts`. A trial migration of the six 64-bit surfaces compiled in isolation, but changing the `OpEnvelope.sll/srl/sra/slli/srli/srai` constructor arities requires a simultaneous exhaustive update of pattern consumers in `Dispatch/Shift.lean`, `AeneasBridgeTrust/{Base,Shifts}.lean`, `TraceLevelExport/{StepStrongAluArith,Dispatcher,ProgramDecode,BootSegmentMemorySeed}.lean`, and all construction callers. The trial was reverted rather than commit a tree that broke exhaustive patterns. The six W-shift wrappers are not separate `Wrappers/<Op>.lean` declarations; their canonical and `OpEnvelope` surfaces are additionally coupled to the large `Dispatch/Remaining.lean` match. No hypothesis was added or claim weakened. Current counts remain below. |
| 2 | ADD_RTYPEW | **Blocked / unchanged** | Inspection confirmed two genuinely different providers for ADD/ADDI (`OpEnvelope.add_via_binary` uses static Binary; `add_via_binaryadd` uses BinaryAdd), while ADDW/ADDIW/SUBW use static Binary. A single component-equality package cannot type both alternatives; this needs a sum of a `StaticBinaryRTypeEvidence`-style package and a new BinaryAdd-dependent package, followed by simultaneous changes to `equiv_ADD_via_binaryadd`/`EquivCore.Add.equiv_ADD_of_binaryadd_row`, `OpEnvelope`, `Dispatch/ADD_RTYPEW.lean`, `Dispatch/Misc.lean`, and StepStrong callers. No caller premise was introduced and all surfaces remain unchanged. |
| 3 | DIVU | **Blocked / unchanged** | The work-order label “ArithMul provider specialization” does not match the actual canonical surface: `ZiskFv/Equivalence/Divu.lean:equiv_DIVU` and `Compliance/Wrappers/Divu.lean:equiv_DIVU_of_table` use `Valid_ArithDiv`, `opBus_row_ArithDiv`, `ArithDivTableWitness`, chunk/carry witnesses, and a remainder-bound witness. The generic seam’s first branch is expressed through `arithMulProviderComponent`, so deriving the exact `Valid_ArithDiv` row/index and all of these dependent witnesses is not a direct specialization of the existing `OpProviderRowBranch`. The surface was not weakened to hide this mismatch. |
| 4 | Remaining | **Blocked / unchanged** | `Dispatch/Remaining.lean` is not one provider family: it contains loads/stores, six W-shifts, five multiplication forms, seven signed/unsigned div/rem forms, and jumps. The M-extension canonicals depend on different primary/secondary Arith rows and distinct witness packages (examples: `equiv_MUL` 36 binders, `equiv_DIV` 30, `equiv_REMU` 22). The current four-way seam records only one primary Arith provider message and cannot derive secondary matches or the dependent `Valid_ArithDiv` row witnesses used by these theorem statements. Per-op provider variants are therefore required before safe surface shrinkage. |
| 5 | Misc | **Blocked / unchanged** | `Dispatch/Misc.lean` combines LB/LH/LW memory-provider routes with ADDI’s Binary/BinaryAdd alternatives and ADDIW’s static-Binary route. The load arms’ provider data is tied to `LdCleanWitness`/full-ensemble memory message equality, not `OpProviderRowFacts`; ADDI has the same two-provider sum issue as item 2. No common evidence package can faithfully type all arms. |
| 6 | NoMemOrSimple | **Attempted; no listed provider binders to remove** | `Dispatch/NoMemOrSimple.lean` covers LUI, AUIPC, AUIPC-x0, and FENCE. These arms have no `providerTable`, `providerRow`, component/spec, provider membership, provider match, or rd-lane binders. Their `MainRowPins` are semantically opcode/control pins and no operation-bus provider row exists for the no-memory forms. No change was appropriate under the item’s provider-specialization recipe. |
| 7 | LDSD | **Blocked / unchanged** | The canonical LD/SD surfaces already have no loose provider table/row/component/spec/match or rd-lane binders: they consume `LdCleanWitness`/`SdCleanWitness`. The remaining `MainRowPins main r_main 0 OP_COPYB` can be obtained from accepted decode facts, but canonical theorem scope has no `AcceptedZiskTrace`; moving it out requires changing the `OpEnvelope` constructors and all load/store dispatch/trace callers together. Memory timeline facts remain inside the Clean witnesses and were intentionally not forced into the generic operation-bus seam. |
| 8 | Cleanup | **Done: nothing deletable yet** | A zero-consumer search found every `main_request_*_provided` declaration still has live consumers. In particular, `main_request_shift_provided` has callers in `ConstructionShift.lean` and `TraceLevelExport/StepStrongAluArith.lean`; add/logic/compare/W/div/rem helpers likewise remain consumed. Therefore no balance-rebuild lemma or loose helper was deleted prematurely. |
| 9 | Final sweep | **Done for the resulting tree; rollout incomplete** | Full build and all available trust checks pass as recorded below. Protected roots, audit file, and `trust/generated/` are byte-identical to the supplied snapshot. The parameter table records both the prior accepted RTYPE/ITYPE migration and every family inspected in this run. |

## Explicit theorem-parameter counts

Counts are individual explicit parameters on the named wrapper/canonical declaration. “Unchanged” means this run did not complete that family’s surface migration.

| Family / theorem(s) | Wrapper before → after | Canonical before → after |
|---|---:|---:|
| Prior RTYPE: `equiv_SUB`, `equiv_AND`, `equiv_OR`, `equiv_XOR`, `equiv_SLT`, `equiv_SLTU` | 19 → 10 | 19 → 10 |
| Prior ITYPE: `equiv_ANDI`, `equiv_ORI`, `equiv_XORI` | 20 → 14 | 20 → 14 |
| Prior ITYPE compare: `equiv_SLTI`, `equiv_SLTIU` | 19 → 13 | 19 → 13 |
| Shift64: `equiv_SLL`, `equiv_SRL`, `equiv_SRA`, `equiv_SLLI`, `equiv_SRLI`, `equiv_SRAI` | 19 → 19 | 19 → 19 |
| ShiftW register: `equiv_SLLW`, `equiv_SRLW`, `equiv_SRAW` | no separate wrapper | 19 → 19 |
| ShiftW immediate: `equiv_SLLIW`, `equiv_SRLIW`, `equiv_SRAIW` | no separate wrapper | 18 → 18 |
| ADD static route: `equiv_ADD` | 19 → 19 | 19 → 19 |
| ADDI static route: `equiv_ADDI` | 20 → 20 | 20 → 20 |
| W-add: `equiv_ADDW`, `equiv_ADDIW`, `equiv_SUBW` | 19 → 19 | 19 → 19 |
| DIVU: `equiv_DIVU_of_table` / `equiv_DIVU` | 22 → 22 | 22 → 22 |
| Remaining MUL: `equiv_MUL`, `equiv_MULH`, `equiv_MULHU`, `equiv_MULHSU`, `equiv_MULW` | 36/34/33/34/23 unchanged | 36/34/33/34/23 unchanged |
| Remaining DIV/REM: `equiv_DIV`, `equiv_REM`, `equiv_REMU`, `equiv_DIVW`, `equiv_DIVUW`, `equiv_REMW`, `equiv_REMUW` | 29/28/22/37/25/36/27 unchanged | 30/29/22/38/25/37/25 unchanged |
| Misc loads: `equiv_LB`, `equiv_LH`, `equiv_LW` | 16 → 16 | 16 → 16 |
| LDSD: `equiv_LD`, `equiv_SD` | canonical compatibility wrappers 10/10 unchanged (`Sd.lean` also has a 28-parameter full-ensemble constructor) | 10 → 10 each |
| Remaining loads: `equiv_LBU`, `equiv_LHU`, `equiv_LWU` | 12 → 12 | 12 → 12 |
| Remaining stores: `equiv_SB`, `equiv_SH`, `equiv_SW` | canonical compatibility wrappers 11 each unchanged (full-ensemble constructors are 37/36/34) | 11 → 11 each |
| NoMemOrSimple: `equiv_LUI`, `equiv_AUIPC`, `equiv_FENCE` | canonical wrappers 16/8/12 unchanged (LUI wrapper file also has a 16-parameter construction theorem) | 16/8/12 unchanged |
| Remaining jumps: `equiv_JAL`, `equiv_JALR` | canonical wrappers 8/28 unchanged | 8/28 unchanged |

## Evidence-package design

- Prior accepted RTYPE: dependent `StaticBinaryRTypeEvidence`, including provider identity/row/spec/match, two operand bindings, Main pins, and destination lane.
- Prior accepted ITYPE: `StaticBinaryProviderEvidence`, retaining opcode-specific immediate/subset bindings outside the common provider package.
- Shift design added here: dependent `ShiftProviderEvidence`, parameterized by Main row, bus, opcode, input A, and natural shift amount. It packages the BinaryExtension table/row/component/spec/match, input-A binding, shift-amount binding, Main pins, and destination lane.
- ADD/ADDI require a provider sum (static Binary versus BinaryAdd); W-add can reuse a static-Binary dependent package with 32-bit extraction fields.
- Arith families require distinct primary/secondary and ArithMul/ArithDiv evidence variants; the current generic provider branch is insufficient for the dependent validator/index witnesses.
- Loads/stores should retain their existing Clean memory witness packages; only accepted-trace caller-side pin assembly is common with the operation families.

## Verification

- `lake build`: **passed**, 9012 jobs, including `ZiskFv/Audit.lean`.
- Source trust checks: **1–12 and 14–16 passed**; check 13 was deferred exactly as authorized because the supplied snapshot omits the `zisk` submodule.
- Semantic trust checks: checks **1–13 passed** in the aggregate run; checks 14–16 were then run directly and passed (all Clean completeness witnesses; register MemBus witness; 824 extraction/decode raw closures). The aggregate script exceeded the execution window while replaying the long witness suite, not because of a reported failing check.
- `ZiskFv/Soundness.lean`, `ZiskFv/Completeness.lean`, and `ZiskFv/Audit.lean`: SHA-256 unchanged from the installed snapshot.
- `trust/generated/`: byte-for-byte unchanged.
- Modified Lean sources contain no `sorry`, `admit`, `native_decide`, `opaque`, `partial`, or `implemented_by`.

# Summary of changes for run 8e2b9014-647a-42e6-ba5a-db6d87f489b2
Implemented and verified a substantial partial Phase 2.3/2.4 refactor, with the exact per-item status recorded at the top of `ARISTOTLE_SUMMARY.md`.

Completed:
- Replaced the working tree with the supplied source-of-truth snapshot.
- Shrunk all SUB/AND/OR/XOR/SLT/SLTU RTYPE wrapper and canonical surfaces using `StaticBinaryRTypeEvidence`.
- Shrunk all ANDI/ORI/XORI/SLTI/SLTIU ITYPE wrapper and canonical surfaces using `StaticBinaryProviderEvidence`.
- Updated the corresponding construction and dispatch callers.
- Added `AcceptedZiskTrace.staticBinaryCompareProviderRowFacts` and migrated SLT/SLTU strong exports away from rebuilding channel balance.
- Confirmed branch wrappers have none of the targeted provider/pin/lane binders.

Verification:
- Full `lake build` passes (9012 jobs), including the unchanged audit golden tests.
- Semantic trust gate passes all 16 checks, including 824 extraction/decode closure checks.
- Source trust checks 1–12 and 14–16 pass; check 13 is precisely blocked by the supplied snapshot omitting `zisk/core/src/aeneas_extract.rs`, as anticipated by the work order.
- `trust/generated/`, root theorem files, audit surface, and build pins remain unchanged.
- Changes are committed and pushed.

The requested all-family rollout was not completed: Shift, ADD_RTYPEW, DIVU, Remaining, Misc, NoMemOrSimple, LDSD, and final dead-helper cleanup remain. `ARISTOTLE_SUMMARY.md` reports these honestly as not reached and includes the completed per-theorem before/after parameter counts and design choices.

# Summary of changes for refactor-3 Phase 2.3/2.4 continuation (2026-07-16)

This run made a verified partial implementation of the 12-item work order. It did **not** complete the full requested roll-out; the uncompleted items are called out explicitly rather than being represented as done.

## Per-item status

| # | Family / task | Status | Detail |
|---|---|---|---|
| 1 | RTYPE | **Done for SUB/AND/OR/XOR/SLT/SLTU** | Added one dependent static-Binary evidence package; all eight seam-derived loose arguments (`providerTable`, `providerRow`, component/spec/row/match, pins, rd lane) are now one package on the six wrapper and canonical surfaces. Updated construction and dispatch callers. Added and consumed `staticBinaryCompareProviderRowFacts`; SLT/SLTU no longer rebuild balance through `main_request_compare_provided`. ADD remains owned by item 4. |
| 2 | ITYPE | **Done for ANDI/ORI/XORI/SLTI/SLTIU** | Added a common static-Binary provider evidence package; removed the seven common provider/pin/lane binders from all five wrappers and canonicals while retaining genuine opcode-specific input/immediate facts. Updated construction and dispatch callers. |
| 3 | Shift | **Not reached** | The twelve BinaryExtension wrappers still expose the listed provider/pin/lane arguments. No statement was weakened and no replacement premise was added. |
| 4 | ADD_RTYPEW | **Not reached** | ADD/ADDI/ADDW/ADDIW/SUBW and their BinaryAdd/static-Binary alternatives remain unchanged. |
| 5 | DIVU | **Not reached** | The ArithMul specialization and DIVU surface migration remain outstanding. |
| 6 | Remaining | **Not reached** | M-extension and other `Dispatch/Remaining.lean` surfaces remain unchanged. |
| 7 | Misc | **Not reached** | No Misc-family wrapper signatures were changed. |
| 8 | NoMemOrSimple | **Not reached** | No NoMemOrSimple-family wrapper signatures were changed. |
| 9 | Branch | **No applicable listed binders found** | The six branch wrappers use `BranchInstrOperands` and `BranchPromises`; they do not expose `providerTable`, `providerRow`, component/spec/match, rd lane, or `MainRowPins`. EquivCore nextPC was untouched. |
| 10 | LDSD | **Not reached** | No load/store timeline binder was forced or removed. |
| 11 | Cleanup | **Not reached** | No `main_request_*` theorem was deleted. Existing consumers remain and require a later zero-consumer sweep after the remaining migrations. |
| 12 | Final sweep | **Partial** | Full build and all available trust checks pass as detailed below; the requested all-family parameter table cannot honestly be marked complete because items 3–8 and 10–11 remain. |

## Parameter counts (individual explicit theorem parameters)

The design choice for completed families was **(a)**: each wrapper consumes one dependent evidence package. The package is assembled by existing trace/construction callers; no new independent proposition or trust marker was introduced.

| Theorem(s) | Before | After | Change |
|---|---:|---:|---:|
| `equiv_SUB`, `equiv_AND`, `equiv_OR`, `equiv_XOR`, `equiv_SLT`, `equiv_SLTU` (wrapper and canonical each) | 19 | 10 | −9 |
| `equiv_ANDI`, `equiv_ORI`, `equiv_XORI` (wrapper and canonical each) | 20 | 14 | −6 |
| `equiv_SLTI`, `equiv_SLTIU` (wrapper and canonical each) | 19 | 13 | −6 |

The RTYPE package includes the two operand-row equalities because those have a uniform type. The ITYPE package intentionally stops at provider selection/pins/rd-lane; immediate routing and Main subset facts remain explicit genuine per-opcode data.

## New reusable facts and structures

- `StaticBinaryProviderEvidence`
- `StaticBinaryRTypeEvidence`
- `AcceptedZiskTrace.staticBinaryCompareProviderRowFacts`

## Verification

- `lake build`: **passed**, 9012 jobs; this includes the untouched `ZiskFv/Audit.lean` golden tests.
- `trust/scripts/check-all.sh`: checks **1–12 and 14–16 passed**. Check 13 alone could not execute because the delivered snapshot has no `zisk/core/src/aeneas_extract.rs`, exactly the pre-authorized snapshot limitation.
- `trust/scripts/check-all-semantic.sh`: **all 16 checks passed**, including all 824 extraction/decode raw closures.
- `trust/generated/`: byte-for-byte unchanged.
- `ZiskFv/Audit.lean`, both root theorem source files/statements, build pins, and lockfiles: untouched.
- Modified proof sources contain no `sorry` or `admit`.

# Summary of changes for run 3b98c185-02f3-4cec-bed7-a7d0f8803d23
Continued the Phase 2 accepted-trace ensemble-seam refactor without changing either root theorem or its trust surface.

### Implemented
- Added and proved `AcceptedZiskTrace.staticBinaryLogicProviderRowFacts` in `ZiskFv/Compliance/AcceptedZiskTrace/DerivedRowFacts.lean`.
  - It handles the AND/OR/XOR shape family once at the accepted Clean ensemble seam.
  - Generic channel-balance row selection comes from `opProviderRowFacts`.
  - Impossible ArithMul, BinaryExtension, and BinaryAdd branches are eliminated only in the shape specialization.
  - The surviving static-Binary row carries table/row membership, component identity, table `Spec`, and exact operation-bus matching.
- Migrated all six AND/OR/XOR strong-export paths in `StepStrongAluArith.lean`—both register and immediate forms—to this seam fact instead of rebuilding balance through `main_request_logic_provided`.
- Added the direct `SharedBundles` import required by the derived-row-facts module, removing reliance on accidental transitive imports.

### Verification
- Full `ZiskFv` build succeeds: 9012 jobs.
- The modified files contain no `sorry` or `admit`.
- `staticBinaryLogicProviderRowFacts` has only the permitted standard axiom closure: `propext`, `Classical.choice`, and `Quot.sound`.
- Trust checks 1–12 and 14–16 pass. Check 13 cannot run in this submitted snapshot because the external source file `zisk/core/src/aeneas_extract.rs` is absent; this is unrelated to the Lean changes.
- All changes are committed and pushed. Working tree is clean.

# Summary of changes for run 322f340e-cba5-4f1f-881e-93544a29889c
Implemented the Phase 2 ensemble-seam refactor and committed it as `66ca240` (`Derive row facts at accepted trace seam`). `ARISTOTLE_SUMMARY.md` was not modified.

### Changes
- Added `ZiskFv/Compliance/AcceptedZiskTrace/DerivedRowFacts.lean`, providing reusable, proof-derived accepted-trace facts:
  - `OpProviderRowBranch` / `OpProviderRowFacts`: an opcode-independent four-way classification of the concrete operation-bus provider row, including row membership, component identity, Clean row `Spec`, and exact entry matching.
  - `AcceptedZiskTrace.opProviderRowFacts`: derives those provider facts from the accepted trace’s constraints, channel balance, and table soundness.
  - `AcceptedZiskTrace.staticBinarySubProviderRowFacts`: the R-type SUB pilot specialization, eliminating impossible provider branches only after consuming the generic ensemble-seam fact.
  - `AcceptedZiskTrace.registerWriteLanes`: derives the Main register-write lane relation once for any indexed arithmetic Main row.
- Migrated the SUB strong-export path to the new generic provider fact rather than directly rebuilding the balance argument through `main_request_sub_provided`.
- Migrated all 28 repeated register-write-lane derivations in `StepStrongAluArith.lean` to `trace.registerWriteLanes`, deleting 674 lines of duplicated row-selection and transport proofs.
- Exported the new accepted-trace fact module from `ZiskFv.lean`.

This is a T0 refactor: no root theorem statement or trust premise changed.

### Verification
- Full `ZiskFv` build succeeds: 9010 jobs.
- The modified files contain no `sorry` or `admit`.
- All three new principal theorems have only the permitted standard axiom closure: `propext`, `Classical.choice`, and `Quot.sound`.
- The complete source-level trust gate passes all 16 checks.
- The semantic trust checks pass through the project checks; the final extraction-closure check was also run separately and passed for all 824 declarations. The combined script’s only failure was that the submitted snapshot did not preserve executable bits on its nested scripts, not a Lean or trust failure.
- Working tree is clean.

# Summary of changes for run 65f24360-d87a-426f-b91a-b4a3491a5435
I investigated the review's critique against the actual code and confirmed it is correct. I then corrected the affected plans.

## What I checked (and found)
The critique says §4.1 of the refactor plan rests on a stale premise: it treated `aeneasBridgeTrust` and `memoryTimelineConstructionEvidence` as "hidden trust" living in internally-built `OpEnvelope` fields, and proposed lifting them into a root trust binder. Verifying against the source:

- **They are discharged, not outstanding.** `ZiskFv/Compliance/TraceLevelExport/StepStrongAluArith.lean:223` proves `env.aeneasBridgeTrust` from the derived accepted-trace row facts (`h_input_r1_row`/`h_input_r2_row`), and `env.memoryTimelineConstructionEvidence` is `trivial` on non-load arms; for load arms it is `bootSeed`-derived (via `LoadMemoryTimelineCoherenceEvidence`). `OpEnvelope.memoryTimelineConstructionEvidence` is literally `True` for every non-load arm.
- These two fields are hypotheses of the **internal** lemma `zisk_riscv_compliant_program_bus`, not of `root_soundness`. `ZiskFv/Compliance/TraceLevelExport.lean` documents the three discharge routes and states plainly that these obligations are discharged in place.
- **The frozen axiom closure confirms it.** `ZiskFv/Audit.lean`'s `#print axioms root_soundness` golden test shows only the trusted Sail-extraction primitives plus the standard permitted axioms — no `sorryAx`, no extra trusted premise hiding in a constructed value.
- The confusion traces to the C3 doc drift the plan itself diagnosed; the pre-Phase-0.3 `trust/trusted-base.md` described the internal lemma (where they genuinely are hypotheses). That doc is already fixed and needed no further change.

## Conclusion
The critique is right. Adding these as root binders would **weaken** `root_soundness` by re-introducing premises the proof currently earns. The legitimate remainder of the §4.1 move is only the **T1 bundling** of binders that already exist on the root (`inputsAgree`, `bootSeed`, and the scope binder) into one record for readability — `channels_balanced` is already inside `AcceptedZiskTrace`, so it is not a new binder either.

## What I changed (docs only, no proof code touched)
I dropped the "lift hidden trust (T2)" component from §4.1 and made the surrounding text consistent across the plan set, adding an explicit correction note and pointing at the code/axiom-closure evidence:
- `docs/refactor/FINAL-PLAN.md` — §2.3 (corrected consequence + a "Correction note"), §4.1 (removed the `aeneasBridge`/`channelsBalanced` fields from the proposed `SoundnessTrust` record; reclassified as a single T1 move), §6.3, §7, the Phase-1 roadmap step, the effort/risk table (`T1 (+ optional T2)` → `T1`), the §5 residual line, the S1 headline, and the request-mapping table.
- `docs/refactor/01-architecture-map.md` §1.3, `03-root-theorem-api.md` (rule 2, the record sketch, benefits), `05-inconsistencies-and-correctness.md` (T1 row), `06-roadmap.md` (step 1.1), `07-root-stability-and-upstream-clean.md` (A.1/A.2), and `docs/refactor/README.md` (R1).

`ARISTOTLE_SUMMARY.md` was left untouched. All changes are committed and pushed to `main`.

# Summary of changes for run db5a1315-b78b-4801-b149-a85979b0c83e
Implemented **Phase 0** and **Phase 1.3** from `docs/refactor/FINAL-PLAN.md` (the "suggested first PR"). All changes build (full `ZiskFv` target compiles cleanly, 9009 jobs) and are committed and pushed to `main`.

## Phase 1.3 — completeness API symmetry (`ZiskFv/Completeness.lean`)
- Added a `ZiskCompletenessObligations z` record bundling the five previously-loose obligation binders (`decoderAcceptsInShape`, `loweringTotal`, `rowTotal`, `opcodeTotal`, `soundnessContract`), the completeness analogue of a single trust record.
- Renamed `skeletal_root_completeness → root_completeness`, now taking that one record instead of five separate hypotheses (proof preserved, still honestly conditional). Its axiom closure is the standard allowed set only.
- Propagated the rename through every remaining reference (docstrings in `ZiskFv/Completeness/Aspirational/*`, `README.md`, `trust/README.md`, `trust/defects.md`, `docs/ai/*`). No trust-gate baseline referenced the old name.

## Phase 0 — docs & audit surface (no proof risk)
- **0.2 — new `ZiskFv/Audit.lean`** (imported from `ZiskFv.lean`): the single audit surface. It re-states nothing new but gathers, in reading order, `root_soundness`, `root_completeness`, and the proven `sail_executable_within_supported_decode_shape`, and freezes each as golden tests: a pretty-printed `#check` statement snapshot and a `#print axioms` closure, both under `#guard_msgs (whitespace := lax)`. Any stray `sorry` or newly introduced trusted premise below either root now breaks the build. It also points at `trust/trusted-base.md` and `trust/defects.md`.
- **0.1 — fixed doc/code drift C1–C5:**
  - C1/C2 `ZiskFv/EquivCore/README.md`: corrected the wrong title (was "`ZiskFv/Equivalence/`") and rewrote it to describe `EquivCore/` (the `execute = bus_effect` core theorems) with the correct bottom-up dependency direction `EquivCore → Wrappers → Equivalence`.
  - C2/C4/C5 `ZiskFv/Compliance/README.md`: fixed the inverted wrapper/canonical dependency sentence, replaced hard-coded opcode counts with "read the tree", and corrected the "sum type … to dispatch" framing (the `OpEnvelope.exec_eq` conclusion is a `True`-padded conjunction, not a case-returning dispatch). Also noted `zisk_riscv_compliant_program_bus` is internal and `root_soundness` is the endpoint.
- **0.3 — `trust/trusted-base.md`**: the Claim section now names `ZiskFv.Compliance.root_soundness` (and the `ZiskFv/Audit.lean` surface) as the advertised endpoint, and labels `zisk_riscv_compliant_program_bus` as the internal per-arm channel-balance lemma.

No theorem's trust surface was changed; `root_soundness` is byte-for-byte unchanged (verified via the frozen axiom/statement golden tests). `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run b5c2364e-1f9d-43a4-8a4f-46079c9f14b5
I folded the full architecture review into a single, self-contained final plan/overview and wired it in as the top-level entry point.

## What I added
- **`docs/refactor/FINAL-PLAN.md`** — one comprehensive document that consolidates the entire review (the `README` plus docs `01`–`07`) into a single narrative you can read top-to-bottom. Its ten sections are:
  1. The engagement in one paragraph.
  2. Headline conclusions (the Clean seam is more idiomatic than feared; the problems S1–S5 sit *above* it; nothing proposed weakens a theorem or grows trust).
  3. Architecture as-is — mass distribution, the data-flow pipeline, the two stacked root theorems, per-opcode multiplicity, and the inverted dependency direction.
  4. Clean idioms — the north star, what the project already does right, an idiomatic-Clean scorecard, and the four divergences D1–D4 to fix.
  5. Top-level theorem API redesign — one `SoundnessTrust`/`SoundnessScope` record so the TCB is visible in the type, demoting the old global theorem to an internal per-arm lemma with dependent-match dispatch, symmetric `root_completeness`, and one `Audit.lean`.
  6. Proof-architecture refactor — R2 (make Clean the spine, retire the `Airs/` records), R4 (derive facts at the ensemble seam), R3 (factor per shape, not per opcode), R5 (idiomatic dispatch), reusable abstractions, and file-size hygiene.
  7. Inconsistencies and correctness-adjacent smells (C1–C5, naming hazards, trust-visibility T1–T4, review gates Q1–Q4).
  8. Root-statement stability — the T0/T1/T2 change-tier discipline, the equivalence-bridge protocol, and the `#print axioms` golden test that make the refactor safe.
  9. Upstream-Clean status and tracking policy (fork base, the 6 local patches, ranked incoming PRs including #398, the `Vm.lean` overhaul, autoelaborate, Lean 4.29, witgen-ir).
  10. The sequenced, build-green, trust-monotone roadmap (Phases 0–5) with an effort/risk table, plus a mapping back to your original request and to the existing `simplification-suggestions.md`.

- **`docs/refactor/README.md`** — added a "Start here" pointer and an index row so `FINAL-PLAN.md` is the clear front door; the numbered documents remain as the detailed backing.

No proof code was changed (this is documentation/planning, as before). Everything is committed and pushed to `main`; the working tree is clean.

# Summary of changes for run eaad5f5a-e5a5-436b-b7f8-ab0a2c770e10
You're seeing a git-history artifact, not an old checkout. Here's what actually happened, based on inspecting the repo you received.

## What the returned repo looks like
The repo has exactly one commit:
- `2224b0e "Initial commit"`, authored `Aristotle <aristotle@harmonic.fun>`, dated today (2026-07-14), working tree clean.

There is no other history. Notably, even the internal commit `71d192b` that the previous run's `ARISTOTLE_SUMMARY.md` says it "committed and pushed to main" does **not** exist in what you got back. In other words, the returned repository was flattened into a single fresh snapshot commit that shares **no common ancestry** with your branch.

## Why it *looks* two weeks old (but isn't)
Because the returned snapshot has no shared history with your repo, git can't find the true merge-base when you compare/merge/rebase it against your branch. It falls back to the nearest commit whose **content** overlaps. Since your recent commits (including the build-structure change) aren't present as ancestors, the closest content match surfaces as "a commit ~two weeks old." That ancestry is an illusion produced by the history being squashed on the way back to you — it is not evidence that an old checkout was used.

## The content is NOT stale — your build-structure change IS present
I confirmed the returned working tree contains exactly the build structure you added to make the CLI launch the run:
- `lakefile.toml` explicitly documents the immutable-git-package inputs and says "Lake and Aristotle consume this exact commit directly," and wires up `ZiskFvLeanInputs`, the `Clean` fork, `ProductionM2` (`trust/aeneas`), and the `TrustGate` lib/exe.
- `flake.nix` defines the `aristotle-inputs-src` input and states "Lake and Aristotle consume it by the same immutable Git commit; CI checks it is byte-for-byte the output of packages.aristotle-inputs."
- `scripts/check-aristotle-inputs.sh` and `scripts/sync-aristotle-inputs.sh` are present.
- The previous run's actual deliverables are all present and match the summary: `docs/refactor/01..07` plus `README.md` (doc 07 = root-stability + upstream-Clean analysis).

So the run genuinely operated on the branch you sent, with your new build structure — the CLI succeeded precisely because that structure was in place. What came back is a squashed single-commit snapshot of that work; only the git history was lost, not the content.

## Two things worth double-checking on your side
1. The returned work is (per the prior summary and the files present) **documentation/plans only** — no proof code was changed. If you expected code changes, that matches the earlier "no code changes, as requested" scope, not a lost/old build.
2. To be fully certain nothing in the build wiring regressed, diff these between your branch tip and the returned tree: `lakefile.toml`, `flake.nix`, `flake.lock`, `lake-manifest.json`, and `scripts/*aristotle*`. You should find them identical (or only your intended changes).

## How to reconcile it cleanly
Don't rely on ancestry-based merge. Options:
- Treat the returned tree as a snapshot: check out your branch and overlay the returned files (e.g. copy in the new/changed files — chiefly everything under `docs/refactor/` and `docs/clean-fork-divergences.md`), then commit on top of your branch so your history is preserved.
- Or add the returned repo as a remote and `git merge --allow-unrelated-histories`, resolving conflicts, which keeps your branch history and layers the new docs on top.
- Use `git diff --no-index <your-branch-tree> <returned-tree>` to see the true content delta regardless of history.

Bottom line: the agent worked on your correct, new-build-structure branch; the "two-week-old base commit" is a side effect of the returned repo being a single squashed snapshot with no shared history, not a sign that outdated code was used.

# Summary of changes for run 0d7220f8-6f22-4d00-9646-6abb6f4de92c
I addressed both sanity-check concerns and folded the answers into the plan. No proof code was changed; the work is a new plan document plus an index update, committed and pushed to `main` (see `docs/refactor/07-root-stability-and-upstream-clean.md`, referenced from `docs/refactor/README.md`).

## 1. Keeping the root statement stable (Part A of doc 07)

You're right that the earlier plan (doc 03/R1) was too casual about editing `root_soundness`. The revised, principled approach:

- **A change-tier discipline.** Every proposed change is classified: **T0** = strictly *below* the root, the root's type is byte-for-byte unchanged (this is the default, and ~95% of the real work); **T1** = re-package existing binders only (allowed *only* behind a machine-checked equivalence proof); **T2** = actually change what is claimed or trusted (rare, isolated, its own reviewed PR, must shrink not grow the TCB).
- **The two changes you care about most — collapsing the ~63× per-opcode multiplicity and making Clean the spine — are 100% T0 and need no root change at all.** So the high-risk structural work all happens under a frozen root.
- **The root moves last, once, and provably.** Do all T0 work first; add the audit surface early; only then, if still desired, reskin the root as a T1 change behind an `old ↔ new` equivalence-bridge theorem; treat lifting hidden trust to root binders as an optional, clearly-flagged T2 step that can be deferred indefinitely.
- **Mechanical guards make accidental drift impossible:** a `#print axioms root_soundness/root_completeness` golden test under `#guard_msgs`, plus a committed statement snapshot, so any unintended root change fails the build rather than relying on review. Net: the root is untouched through the whole risky portion and simplifies below it, exactly as you asked.

Where this conflicts with the sequencing in docs 03/06, doc 07 supersedes them.

## 2. Upstream Clean (Part B of doc 07)

Yes — I examined upstream `Verified-zkEVM/clean` directly and pinned the fork precisely by content (the vendored copy was committed as a squashed "Initial commit" with no history):

- **Fork base ≈ mid-May 2026** (around upstream `main` ~`2de99379`, the PR #384 / sha256 era). Upstream `main` HEAD is `1e563b9c` (2026-07-06) — about two months and ~16 merged PRs ahead.
- **The fork carries only 6 locally-modified Clean files.** The two load-bearing ones: (a) `Air/Balance.lean`, patched to tolerate zero-multiplicity (padded) channel rows, and (b) `Air/FlatComponent.lean`/`FlatEnsemble.lean`, which add a bespoke adjacent-row `transition` field. The rest are cosmetic.
- **Incoming PRs of interest, ranked:**
  1. **#398 `fix-zero-multiplicity-channels`** (highest priority) — upstream solved *the same problem* the fork patched locally in `Balance.lean`, differently and more generally. The two overlap and will conflict on merge; adopt upstream's version and delete the local patch. This matters because channel balance is exactly the seam the proof-architecture refactor wants to derive facts from.
  2. The **`Air/Vm.lean` / `OrderedChannel.lean` overhaul** (~+400 lines) — this is the ensemble/channel-soundness machinery the review flagged as barely used; read it *before* re-proving `provider_row_facts` locally, since some of it may now exist upstream.
  3. **#375 `autoelaborate` + #425 `elaborate-circuit-parametric`** — big circuit-elaboration improvements relevant to writing components idiomatically with less boilerplate.
  4. A **new `Circuit/Formal.lean`** consolidating the `FormalCircuit`/`GeneralFormalCircuit` API the whole `AirsClean/` layer sits on — the main mechanical re-base cost.
  5. **#370 bump to Lean 4.29** — upstream is on 4.29; this project is on 4.28, so a re-base past this point forces a coordinated toolchain+mathlib bump. Recommendation: stop the re-base just before 4.29 and bump separately.
  6. **witgen-ir (#403/#413)** — a new verified witness-generation/extraction IR; not needed for soundness/completeness but worth tracking as a future extraction capability.
- **One extra finding:** the fork's local `transition` field duplicates capability upstream already offers at the `Table` layer via `InductiveTable`. Worth resolving (use `InductiveTable`, or upstream the field) rather than maintaining a silent divergence.

Suggested Clean-tracking policy (in doc 07 §B.5): adopt #398 now as an isolated well-tested step; read the current `Vm.lean` before the derive-at-seam work; settle the transition-constraint story; defer the full re-base past Lean 4.29 until the structural work is done. Importantly, **none of this touches the root theorems** — upstream alignment is all T0 from the project's side, so staying current with Clean and keeping the root stable are fully compatible.

# Summary of changes for run 91b6fca9-d7d2-42b5-8624-0b3e49bc31a2
I delivered a comprehensive, code-grounded architecture review and refactor plan (no code changes, as requested) under `docs/refactor/`, committed and pushed to `main`. It's built from a read of `ZiskFv/`, the vendored `Clean` package, and `trust/`.

**Documents (start at `docs/refactor/README.md`):**
- `README.md` — executive summary, top-10 findings, and the three highest-leverage recommendations.
- `01-architecture-map.md` — the as-is layer cake, mass distribution, the two stacked root theorems, and the ~7–9 near-parallel per-opcode layers.
- `02-clean-idioms-and-usage.md` — upstream Clean idioms vs project usage, with an idiomatic-Clean scorecard.
- `03-root-theorem-api.md` — concrete redesign of `root_soundness`/`root_completeness` (Lean sketches).
- `04-proof-architecture-refactor.md` — the structural refactor (one circuit model, per-shape factoring, deriving facts at the ensemble seam, reusable abstractions).
- `05-inconsistencies-and-correctness.md` — a located checklist of doc/code drift and correctness-relevant smells.
- `06-roadmap.md` — a sequenced, build-green, trust-monotone plan with effort/risk and exit criteria.

**Key findings.** The two seams that matter most are actually idiomatic Clean: per-component circuits are real `GeneralFormalCircuit`s with `ProvableStruct` rows and `circuit_proof_start`, and the full circuit is a `FormalEnsemble` whose per-table specs are derived from constraints + channel balance (`AcceptedZiskTrace`). The real problems sit above that seam:
1. Two stacked soundness statements — the advertised `root_soundness` (per-step, over `AcceptedZiskTrace`) is implemented by constructing `OpEnvelope` arms and invoking the older `zisk_riscv_compliant_program_bus`, so the trusted premises are split between the theorem's binders and internal `OpEnvelope` fields (`aeneasBridgeTrust`, memory-timeline evidence) that are invisible in its type.
2. Two parallel circuit models — a legacy record model (`Airs/`, `Valid_Main` referenced by ~299 files) bridged per-opcode into the Clean components, so the idiomatic layer is a tributary rather than the spine.
3. ~63 opcodes × 7–9 near-identical layers (`Airs`, `AirsClean`, `EquivCore`, `Equivalence`, `Compliance/Wrappers`, `Compliance/Construction*`, `OpEnvelope`, `TraceLevelExport`).
4. A bespoke promise/caller-burden/forbidden-shape trust discipline standing in for facts that Clean's ensemble soundness (`Vm.lean`/`OrderedChannels.lean`, used in ~0 files) is designed to derive.
5. Documentation that contradicts the code (e.g. `EquivCore/README.md` actually documents `Equivalence/`; the wrapper/canonical dependency direction is inverted vs the code; `trust/trusted-base.md` names the old theorem as "the global theorem" while READMEs name `root_soundness`).

**Top recommendations.** R1: unify to a single advertised soundness endpoint with one `SoundnessTrust`/`SoundnessScope` record so the whole TCB is visible in the type; make completeness symmetric (`root_completeness` + one obligations record) and add a single `Audit.lean` audit surface. R2: make the Clean component `Spec`s the spine and retire the `Airs` record model + per-opcode bridges. R3: factor per-*shape* (~12 families) instead of per-opcode, deriving provider/lane/pin facts once from channel balance. The roadmap sequences these to keep the build green and the trust ledger monotonically shrinking. The plan extends (and partly supersedes) the existing tactical `simplification-suggestions.md`, which it cross-references.

All work is committed (commit `71d192b`) and pushed; the working tree is clean.