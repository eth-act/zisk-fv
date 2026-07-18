# Refactor 11 report

## Installation

The authoritative tarball was overlaid non-destructively while preserving `.lake` and build artifacts. All 832 regular archive files compared byte-for-byte immediately after extraction with zero mismatches. The attached tarball was not committed.

## Item status

1. **ArithMul mirror: completed at the circuit-operation level.** `ArithMul.mainComplete` in `ZiskFv/AirsClean/ArithCompleteConstraints.lean` extends the established lookup-aware circuit with exact generated mirrors for constraint 2 and constraints 40–45. Constraint 46 was already present in `mainWithArithTable`. `ModeSpec` records the corresponding consumer-facing proposition. The existing `FullSpec` tuple shape was deliberately preserved to avoid changing callers before migration.
2. **ArithDiv mirror: completed at the circuit-operation level.** `ArithDiv.mainComplete` adds exact generated mirrors for constraints 0–5, 9–30, and 39–48. `ArithDivAux.inv_sum_all_bs` adds the missing generated witness column, and row/constant builders were updated. Existing lookup-aware tuple shapes were preserved.
3. **Q2 audits: updated.** Both `Interface.lean` tables now identify exact operation supplies for every formerly missing row.
4. **Consumer migration: blocked / not completed.** The existing project has 80 files referring to legacy Arith row/model surfaces under the broad pre-migration count. Integrating the new operations directly into the existing lookup-aware circuit changed the `ConstraintsHold.Soundness` conjunction ordering and broke numerous consumer destructurings (`ArithMul/ConsumerFacts.lean` and `Compliance/SharedBundles.lean` were the first verified failures). The completed mirrors were therefore exposed additively as `mainComplete`, preserving all existing APIs and the green build. Migrating all 80 references requires a staged projection API and mechanical retargeting beyond this checkpoint.
5. **Legacy deletion: blocked.** Since item 4 did not reach reference count zero, deleting `Mul.lean`, `Div.lean`, `CarryChain.lean`, `CarryChainCompleteness.lean`, or `BusRes1.lean` would break active consumers. No legacy file was deleted.
6. **Final sweep: completed for the resulting checkpoint.** Full `lake build` passes. `trust/scripts/check-all-semantic.sh` passes all 16 checks. `trust/scripts/check-all.sh` passes checks 1–12 and 14–16; check 13 alone cannot execute because `zisk/core/src/aeneas_extract.rs` is absent, the pre-authorized snapshot limitation. `trust/generated/` is byte-unchanged. Protected roots, `ZiskFv/Audit.lean`, build pins, and lockfiles are byte-identical to the supplied snapshot.

## Updated Q2 summary

### ArithMul

| Legacy surface | Completed Clean supply | Outcome |
|---|---|---|
| carry constraints 6–8 and 31–38 | `main` / `Spec` | exact |
| selector disjointness, constraint 2 | `mainComplete`; `ModeSpec` clause 1 | exact |
| booleans 40–45 | `mainComplete`; `ModeSpec` clauses 2–7 | exact |
| result mux, constraint 46 | `mainWithArithTable`; `C46Spec` | exact |
| table and range lookups | existing lookup-aware variants / `FullSpec` | exact |

### ArithDiv

| Legacy surface | Completed Clean supply | Outcome |
|---|---|---|
| carry constraints 6–8 and 31–38 | `main` / `Spec` | exact |
| booleans/disjointness 0–5, 39–45 | `mainComplete` | exact operation supply |
| zero-divisor/overflow boundaries 9–24 | `mainComplete` | exact operation supply |
| inverse-sum detector 25 | `ArithDivAux.inv_sum_all_bs`; `mainComplete` | exact operation supply |
| scope/disjointness 26–30 | `mainComplete` | exact operation supply |
| result mux 46 | `mainComplete` | exact operation supply |
| W-mode high-lane zero 47–48 | `mainComplete` | exact operation supply |
| table and indexed ranges | existing lookup-aware variants / `FullSpec` | exact |

## Constraint citations

Every addition is labeled in `ArithCompleteConstraints.lean` with its generated extraction name/range and PIL source:

- ArithMul `constraint_2_every_row` — `arith.pil:48`.
- ArithMul `constraint_40_every_row` through `constraint_45_every_row` — `arith.pil:238–243`.
- ArithMul `constraint_46_every_row` (pre-existing supply) — `arith.pil:262/263`.
- ArithDiv `constraint_0_every_row` through `constraint_5_every_row` — `arith.pil:46–53`.
- ArithDiv `constraint_9_every_row` through `constraint_24_every_row` — `arith.pil:130–141`.
- ArithDiv `constraint_25_every_row` through `constraint_30_every_row` — `arith.pil:143–153`.
- ArithDiv `constraint_39_every_row` through `constraint_45_every_row` — `arith.pil:237–243`.
- ArithDiv `constraint_46_every_row` — `arith.pil:263`.
- ArithDiv `constraint_47_every_row` and `constraint_48_every_row` — `arith.pil:265–266`.

No audited item lacked a generated counterpart, and no constraint was added beyond this generated list.

## Counts and delta

- Broad legacy-reference file count before this work order (committed T10 report): **77**.
- Broad current reference count using the expanded legacy-type/path search: **80**. This is not a successful migration reduction; the difference reflects the expanded search and the new adapter references.
- Deleted legacy files: **none** (blocked by active references).
- Net source delta from the supplied snapshot: **+175 lines** (203 added, 28 deleted), including this report.
- `trust/generated/`: **unchanged**.

## Verification

- `lake build`: **passed**.
- `trust/scripts/check-all-semantic.sh`: **all 16 checks passed**.
- `trust/scripts/check-all.sh`: **checks 1–12 and 14–16 passed**; check 13 failed only with `FileNotFoundError` for the absent pre-authorized `zisk/core/src/aeneas_extract.rs`.
- Non-generated project zero-sorry gate: **passed** as trust check 5.
- Root theorem files, `ZiskFv/Audit.lean`, `lakefile.toml`, `lake-manifest.json`, `flake.nix`, and `flake.lock`: **unchanged**.

`ARISTOTLE_SUMMARY.md` was not modified because the user explicitly instructed this turn not to edit that file; this report is the requested reporting mirror.
