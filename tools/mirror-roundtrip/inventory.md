# mirror-roundtrip: the mirror-side inventory

Issue: eth-act/zisk-fv#304, blocked by #303. This is the *other* direction of
#303's round trip. #303 decided that every polynomial constraint in
`build/zisk.pilout` reached `build/extraction/Extraction/` unaltered. Nothing in
that argument touches `ZiskFv/`: the emitted per-AIR files are imported by no
Lean under `ZiskFv/` at all, so a constraint can round-trip perfectly into the
extraction and still be restated wrongly, partially, or not at all in the
handwritten Lean the proof actually consumes.

This document is the denominator for that second direction: every handwritten
polynomial-constraint mirror under `ZiskFv/AirsClean/**`, the row records they
project, the existing field-to-column maps, and -- the point -- which generated
constraints no mirror claims. Anything missing here becomes a constraint a later
gate silently never checks.

Everything numeric below is produced by `survey.py` and can be regenerated:

```
python3 tools/mirror-roundtrip/survey.py                      # everything
python3 tools/mirror-roundtrip/survey.py --section coverage    # one section
python3 tools/mirror-roundtrip/survey.py --quiet               # summary only
```

`survey.py` reuses `pilout_wire` and `pilout_atoms` from `tools/pilout-roundtrip`
for the pilout side, so the two tools cannot disagree about what a column or a
constraint index is. It reads only; it edits nothing under `ZiskFv/`.

### The inventory can go stale, and says so

The scope is a declared list (`CLASSIFICATION` in `survey.py`), not a shape
heuristic -- the same discipline as `DECLARED_AIRS` in `check.py`, and for the
same reason: letting the mirror set be discovered from what looks like a mirror
would let the mirror choose what the audit covers, and a new predicate that
classified itself as "not a mirror" is exactly the drop this inventory exists to
prevent. So the list has the opposite failure mode, going stale, and both
directions are checked:

* a `Prop`-valued declaration under the mirror root that `CLASSIFICATION` does not
  name is reported by name and file:line, and the run exits 1;
* a `CLASSIFICATION` entry naming a declaration that no longer exists is reported
  the same way.

Verified rather than asserted: copying `ZiskFv/AirsClean` to a temporary tree,
appending one `def NewGapSpec (row : MemRow FGL) : Prop := row.sel = 0` to
`Mem/Spec.lean`, and running
`survey.py --mirror <copy>` exits 1 with
`FAIL: Prop-valued declarations missing from CLASSIFICATION: ZiskFv/AirsClean/Mem/Spec.lean:143 NewGapSpec`;
the same copy without the mutation exits 0. `--mirror` accepts a tree outside the
repo precisely so that check needs no write to `ZiskFv/`.

## Headline counts

| quantity | value |
| -------- | ----- |
| Lean files under `ZiskFv/AirsClean/**` | 103 |
| top-level declarations in them | 1860 |
| `Prop`-valued `def`/`abbrev` | 104 |
| classified as mirrors | 40 |
| classified as near-misses | 64 |
| unclassified | 0 |
| top-level conjuncts across the 40 mirrors | 227 (composites re-count their parts) |
| row records used by a mirror | 27 (10 top-level plus 17 sub-structs) |
| handwritten field-to-column / `Expr`-to-field maps | 30 |
| published mirror predicates nothing references | 1 (`Main.RomBoolSpec`) |
| comparable generated constraints | 176 |
| comparable constraints no mirror claims | **18** |
| comparable constraints claimed only outside the mirror root | 15 |

"Comparable" is the issue's own exclusion rule: total minus every constraint
whose expression tree reaches `Extraction.Circuit.challenge` or a stage-2 lane
`main c (id := 2)`. `survey.py` computes it off the pilout operands, and it
reproduces the per-AIR figures independently (Arith 49, Binary 7, BinaryAdd 4,
BinaryExtension 0, Main 39, Mem 24, MemAlign 33, MemAlignByte 9,
MemAlignReadByte 4, MemAlignWriteByte 7; total 176).

The **extractor's own single-field/two-field binder distinction is deliberately
not used** as the exclusion rule. It would exclude nine more Main constraints --
Main {0, 3, 4, 9, 10, 19, 20, 21, 38}, the ones reaching an `AirValue` or
`AirGroupValue` but no challenge and no stage-2 lane -- and Main #3 and #9 are
precisely the flagship gap below. Using the binder rule would make the flagship
finding disappear.

## Scope, and one place it leaks

The issue scopes the inventory to `ZiskFv/AirsClean/**`. That boundary is not
where the mirrors stop. `ZiskFv/AirsClean/Mem/GeneratedTransition.lean:251`
(`generatedTransition`) reaches `ZiskFv.Airs.Mem.segmentResidualEveryRow`
(`ZiskFv/Airs/Mem.lean:296`, 15 conjuncts) and
`ZiskFv.Airs.Mem.permutation_every_row`, both of which are polynomial mirrors
declared *outside* the mirror root. Those 15 conjuncts are exactly Mem's 15
comparable constraints that no in-root mirror claims, and
`segmentResidualEveryRow_of_segment_every_row` (`ZiskFv/Airs/Mem.lean:332`)
destructures the 24-clause `segment_every_row` at indices
`{0,1,2,9,10,11,12,13,14,15,16,17,19,20,22}`, pinning the index correspondence
in the source. `survey.py` records this in its `DELEGATED` list and reports it
separately from the genuinely unmirrored set, so neither is confused with the
other. **Decision needed from the owner:** whether #305's gate scope is
`AirsClean` only (in which case 15 Mem constraints are out of scope and should be
declared so) or "every polynomial mirror the AirsClean components reach" (in
which case `ZiskFv/Airs/Mem.lean` joins the root). Nothing here changes it.

## 1. Mirror inventory

Classes, as `survey.py` defines them:

| class | meaning |
| ----- | ------- |
| `MIRROR` | conjunction of field equations over row-record projections |
| `MIRROR_2ROW` | same, over two row records at a fixed row offset |
| `MIRROR_MIXED` | field equations plus non-polynomial clauses in one predicate |
| `MIRROR_VALIDATOR` | the same equations over `Valid_<AIR>` accessors at a row index |
| `MIRROR_BUILDER` | the same equations over an honest-row builder's inputs |
| `MIRROR_ENV` | an adapter restating a mirror at Clean `Environment`s |
| `MIRROR_COMPOSITE` | a conjunction of other named mirrors, no equations of its own |
| `MIXED_COMPOSITE` | a conjunction mixing named mirrors with non-polynomial specs |

`conj` is the number of `∧`-separated clauses at bracket depth 0. `claims` is the
generated constraint indices the mirror is *asserted* to restate: an audited
reading of the mirror body against `build/extraction/Extraction/<AIR>.lean` and
its provenance comments, **not** a pairing decided polynomially. #305 decides the
pairings; what the claim sets buy now is that "which constraints have no mirror"
is computed arithmetic instead of a reader's impression.

### Arith (row records `ArithMulRow`, `ArithDivRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:54` | `Spec` | `MIRROR` | `row : ArithMulRow` | 11 | c6-c8, c31-c38 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:166` | `C46Spec` | `MIRROR` | `row : ArithMulRow` | 1 | c46 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:238` | `DivModeSpec` | `MIRROR` | `row : ArithMulRow` | 13 | c0-c5, c39-c45 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:253` | `DivBoundarySpec` | `MIRROR` | `row : ArithMulRow` | 16 | c9-c24 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:271` | `DivInverseSumSpec` | `MIRROR` | `row : ArithMulRow` | 1 | c25 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:276` | `DivScopeSpec` | `MIRROR` | `row : ArithMulRow` | 5 | c26-c30 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:283` | `DivWModeSpec` | `MIRROR` | `row : ArithMulRow` | 2 | c47, c48 |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:289` | `SharedDivBlockSpec` | `MIRROR_COMPOSITE` | `row : ArithMulRow` | 5 | (its parts) |
| `ZiskFv/AirsClean/ArithMul/Spec.lean:234` | `FullSpec` | `MIXED_COMPOSITE` | `row : ArithMulRow` | 6 | (its parts) |
| `ZiskFv/AirsClean/ArithDiv/Spec.lean:70` | `Spec` | `MIRROR` | `row : ArithDivRow` | 11 | c6-c8, c31-c38 |
| `ZiskFv/AirsClean/ArithDiv/Spec.lean:186` | `FullSpec` | `MIXED_COMPOSITE` | `row : ArithDivRow` | 3 | (its parts) |

All rows are current-row only; Arith has no cross-row comparable constraint.
The seven primary `ArithMul` predicates cover c0-c48 exactly, which is all 49
comparable Arith constraints. `ArithDiv.Spec` is a **second view of the same 11**
in a different row record, so #305 must decide 60 Arith mirror conjuncts against
49 generated constraints, with 11 pairings appearing twice.

The circuit-side carrier of the same set is
`ZiskFv/AirsClean/ArithCompleteConstraints.lean:18` (`sharedMainComplete`, 38
`assertZero`s over `mainWithArithTable`'s 11), whose comments cite the generated
constraint ranges directly. It is a `Circuit FGL Unit`, not a `Prop`, so it is
not in the mirror table; see near-miss category "circuit-side carriers".

### Binary (row record `BinaryRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/Binary/Spec.lean:45` | `Spec` | `MIRROR` | `row : BinaryRow` | 7 | c0-c6 |
| `ZiskFv/AirsClean/Binary/Bridge.lean:1100` | `constraints_at` | `MIRROR_VALIDATOR` | `Valid_Binary` at `r` | 7 | c0-c6 |

Complete: 7 conjuncts for 7 comparable constraints.

### BinaryAdd (row record `BinaryAddRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/BinaryAdd/Circuit.lean:113` | `CoreFacts` | `MIRROR` | `row : BinaryAddRow` | 4 | c0-c3 |
| `ZiskFv/AirsClean/BinaryAdd/Bridge.lean:82` | `constraints_at` | `MIRROR_VALIDATOR` | `Valid_BinaryAdd` at `r` | 4 | c0-c3 |
| `ZiskFv/AirsClean/BinaryAdd/Circuit.lean:131` | `ComponentSpecFacts` | `MIXED_COMPOSITE` | `row : BinaryAddRow` | 3 | (its parts) |

Complete: 4 for 4. Note `BinaryAdd.Spec` is **not** a mirror -- it is the
semantic `cPacked = (packed32 a + packed32 b) % 2^64` statement over `ℕ`. The
polynomial content is `CoreFacts`, which only `ComponentSpecFacts` references.

### BinaryExtension (row record `BinaryExtensionRow`)

No mirror, and none needed: BinaryExtension has **0** comparable constraints --
all 8 reach a challenge or a stage-2 lane. `BinaryExtension.Spec` and
`BinaryExtension.Bridge.constraints_at` are both `True`, which is the correct
statement here and is classified `NEAR_VACUOUS` rather than as a mirror.

### Main (row records `MainRow`, `MainRowWithRom`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/Main/Spec.lean:52` | `Spec` | `MIRROR` | `row : MainRow` | 9 | c7, c8, c13-c17, c22, c28 |
| `ZiskFv/AirsClean/Main/Spec.lean:68` | `AddressSpec` | `MIRROR` | `row : MainRowWithRom` | 4 | c1, c2 (**only 2 of 4**) |
| `ZiskFv/AirsClean/Main/Spec.lean:78` | `SourceSpec` | `MIRROR` | `row : MainRowWithRom` | 4 | c5, c6, c11, c12 |
| `ZiskFv/AirsClean/Main/Circuit.lean:346` | `RomBoolSpec` | `MIRROR` | `row : MainRowWithRom` | 14 | c23-c27, c29-c37 |
| `ZiskFv/AirsClean/Main/Circuit.lean:708` | `pcHandshakeBetween` | `MIRROR_2ROW` | `prev`, `curr : MainRowWithRom` (`curr` = `prev` + 1) | 1 | c18 |
| `ZiskFv/AirsClean/Main/Circuit.lean:721` | `sourceCCopyBetween` | `MIRROR_2ROW` | `prev`, `curr : MainRowWithRom` | 2 | c4, c10 |
| `ZiskFv/AirsClean/Main/Circuit.lean:734` | `transitionBetween` | `MIRROR_COMPOSITE` | `prev`, `curr : MainRowWithRom` | 2 | (its parts) |
| `ZiskFv/AirsClean/Main/Circuit.lean:942` | `pcHandshakeTransition` | `MIRROR_ENV` | two `Environment`s | 1 | (via `transitionBetween`) |
| `ZiskFv/AirsClean/Main/Circuit.lean:326` | `MainRomAddressGuard` | `MIRROR_BUILDER` | `(bits, free)` | 1 | c2 |
| `ZiskFv/AirsClean/Main/Circuit.lean:333` | `MainRomSourceGuard` | `MIRROR_BUILDER` | `(msg, bits, free)` | 4 | c5, c6, c11, c12 |
| `ZiskFv/AirsClean/Main/Bridge.lean:87` | `constraints_at` | `MIRROR_VALIDATOR` | `Valid_Main` at `r` | 9 | same as `Spec` |
| `ZiskFv/AirsClean/Main/CrossRow.lean:68` | `pc_handshake_at` | `MIRROR_VALIDATOR` | `Valid_Main` at `r`, `r - 1` over `ℕ` | 1 | c18 |

32 of Main's 39 comparable constraints are claimed. Seven are not; see finding
F1.

### Mem (row record `MemRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/Mem/Spec.lean:56` | `Spec` | `MIRROR` | `row : MemRow` | 9 | c3-c8, c18, c21, c23 |
| `ZiskFv/AirsClean/Mem/Bridge.lean:239` | `constraints_at` | `MIRROR_VALIDATOR` | `Valid_Mem` at `r` | 9 | same |
| `ZiskFv/AirsClean/Mem/GeneratedTransition.lean:251` | `generatedTransition` | `MIRROR_COMPOSITE` | `previous`, `current : Environment` | 3 | delegates out of root |

9 of 24 in root; the other 15 via `ZiskFv/Airs/Mem.lean:296`. See finding F4.

### MemAlign (row record `MemAlignRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/MemAlign/Spec.lean:48` | `Spec` | `MIRROR` | `row : MemAlignRow` | 16 | c16-c28, c30-c32 |
| `ZiskFv/AirsClean/MemAlign/Circuit.lean:233` | `transitionRows` | `MIRROR_2ROW` | `previous` = row -1, `current` = row 0 | 9 | c1, c3, c5, c7, c9, c11, c13, c15, c29 |
| `ZiskFv/AirsClean/MemAlign/Circuit.lean:254` | `cyclicSuccessorTransitionRows` | `MIRROR_2ROW` | `current` = row 0, `successor` = row +1 | 9 | c0, c2, c4, c6, c8, c10, c12, c14 (**8 claims, 9 conjuncts**) |
| `ZiskFv/AirsClean/MemAlign/Circuit.lean:244` | `transition` | `MIRROR_ENV` | two `Environment`s | 1 | (via `transitionRows`) |
| `ZiskFv/AirsClean/MemAlign/Circuit.lean:265` | `cyclicSuccessorTransition` | `MIRROR_ENV` | two `Environment`s | 1 | (via the successor rows) |

All 33 comparable constraints claimed, and one mirror conjunct over: 34
conjuncts, 33 claims. See finding F3.

### MemAlignByte (row record `MemAlignByteRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/MemAlignByte/Spec.lean:77` | `Spec` | `MIRROR_MIXED` | `row : MemAlignByteRow` | 8 (5 equations + 3 `.val <`) | c3, c5-c8 |
| `ZiskFv/AirsClean/MemAlignByte/Bridge.lean:116` | `constraints_at` | `MIRROR_VALIDATOR` | `Valid_MemAlignByte` at `r` | 5 | c3, c5-c8 |

5 of 9. Four selector/`is_write` booleans are unclaimed; see finding F2.

### MemAlignReadByte (row record `MemAlignReadByteRow`)

| file:line | name | class | rows | conj | claims |
| --------- | ---- | ----- | ---- | ---- | ------ |
| `ZiskFv/AirsClean/MemAlignReadByte/Spec.lean:73` | `Spec` | `MIRROR_MIXED` | `row : MemAlignReadByteRow` | 2 (1 equation + 1 `.val <`) | c3 |
| `ZiskFv/AirsClean/MemAlignReadByte/Bridge.lean:98` | `constraints_at` | `MIRROR_VALIDATOR` | `Valid_MemAlignReadByte` at `r` | 4 | c0-c3 |

All 4 claimed, but 3 of them **only** in the validator-indexed form; see F2.

### MemAlignWriteByte

**No mirror of any kind, no row record, no `ZiskFv/AirsClean/MemAlignWriteByte/`
directory.** The string `MemAlignWriteByte` does not occur anywhere in `ZiskFv/`
or `trust/`. See finding F5.

## 2. Near-misses

64 `Prop`-valued declarations under the mirror root look like mirrors and are
not. Grouped by what each actually is. Full list:
`survey.py --section nearmisses`.

### `NEAR_RANGE` -- bounds on `.val`, not field equations (11)

`ℕ`-valued bit-width facts. They are not polynomial identities and cannot be
compared against a pilout constraint in the pilout's own algebra: `x.val < 2`
is not `x * (1 - x) = 0` as a term, even where the two are equivalent facts.

`Binary/Spec.lean:37` `Assumptions`; `BinaryAdd/Spec.lean:49` `Assumptions`;
`Main/Spec.lean:47` `Assumptions`; `Mem/Spec.lean:51` `Assumptions`;
`MemAlign/Spec.lean:40` `Assumptions`; `MemAlignByte/Spec.lean:70`
`Assumptions`; `MemAlignReadByte/Spec.lean:64` `Assumptions`;
`ArithMul/Spec.lean:182` `ChunkRangeSpec`; `ArithMul/Spec.lean:203`
`CarryRangeSpec`; `BinaryAdd/Circuit.lean:122` `RangeFacts`;
`Mem/Constraints.lean:61` `dualMemRowRangeFacts`.

### `NEAR_LOOKUP` -- lookup or static-table membership (12)

Membership in a `StaticTable`, which is a lookup argument, not a polynomial
identity of the AIR. `ArithMul/Spec.lean:151` and `ArithDiv/Spec.lean:166`
`ArithTableSpec`; `ArithMul/Spec.lean:216` and `ArithDiv/Spec.lean:172`
`IndexedRangeSpec`; `Binary/Bridge.lean:24,37,59,79` the four
`StaticBinaryTable*Facts`; `Binary/Circuit.lean:359`
`StaticBinaryTableSpecFacts`; `BinaryExtension/Bridge.lean:244`
`StaticBinaryExtensionTableWfFacts`; `BinaryExtension/Bridge.lean:310`
`ShiftB0RangeSpecFact`; `BinaryExtension/StaticCircuit.lean:108`
`StaticBinaryExtensionTableSpecFacts`.

### `NEAR_BUS` -- bus, channel, interaction or trace-replay predicates (30)

Existentials over `witness.interactionsWith`, `providerTable.table`,
`matches_memory_entry` and replay-row embeddings. They constrain the *channel*
layer, which #303 also declared out of scope. All 30 are in
`ZiskFv/AirsClean/FullEnsemble/Balance/` plus `Mem/TraceSpec.lean`:
`EmbeddedInTrace.lean:31,40,47,82,95,108,121`;
`MemAlignSkippableProve.lean:22`;
`MemBusRowBridges.lean:208,879,1000,1556,1639,1674,1707,1743,1758,1778,2094,2118,2158,2200,2760`;
`RowExtraction.lean:198`; `RowsBridgeFacts.lean:222`;
`TimelineEvidence.lean:29,1910,1926`; `Mem/TraceSpec.lean:21,30`.

### `NEAR_VACUOUS` -- `True` (5)

`ArithMul/Spec.lean:50` and `ArithDiv/Spec.lean:60` `Assumptions`;
`BinaryExtension/Spec.lean:35` `Assumptions`; `BinaryExtension/Spec.lean:39`
`Spec`; `BinaryExtension/Bridge.lean:337` `constraints_at`. For
BinaryExtension the three vacuous ones are correct -- the AIR has no comparable
constraint -- but they are `True`, so they are not mirrors and must not be
counted as coverage.

### `NEAR_SEMANTIC` -- a statement over `ℕ` (1)

`BinaryAdd/Spec.lean:58` `Spec`: `cPacked row = (packed32 a + packed32 b) % 2^64`.
This is the AIR's *meaning*, proved from `CoreFacts` plus `RangeFacts`. It has no
pilout counterpart and must not be paired with one.

### `NEAR_SOUNDNESS` -- quantified `ConstraintsHold` surfaces (2)

`Binary/Bridge.lean:1033` and `BinaryExtension/Bridge.lean:344`
`StaticLookupSoundness`: `∀ r offset env, ConstraintsHold.Soundness env (...)`.
A surface over a circuit's operations, not a list of equations.

### `NEAR_DATA` -- prover-data / raw-cell bindings (1)

`Mem/GeneratedTransition.lean:239` `memRangeSidecarBridge`: pins four raw Mem
cells to canonical `ProverData` keys. Not an AIR constraint.

### `NEAR_LITERAL` -- disjunctions of literal values (2)

`RangeTables.lean:289` `ArithRangePosId` and `:295` `ArithRangeNegId`: `r = 3 ∨
r = 4 ∨ ...` over upstream `arith_range_table.pil` range IDs.

### Circuit-side carriers (not `Prop`, so not in the 104)

Worth naming because they hold the same polynomial content in `Expression FGL`
over `Var Row` and are the operational source the `Spec`s are proved from. A
later gate may prefer to compare *these* rather than the `Prop`s, since they are
what the component actually asserts. `assertZero` counts from `survey.py`'s
scan:

| file:line | name | `assertZero` | `lookup` |
| --------- | ---- | ------------ | -------- |
| `ArithCompleteConstraints.lean:18` | `sharedMainComplete` | 38 | 0 |
| `ArithDiv/Constraints.lean:49` | `main` | 11 | 0 |
| `ArithMul/Constraints.lean:136` | `main` | 11 | 0 |
| `ArithMul/Constraints.lean:240` | `mainWithArithTable` | 1 | 32 |
| `Binary/Constraints.lean:144` | `main` | 7 | 0 |
| `BinaryAdd/Constraints.lean:48` | `main` | 4 | 8 |
| `BinaryExtension/Constraints.lean:69` | `main` | 0 | 0 (one op-bus push; the 8 table tuples are channel `emit`s in `mainWithBinaryExtensionTable` at `:90`) |
| `Main/Constraints.lean:27` | `main` | 9 | 0 |
| `Main/Constraints.lean:242` | `mainWithRom` | 22 | 1 |
| `Mem/Constraints.lean:37` | `main` | 9 | 0 |
| `Mem/Constraints.lean:112` | `segmentGeneratedConstraintAssertions` | 24 | 0 |
| `Mem/Constraints.lean:162` | `permutationGeneratedConstraintAssertions` | 10 | 0 |
| `MemAlign/Constraints.lean:41` | `main` | 16 | 0 |
| `MemAlignByte/Constraints.lean:58` | `main` | 9 | 5 |
| `MemAlignReadByte/Constraints.lean:59` | `main` | 4 | 3 |

`Mem/Constraints.lean:112` is the interesting one: 24 `assertZero`s covering
*all* 24 comparable Mem constraints, over `Valid_Mem` and `SegmentColumns`
rather than over `MemRow`. So Mem's full comparable set does have a
handwritten circuit-side carrier inside the mirror root, even though its
`Prop`-level mirror is split 9-in-root / 15-out-of-root.

### Theorem statements that restate a mirror

Not declarations, so out of the inventory, but they matter for F6:
`Main/Circuit.lean:397` `romBoolSpec_of_mainWithRomAndMemBus_constraints` states all 14
`RomBoolSpec` equations inline as its conclusion. The equations are therefore
live in the proof even though the named predicate is not.

## 3. Row records, fields in declaration order

Indexed dumps: `survey.py --section records`. Positions below are
`ProvableStruct`-flattened order.

**`MainRow`** (18) `ZiskFv/AirsClean/Main/Row.lean:32`:
`a_0, a_1, b_0, b_1, c_0, c_1, flag, pc, is_external_op, op, m32, ind_width,
set_pc, jmp_offset1, jmp_offset2, store_pc, im_high_degree_2, segment_l1`

**`MainRomRow`** (25) `ZiskFv/AirsClean/Main/Row.lean:61`:
`a_offset_imm0, a_imm1, b_offset_imm0, b_imm1, store_offset, a_src_imm,
a_src_mem, is_precompiled, b_src_imm, b_src_mem, store_mem, store_ind,
b_src_ind, a_src_reg, b_src_reg, store_reg, addr0, addr1, addr2, main_step,
a_reg_prev_mem_step, b_reg_prev_mem_step, store_reg_prev_mem_step,
store_reg_prev_value_0, store_reg_prev_value_1`

**`MainRowWithRom`** (43 = `core` ++ `rom`) `ZiskFv/AirsClean/Main/Row.lean:127`.

**`MemRow`** (13) `ZiskFv/AirsClean/Mem/Row.lean:23`:
`addr, step, sel, addr_changes, step_dual, sel_dual, value_0, value_1, wr,
previous_step, increment_0, increment_1, read_same_addr`

**`MemAlignRow`** (31) `ZiskFv/AirsClean/MemAlign/Row.lean:24`:
`addr, offset, width, wr, pc, reset, sel_up_to_down, sel_down_to_up, reg_0,
reg_1, reg_2, reg_3, reg_4, reg_5, reg_6, reg_7, sel_0, sel_1, step, sel_2,
sel_3, sel_4, sel_5, sel_6, sel_7, sel_prove, preL1, delta_addr, delta_pc,
value_0, value_1`

**`MemAlignByteRow`** (16) `ZiskFv/AirsClean/MemAlignByte/Row.lean:49`:
`sel_high_4b, sel_high_2b, sel_high_b, direct_value, composed_value,
written_composed_value, written_byte_value, value_16b, value_8b, byte_value,
addr_w, step, is_write, mem_write_values_0, mem_write_values_1, bus_byte`

**`MemAlignReadByteRow`** (10) `ZiskFv/AirsClean/MemAlignReadByte/Row.lean:43`:
`sel_high_4b, sel_high_2b, sel_high_b, direct_value, composed_value, value_16b,
value_8b, byte_value, addr_w, step`

**`BinaryRow`** (39 = five sub-structs) `ZiskFv/AirsClean/Binary/Row.lean:78`:
- `BinaryAByteCols` (8) `:24`: `free_in_a_0 .. free_in_a_7`
- `BinaryBByteCols` (8) `:35`: `free_in_b_0 .. free_in_b_7`
- `BinaryCByteCols` (8) `:46`: `free_in_c_0 .. free_in_c_7`
- `BinaryChainCols` (10) `:57`: `carry_0 .. carry_7, b_op, b_op_or_sext`
- `BinaryModeCols` (5) `:70`: `mode32, result_is_a, use_first_byte, c_is_signed, mode32_and_c_is_signed`

**`BinaryAddRow`** (10) `ZiskFv/AirsClean/BinaryAdd/Row.lean:43`:
`a_0, a_1, b_0, b_1, c_chunks_0, c_chunks_1, c_chunks_2, c_chunks_3, cout_0,
cout_1`

**`BinaryExtensionRow`** (29 = four sub-structs)
`ZiskFv/AirsClean/BinaryExtension/Row.lean:65`:
- `BinaryExtensionACols` (8) `:24`: `free_in_a_0 .. free_in_a_7`
- `BinaryExtensionCColsLo` (8) `:35`: `free_in_c_0 .. free_in_c_7`
- `BinaryExtensionCColsHi` (8) `:46`: `free_in_c_8 .. free_in_c_15`
- `BinaryExtensionFlags` (5) `:57`: `op, free_in_b, op_is_shift, b_0, b_1`

**`ArithMulRow`** (44 = three sub-structs) `ZiskFv/AirsClean/ArithMul/Row.lean:81`:
- `ArithMulChunks` (16) `:23`: `a_0..a_3, b_0..b_3, c_0..c_3, d_0..d_3`
- `ArithMulFlags` (17) `:42`: `na, nb, nr, np, sext, m32, div, div_by_zero, div_overflow, main_div, main_mul, signed, range_ab, range_cd, op, bus_res1, multiplicity`
- `ArithMulCarries` (11) `:65`: `carry_0..carry_6, fab, na_fb, nb_fa, inv_sum_all_bs`

**`ArithDivRow`** (43 = three sub-structs) `ZiskFv/AirsClean/ArithDiv/Row.lean:85`:
- `ArithDivChunks` (16) `:23`: same 16 as `ArithMulChunks`
- `ArithDivFlags` (17) `:42`: same 17 as `ArithMulFlags`
- `ArithDivAux` (10) `:72`: `fab, na_fb, nb_fa, carry_0..carry_6` -- **no `inv_sum_all_bs`**

### Field order is not column order

`survey.py --section records` prints, per record, the fields with no same-named
stage-1 column and the stage-1 columns with no same-named field. Measured:

| record | fields | stage-1 cols | positional? |
| ------ | ------ | ------------ | ----------- |
| `MainRowWithRom` | 43 | 38 | no |
| `MemRow` | 13 | 13 | yes, but two fields renamed |
| `MemAlignRow` | 31 | 29 | **no** |
| `MemAlignByteRow` | 16 | 16 | yes |
| `MemAlignReadByteRow` | 10 | 10 | yes |
| `BinaryRow` | 39 | 39 | **no** |
| `BinaryAddRow` | 10 | 10 | yes |
| `BinaryExtensionRow` | 29 | 29 | **no** |
| `ArithMulRow` | 44 | 44 | **no** |
| `ArithDivRow` | 43 | 44 | **no** |

The three positional records (`MemAlignByteRow`, `MemAlignReadByteRow`,
`BinaryAddRow`) are exactly the three whose docstrings say `AUTO-GENERATED by
tools/pil-extract (clean-component subcommand)`. Every hand-written record is
non-positional. Concretely:

* `MemAlignRow` has `... sel_0, sel_1, step, sel_2 ...`; the generated header has
  `sel[0..7]` contiguous at stage-1 columns 16-23 with `step` at 24,
  `delta_addr` 25, `sel_prove` 26.
* `ArithMulRow` starts `chunks.a_0` at position 0; the AIR's column 0 is
  `carry[0]`, with `a[0]` at column 7 and `fab`/`na_fb`/`nb_fa` at 30-32.
* `BinaryRow` starts `aBytes.free_in_a_0` at position 0; the AIR's column 0 is
  `b_op`, with `free_in_a[0]` at column 1.
* `BinaryExtensionRow` starts `aCols.free_in_a_0`; column 0 is `op`.

**A gate that assumed positional correspondence would be wrong for six of the
ten records.** The correspondence has to come from a name-or-explicit map.

Fields with no stage-1 column at all, i.e. the reclassification cases:

| record | field | what it is |
| ------ | ----- | ---------- |
| `MainRowWithRom` | `core.segment_l1` | fixed column `Main.SEGMENT_L1` (index 0), materialized by `mainFixedColumns` slot 0 |
| `MainRowWithRom` | `rom.main_step` | fixed column `Main.SEGMENT_STEP` (index 1), `mainFixedColumns` slot 1 |
| `MainRowWithRom` | `rom.addr0`, `rom.addr2` | PIL `const expr` definitions; **no pilout column and no pilout constraint** |
| `MainRowWithRom` | `core.im_high_degree_2` | no stage-1 column and no fixed column in this pilout |
| `MemAlignRow` | `preL1` | fixed column `MemAlign.L1` (index 0) |
| `MemAlignRow` | `delta_pc` | the `pc' - pc` slot of hint #998, not a column |
| `MemRow` | `increment_0`, `increment_1` | renamed: columns 10, 11 are `l_increment`, `h_increment` |

Fixed columns and how often the comparable set reads them (`survey.py`):

| AIR | fixed 0 | comparable uses | fixed 1 | uses | fixed 2 | uses |
| --- | ------- | --------------- | ------- | ---- | ------- | ---- |
| Main | `Main.SEGMENT_L1` | 9 | `Main.SEGMENT_STEP` | 0 | `__L1__` | 0 |
| Mem | `Mem.SEGMENT_L1` | 10 | `__L1__` | 0 | | |
| MemAlign | `MemAlign.L1` | 1 | `__L1__` | 0 | | |
| Arith, Binary, BinaryAdd, BinaryExtension, MemAlign*Byte | `__L1__` | 0 | | | | |

So fixed columns enter the comparable set in exactly 20 places, across three
columns, and the mirror represents each differently: `Main.SEGMENT_L1` and
`Mem.SEGMENT_L1` through component-owned `IndexedFixedColumns` schemas
(`Main/Circuit.lean:768`, `Mem/GeneratedTransition.lean:40`), and `MemAlign.L1`
as a plain row field with no fixed schema at all -- see finding F7. `__L1__`
never reaches a comparable constraint, so the mirror's silence about it is
correct.

## 4. Existing handwritten field-to-column / `Expr`-to-field maps

30 maps, from `survey.py --section maps`. Four kinds.

### (a) Generated `Expr` term -> mirror expression (2). Both have a zeroing catch-all.

| file:line | name | arms | fallback | gated by |
| --------- | ---- | ---- | -------- | -------- |
| `ZiskFv/AirsClean/MemAlign/Bridge.lean:31` | `h998ExprToField` | 38 | **`\| _ => 0`** | `MemAlignRomWiring.sourceBinding` (`:219`), discharged by `rfl` in `h998Wiring` (`:223`); surfaced by `h998_tuple_matches_successor_message` (`:240`) |
| `ZiskFv/AirsClean/Binary/Wiring.lean:33` | `c10LookupExprToClean` | 18 | **`\| _ => 0`** | `BinaryC10Wiring.sourceBinding` (`:79`), discharged by `rfl` in `c10Wiring` (`:83`); surfaced by `c10_lookup_tuple_matches_lookupMessage7` (`:97`) |

These are the two maps the issue is about. Both are *partial functions with a
zeroing fallback*: a wrong or missing arm silently becomes `0`, which weakens
rather than fails. What gates them today is narrow but real: each is used only
inside one `rfl`-proved structure field asserting that *one specific* generated
tuple maps to *one specific* live model
(`hint_MemAlign_36_1.slots` -> `memAlignRomSuccessorTuple`, and
`derivedTuple_Binary_10_0.slots` -> `lookupMessage7Tuple`). If an arm needed by
that tuple were wrong, the `rfl` would fail. Both docstrings say the fallback is
"unreachable for the checked tuple", which is the correct claim and is
*enforced only for those tuples*: nothing stops a future caller from applying
either map to a different `Expr` and silently getting zeros. That residual is
the gap #304 exists to make mechanical, and it is a finding (F8), not something
to patch by widening the arm list.

### (b) `Valid_<AIR>` accessor <-> row field record literals (20). Total by construction.

`rowAt`-style, one per AIR plus inverses. A record literal must assign every
field or it does not compile, so there is no fallback and no silent zero; the
failure mode is a *wrong* assignment, which nothing checks.

| file:line | name | direction | leaf assignments |
| --------- | ---- | --------- | ---------------- |
| `ArithDiv/Bridge.lean:189` | `rowAt` | validator -> row | 14 |
| `ArithMul/Bridge.lean:264` | `rowAt` | validator -> row | 17 |
| `Binary/Bridge.lean:268` | `rowAt` | validator -> row | 39 |
| `Binary/Bridge.lean:321` | `validOfRow` | row -> validator | 44 |
| `BinaryAdd/Bridge.lean:47` | `rowAt` | validator -> row | 10 |
| `BinaryAdd/Bridge.lean:180` | `validOfRow` | row -> validator | 13 |
| `BinaryExtension/Bridge.lean:21` | `rowAt` | validator -> row | 33 |
| `BinaryExtension/Bridge.lean:62` | `validOfRow` | row -> validator | 35 |
| `Main/Bridge.lean:34` | `rowAt` | validator -> row | 18 |
| `Main/Bridge.lean:55` | `validOfRow` | row -> validator | 22 |
| `Mem/Bridge.lean:35` | `rowAt` | validator -> row | 13 |
| `Mem/Bridge.lean:67` | `validOfRow` | row -> validator | 16 |
| `MemAlign/Bridge.lean:75` | `rowAtWithDelta` | validator -> row | 31 |
| `MemAlign/Bridge.lean:113` | `rowAt` | validator -> row | 0 (delegates to `rowAtWithDelta ... 0`) |
| `MemAlign/Bridge.lean:119` | `validOfRow` | row -> validator | 30 |
| `MemAlignByte/Bridge.lean:48` | `rowAt` | validator -> row | 16 |
| `MemAlignByte/Bridge.lean:68` | `validOfRow` | row -> validator | 16 |
| `MemAlignReadByte/Bridge.lean:44` | `rowAt` | validator -> row | 10 |
| `MemAlignReadByte/Bridge.lean:58` | `validOfRow` | row -> validator | 10 |

`ArithDiv/Bridge.lean:189` assigns 14 and `ArithMul/Bridge.lean:264` assigns 17,
against 43 and 44 record fields, because the nested sub-struct groups are
assigned as whole literals. Note `MemAlign/Bridge.lean:113`'s `rowAt` pins
`delta_pc := 0` -- documented at `:109` as "the pre-h998 legacy projection has no
`DELTA_PC` source" -- so the legacy view of a MemAlign row states a *false*
`delta_pc` unless the caller uses `rowAtWithDelta`. The docstring says it is not
used as the bus-133 soundness source. Nothing enforces that.

### (c) Effective row slot -> raw witness slot or fixed column (2). Total, `omega`-proved.

| file:line | name | branches | fallback |
| --------- | ---- | -------- | -------- |
| `Main/Circuit.lean:744` | `mainFixedLayout` | 5 | none: final `else`, index arithmetic by `omega` |
| `Mem/GeneratedTransition.lean:26` | `memFixedLayout` | 3 | none: final `else` |

`mainFixedLayout` maps 43 effective slots to 41 raw plus 2 fixed, hardcoding
slot 17 (`core.segment_l1`) and slot 37 (`rom.main_step`). `memFixedLayout` maps
19 effective slots to 17 raw plus 2 fixed. Both are total and their index
arithmetic is proved, but the *choice* of which slot is which fixed column is a
literal in the source with no cross-check against the pilout's fixed-column
declaration.

### (d) Named column-index constants and a constraint-index map (6).

| file:line | name | maps | fallback |
| --------- | ---- | ---- | -------- |
| `Mem/SidecarColumns.lean:67` | `MemFixedColumn.segmentL1` | -> fixed slot 0 | n/a (a constant) |
| `Mem/SidecarColumns.lean:68` | `MemFixedColumn.l1` | -> fixed slot 1 | n/a |
| `Mem/SidecarColumns.lean:77-80` | `MemRangeSidecarRawColumn.distance{Base,End}{0,1}` | -> raw slots 13, 14, 15, 16 | n/a |
| `Mem/RangeWiring.lean:29` | `memRangeSourceOfConstraint` | generated constraint index 29-32 -> (hint slot AST, raw column, prover-data key) | **`\| _ => none`** |

`memRangeSourceOfConstraint` is the good pattern and the contrast with (a): its
fallback is `none`, a refusal, not a zero, and it is consumed only through
`MemRangeWiring.sourceBinding` (`Mem/RangeWiring.lean:57`) which demands
`= some (hint.slots, rawColumn, proverDataKey)`. A missing arm makes the
structure unconstructible instead of silently interpreting a term as zero.

### What is *not* wired

Only four files under `ZiskFv/` import anything from `Extraction`:
`Binary/Wiring.lean`, `Mem/RangeWiring.lean`, `MemAlign/Bridge.lean` (all
`Extraction.LookupWiring`) and `MemAlignRomTable.lean`
(`Extraction.MemAlignRom`). The generated per-AIR constraint files
`Extraction/<AIR>.lean` are imported by nothing under `ZiskFv/`. So the entire
mirror side is connected to the generated side by three `rfl`-checked tuple
bindings and one table import -- and by *nothing at all* for the 176 comparable
polynomial constraints. Every correspondence in section 1's `claims` column is
today a comment, not a check.

## 5. Per-AIR coverage

| air | pilout total | comparable | excluded | primary mirrors | conjuncts | claimed | unclaimed |
| --- | -----------: | ---------: | -------: | --------------: | --------: | ------: | --------: |
| Arith | 65 | 49 | 16 | 8 | 60 | 49 | 0 |
| Binary | 14 | 7 | 7 | 1 | 7 | 7 | 0 |
| BinaryAdd | 9 | 4 | 5 | 1 | 4 | 4 | 0 |
| BinaryExtension | 8 | 0 | 8 | 0 | 0 | 0 | 0 |
| Main | 144 | 39 | 105 | 6 | 34 | 32 | **7** |
| Mem | 34 | 24 | 10 | 1 | 9 | 9 | 0 (15 delegated out of root) |
| MemAlign | 40 | 33 | 7 | 3 | 34 | 33 | 0 |
| MemAlignByte | 16 | 9 | 7 | 1 | 8 | 5 | **4** |
| MemAlignReadByte | 10 | 4 | 6 | 1 | 2 | 4 | 0 |
| MemAlignWriteByte | 15 | 7 | 8 | 0 | 0 | 0 | **7** |
| TOTAL | 355 | 176 | 179 | 22 | 158 | 143 | **18** |

`primary mirrors` and `conjuncts` count only `MIRROR`, `MIRROR_2ROW` and
`MIRROR_MIXED`, so a validator-indexed restatement, a builder-input form, an
environment adapter and a composite are not double-counted. `claimed` aggregates
every mirror class.

Which of the 10 AIRs have a mirror at all: **nine**. Only
**MemAlignWriteByte has none**.

## 6. Reachability

`survey.py --section reachability` counts, per `Prop`-valued declaration, lines
of checked-in Lean under `ZiskFv/`, `trust/` and `Tests/` that mention its name
(comments stripped), excluding the declaration's own head line. Matching is by
name, not by resolved constant, so a name reused across namespaces (`Spec`,
`Assumptions`, `constraints_at`, `transition`) reads as the sum over all of them
and a positive count is only an upper bound. A count of **zero** is conclusive:
no line anywhere mentions the name.

Three declarations have zero external references:

| file:line | name | class |
| --------- | ---- | ----- |
| `ZiskFv/AirsClean/Main/Circuit.lean:346` | `RomBoolSpec` | **`MIRROR`** |
| `ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean:82` | `MutableMemReadReplayRowsEmbeddedInTrace` | `NEAR_BUS` |
| `ZiskFv/AirsClean/FullEnsemble/Balance/EmbeddedInTrace.lean:95` | `MutableMemReplayRowsEmbeddedInTrace` | `NEAR_BUS` |

`RomBoolSpec` is the only unreachable *mirror*; the documented case is confirmed.
See F6. The two `EmbeddedInTrace` predicates are bus predicates, out of scope for
this round trip, and are reported only so the reachability pass is exhaustive.

Two more are reachable but barely, and worth knowing before #305 wires anything:
`BinaryAdd.CoreFacts` and `BinaryAdd.RangeFacts` each have exactly one
reference, both inside `ComponentSpecFacts`.

## 7. Findings

These are reported, not fixed. Each is a mirror-side observation with a source
citation; none is repaired here, and none is made to disappear by widening a
list. Deciding what to do about them is the owner's call.

**F1 -- Main's a-side C copy has no mirror (the flagship gap).** Main c3 and c9
are `(a_src_c)*(a[0]-(previous_c))` and `(a_src_c)*(a[1]-(previous_c))`, both
`main/pil/main.pil:385`. `sourceCCopyBetween`
(`ZiskFv/AirsClean/Main/Circuit.lean:721`) mirrors only the **b-side** pair, c4
and c10 at `main.pil:386`, and its own docstring says so. Nothing in the mirror
root restates the a-side. Five further Main comparable constraints are also
unclaimed: c0 (`Main.main_last_segment*(1-Main.main_last_segment)`,
`main.pil:86`), c19 (`Main.SEGMENT_L1'*(Main.segment_next_pc-(next_pc'))`,
`main.pil:423`), c20 and c21
(`Main.SEGMENT_L1'*(Main.segment_last_c[i]-c[i])`, `main.pil:426`) and c38
(`Main.SEGMENT_L1*(Main.segment_initial_pc-pc)`, `main.pil:508`). All five reach
an `AirValue`/`AirGroupValue` -- the segment-boundary public inputs -- which is
consistent with `sourceCCopyBetween`'s docstring stating that Clean's transition
interface has no public-input surface. c3 and c9 do not have that excuse: they
reach `a_src_c`, a `const expr` over ordinary Main columns, exactly like c4 and
c10.

This is not only a mirror-`Prop` gap: the circuit side does not assert them
either. `main` (`Main/Constraints.lean:27`) and `mainWithRom` (`:242`) together
carry 31 `assertZero`s and none of them is the a-side copy; c4/c10/c18 live in
the component transition. `grep -rn 'a_src_c\|previous_c' ZiskFv` finds one
docstring mention (`ZiskFv/Airs/Main/Main.lean:136`, describing the **b**-side)
and no constraint. The same holds for the other five:
`main_last_segment`, `segment_initial_pc`, `segment_next_pc` and
`segment_last_c` do not occur anywhere in `ZiskFv/`. So all seven are absent from
the tree, not merely absent from the mirror root.

**F2 -- four MemAlignByte booleans appear in the published `Spec` only as `ℕ`
range bounds.** MemAlignByte c0, c1, c2 (`sel_high_{4b,2b,b}*(1-...)`,
`mem_align_byte.pil:35-37`) and c4 (`is_write*(1-is_write)`, `:71`) have no
field-equation clause in `MemAlignByte.Spec`. Three sit in
`MemAlignByte.Assumptions` (`Spec.lean:70`) as `.val < 2`, and `is_write` sits in
`MemAlignByte.Spec` itself as `row.is_write.val < 2 ^ 1`. `x.val < 2` and
`x * (1 - x) = 0` are equivalent facts over `FGL` but not the same term, so a
polynomial gate cannot pair them, and an `Assumptions` clause is a
caller-supplied premise where the generated constraint is an assertion.

**The circuits do assert them.** `MemAlignByte.main`
(`MemAlignByte/Constraints.lean:58`) has 9 `assertZero`s, one per comparable
constraint, each carrying an explicit `-- constraint N
(mem/pil/mem_align_byte.pil:LINE)` comment; `MemAlignReadByte.main`
(`MemAlignReadByte/Constraints.lean:59`) has 4, likewise. So the polynomial
content is present circuit-side and complete for both AIRs; what is incomplete is
the `Prop`-level mirror the component publishes as its `Spec`, and for
MemAlignReadByte the three booleans exist as field equations only in
`MemAlignReadByte/Bridge.lean:98`'s `constraints_at` over a `Valid_<AIR>`. This
is the sharpest illustration of the classification question in section 8: which
artifact #305 gates decides whether this is a four-constraint gap or none.

**F3 -- `cyclicSuccessorTransitionRows` has one conjunct more than the
comparable set.** `ZiskFv/AirsClean/MemAlign/Circuit.lean:254` conjunct 1 is
`current.delta_pc = successor.pc - current.pc`. MemAlign's comparable
constraints are c0-c32 and none of them is that equation; its only generated
source is the `(col 4, row+1) - (col 4, row)` subterm inside
`Extraction.MemAlign.constraint_36_every_row`
(`build/extraction/Extraction/MemAlign.lean:235`), which is challenge-mixed and
therefore **excluded** from the comparable set. So this conjunct is a mirror-side
equation over an excluded constraint's hint payload. It is not obviously wrong --
`MemAlign/Bridge.lean:240`'s `h998_tuple_matches_successor_message` binds the
same tuple by `rfl` -- but a gate scoped to the comparable set has nothing to
pair it against and must either declare it or reach into the excluded set.

**F4 -- 15 of Mem's 24 comparable constraints are mirrored outside the mirror
root.** `Mem.Spec` covers 9 (c3-c8, c18, c21, c23).
`Mem/GeneratedTransition.lean:251` reaches
`ZiskFv.Airs.Mem.segmentResidualEveryRow` (`ZiskFv/Airs/Mem.lean:296`), whose 15
conjuncts are the remaining c0-c2, c9-c17, c19, c20, c22 -- the index
correspondence is pinned by the destructuring in
`segmentResidualEveryRow_of_segment_every_row` (`ZiskFv/Airs/Mem.lean:337-339`).
A gate scoped literally to `ZiskFv/AirsClean/**` reports 15 Mem constraints as
unmirrored when they are not. Scope decision needed; see "Scope" above.

**F5 -- MemAlignWriteByte has no mirror, no row record, and no mention in the
tree.** `grep -rn MemAlignWriteByte ZiskFv trust` returns nothing. The AIR is in
`DECLARED_AIRS`, #303 round-trips its 15 constraints into
`build/extraction/Extraction/MemAlignWriteByte.lean`, and 7 of them are
comparable: c0-c2 (`sel_high_*` booleans, `mem_align_byte.pil:35-37`), c3
(`composed_value`, `:59`), c4 (`written_composed_value`, `:83`), c5 and c6
(`mem_write_values[0]`, `[1]`, `:87-88`). Every one of the 7 has a
character-for-character counterpart among MemAlignByte's constraints, so a mirror
would be near-mechanical -- which is a reason it is easy to miss, not a reason it
is covered.

**F6 -- `RomBoolSpec` is a published mirror predicate that nothing references.**
`ZiskFv/AirsClean/Main/Circuit.lean:346`, 14 conjuncts, claiming Main c23-c27 and
c29-c37. Zero references anywhere in `ZiskFv/`, `trust/` or `Tests/`. Its own
docstring says "These are not part of Main's per-row soundness `Spec`; a future
honest-prover completeness project may consume them separately." The equations
themselves are *not* dead: `mainWithRom` (`Main/Constraints.lean:247-261`)
asserts all 14, and
`romBoolSpec_of_mainWithRomAndMemBus_constraints` (`Main/Circuit.lean:397`) states
all 14 inline. So the situation is precisely "a published mirror predicate
checked against nothing", with a live circuit-side twin. A gate that took
`RomBoolSpec` as evidence of Main coverage would be reading a predicate no proof
consumes.

**F7 -- `MemAlign.L1` is a fixed column modeled as a free witness field.** The
generated `constraint_16_every_row` is `MemAlign.L1*pc`
(`mem_align.pil:121`), rendered as
`preprocessed c (column := 0) * main c (id := 1) (column := 4)`. The mirror
represents `MemAlign.L1` as the row field `preL1`
(`MemAlign/Row.lean:24`, flattened position 26) and `MemAlign.component`
(`MemAlign/Circuit.lean:279`) declares no `fixedColumns` and no `rawWidth` at all --
unlike `Main.componentWithRomMemAndOpBus` (`Main/Circuit.lean:952`) and
`Mem.componentWithDualMemBus` (`Mem/Circuit.lean:253`), both of which carry an
`IndexedFixedColumns` schema. So PIL's `MemAlign.L1`, a fixed column with a known
`[1, 0, 0, ...]` value, becomes an unconstrained field whose only constraint is
`preL1 * pc = 0`. The honest-row builder sets `preL1 := boolF isBoot`
(`MemAlign/Circuit.lean:137`), which is a completeness-side choice, not a soundness
pin. This is a candidate mirror-side weakening, and it is a finding for the owner
-- not something to correct here, since `MemAlignRow` is a protected row
structure.

**F8 -- both `Expr`-to-field maps are partial with a zeroing fallback, gated only
for one tuple each.** `h998ExprToField` (`MemAlign/Bridge.lean:31`, 38 arms) and
`c10LookupExprToClean` (`Binary/Wiring.lean:33`, 18 arms) both end `| _ => 0`.
Each is protected today by exactly one `rfl`-discharged `sourceBinding` covering
one generated tuple; applied to any other `Expr`, a missing arm reads as the zero
polynomial and the caller sees a well-typed, wrong answer. `h998ExprToField` also
carries four redundant `.add (.witness ...) (.constant "0")` arms (lines 62-65)
duplicating the bare-witness arms, which is the shape of a map that was extended
by trial against one artifact. The contrast to copy is
`memRangeSourceOfConstraint` (`Mem/RangeWiring.lean:29`), which returns `Option`
and refuses.

**F9 -- `AddressSpec` has two conjuncts with no generated counterpart.**
`Main/Spec.lean:68` clause 1 is `row.rom.addr0 = row.rom.a_offset_imm0` and
clause 3 is `row.rom.addr2 = row.rom.store_offset + row.rom.store_ind *
row.core.a_0`. Main's comparable set contains a constraint for `addr1` (c1,
`main.pil:192`) and none for `addr0` or `addr2`, and the Main witness header has
no `addr0` or `addr2` column -- PIL defines them as `const expr`. `mainWithRom`
(`Main/Constraints.lean:268,270`) asserts both. They look constructibility-neutral
(the prover can always satisfy a definition of its own witness column), but they
are mirror conjuncts with no pilout constraint to pair against, and a gate must
declare them rather than silently drop them. The same is true of
`core.im_high_degree_2`, a `MainRow` field with neither a stage-1 column nor a
fixed column in this pilout.

**F10 -- five row docstrings state a slot count that no longer matches the
record.** `MemAlign/Row.lean:9` says "19-slot" for a 31-field record;
`ArithMul/Row.lean:9` and `ArithDiv/Row.lean:9` say "28-slot" for 44 and 43;
`Binary/Row.lean:9` says "38-slot" for 39; `BinaryExtension/Row.lean:9` says
"30-slot" for 29. Documentation drift, not a proof defect -- but it is the
first thing a reader uses to size the mirror, and four of the five understate it.
Related, smaller: `MemAlignReadByte/Spec.lean:10,69` cites
`mem_align_byte.pil:57` for `composed_value` where the generated provenance says
`:59`; `MemAlign/Spec.lean:6` says "MemAlign has 25 F-typed constraints" where
the comparable count is 33.

## 8. Blind spots and classifications I am not certain of

* **`claims` is a reading, not a proof.** Every claim set in section 1 was read
  off the mirror body against the generated file and its provenance comments. Two
  of them I am confident about because the source pins the index correspondence
  (`ZiskFv/Airs/Mem.lean:337`'s destructuring, and Arith's totals landing exactly
  on 49). The rest are my pairing, and a wrong claim would move a constraint
  between "claimed" and "unclaimed" without the script noticing. #305 must decide
  the pairings polynomially; until then, treat the "unclaimed" column as a lower
  bound on the gap.

* **Whether `MIRROR_VALIDATOR` should count as coverage at all.** A
  `constraints_at` over a `Valid_<AIR>` is the same equation over a different
  carrier. For MemAlignReadByte that distinction decides whether 3 constraints
  are covered or not (F2), and I report both numbers rather than choosing.
  `Valid_<AIR>` fields are a protected interface, so this is a scope question,
  not something to normalise away.

* **Whether the circuit-side `assertZero` sequences are the real mirror.** I
  classified them out of the 104 because they are `Circuit FGL Unit`, not `Prop`
  -- the issue's own definition. But `Mem/Constraints.lean:112` covers all 24 Mem
  comparable constraints, and `ArithCompleteConstraints.lean:18` covers Arith's
  49; both are inside the root. If #305 compares the circuits instead of the
  `Prop`s, Mem's F4 scope problem mostly evaporates and the inventory's
  denominator changes. I have not assumed either way.

* **`MIRROR_BUILDER` vs `MIRROR`.** `MainRomAddressGuard` and
  `MainRomSourceGuard` state the same equations as `AddressSpec` clause 4 and
  `SourceSpec`, over `(msg, bits, free)` rather than a row record. They are
  completeness-side constructibility conditions on the honest-row builder. I
  classified them as mirrors because the equations are the AIR's; someone might
  reasonably call them near-misses.

* **`Coherent` (`Main/Circuit.lean:250`) is not in the 104** because its result
  type is `MainRomExecKind → Prop`, which the `: Prop` test does not match. Its
  body is `Bool` and `msg.op` equalities over a ROM message, not field equations,
  so it would be `NEAR_SEMANTIC`; I mention it because the same signature shape
  would hide a genuine mirror if one were ever written that way. `survey.py`'s
  unclassified check does not catch that case.

* **`.val`-bound clauses inside `MIRROR_MIXED`.** `MemAlignByte.Spec` and
  `MemAlignReadByte.Spec` mix field equations with `.val <` bounds in one
  conjunction. I counted their conjuncts as 8 and 2 and their claims as 5 and 1,
  so the arithmetic is consistent, but a gate splitting a mixed predicate has to
  do so clause-index by clause-index and those indices are not stable against an
  edit to the predicate.

* **The reference count over-counts, never under-counts.** Name-based matching
  aggregates `Spec` across all ten namespaces, so "145 references" means nothing.
  Only the zeros in section 6 are load-bearing, and they are sound in the
  direction claimed.

* **Excluded constraints are not inventoried.** 179 of the 355 emitted
  constraints reach a challenge or a stage-2 lane and are outside this
  inventory's comparable set, per the issue's rule. Two of them are read by the
  mirror side anyway -- MemAlign c36's hint payload via F3, and Mem's range
  sidecar via `Mem/RangeWiring.lean` -- so "excluded" does not mean "the mirror
  is silent about it".
