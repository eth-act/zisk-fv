# Close the extraction-fidelity gap

*Revision 2, 2026-09-15. This tracked file is the plan of record. Revision 1 was written against
commit `019eec25`; this revision re-baselines it onto branch `extraction-fidelity-hardening`, whose
62 commits of 2026-09-05 already implement several workstreams by a different route. The gitignored
`docs/ai/plan/extraction-fidelity-hardening.md` on the original machine records how those commits
were produced; it is not needed to execute this plan.*

Tracking: umbrella **#368**, children **#369-#376**. Existing issues this builds on: #354, #366,
#348, #358, #268, #328/#103, #330, #19. Issue bodies still carry revision-1 numbers; update them
only after W0c prints the recomputed ones, and count that as bookkeeping, not progress.

## Baseline

The baseline is `extraction-fidelity-hardening` at the commit carrying this file. Verified on it:

- `lake build` is green (9,187 jobs). All 18 generated modules compile through the closed
  inventory in `tools/check-generated-modules.sh`.
- The fast trust gate fails on exactly one of twenty checks: 18/20 reports
  `ZiskFv.AirsClean.MemAlign.ExtractedWiring` and `ZiskFv.AirsClean.MemAlignByte.ExtractedWiring`
  unreachable from `ZiskFv.lean`. Both build cleanly when targeted directly.
- No `axiom`, `sorry`, `native_decide`, `opaque`, `unsafe`, `partial`, `@[extern]` or
  `@[implemented_by]` was added under `ZiskFv/`. `ZiskFv/Soundness.lean` and
  `ZiskFv/Completeness.lean` are untouched.
- `ZiskFv/` consumes 27 generated `ValidatedLink`s (revision 1 counted 6); the extractor emits 130
  (revision 1 counted 124).

Not verified on it:

- No mutation-suite result exists on disk. Every "expected detection layer" in
  `tools/adversarial-mutations/diagnostics.json` is a prediction until a run produces
  `mutation-results/round-NN.json` from this checkout.
- The proof content of roughly 2,700 new Lean lines has been scanned for trust markers only, not
  reviewed against the anti-laundering rules line by line.

Loose ends: four worktrees (`../zisk-fv-{links,mutations,mutation-validation,tables}`), two dirty
files, one unmerged commit. W0a disposes of them.

**Every number in the next section was measured at `019eec25` and is stale here.** Do not adjust
them by hand. W0c recomputes them, and the recomputed ledger replaces this section's table.

## Context, as measured at `019eec25`

A 52-round adversarial mutation sweep (`docs/adversarial-mutation-sweep.md`) injected one defect at
a time into pinned ZisK v0.17.0, recompiled the circuit, re-ran `tools/pil-extract`, and rebuilt. Of
35 mutations that genuinely changed ZisK's compiled constraint system, **24 were caught and 11 were
missed**.

A rule held over all 31 rounds carrying a semantic diff: a mutation is caught iff it changes a
constraint that is either named as `<Air>.extraction.constraint_N_every_row` under `ZiskFv/`, or
covered by a consumed `ValidatedLink`. Applied to the whole population at that commit: **167 of 355
extracted constraints were exposed.**

| constraint class | covered | exposed |
|---|--:|--:|
| pure base field | 151 | 1 |
| reaches a challenge (cubic extension of Goldilocks) | 12 | 157 |
| air value only, no challenge | 25 | 9 |

The base-field layer was finished. The gap is the stage-2 constraints, and what is exposed there is
not the logUp algebra, which the project assumes through `channels_balanced`. It is the **bus tuple**
folded into the accumulator-update constraint. ZisK has no message column.

**Scope.** Single-segment RV64IM, no precompiles, no recursion: **34 of the 167 are out of scope,
all Main's, all cross-segment** (the 31 `main.pil:452` currents, c47/c48 on bus 1000, c142 on bus
106). **133 were in scope.**

**Round 27 is in scope.** It mutates `main.pil:334`, the per-row register ordering check.
`trust/trusted-base.md` disclaims the *claim*, not the scope. It is blocked on a provider that does
not exist (#19, #330, #348), and closes through those issues rather than this plan. The honest tally
is 11 of 11 misses that should close.

**Which rounds the sweep already caught matters for the ledger's semantics.** The report records that
21 of the 24 catches came from modules only `ZiskFv.lean` imports. Those modules defend the
repository's build, not the root theorem's statement. The ledger therefore carries two exposure
columns (W0c).

### Why generating beats tying

`Row.lean` and `Constraints.lean` are a transcription of ZisK. `Spec.lean` and `Soundness.lean` are
irreducibly human. `pil-extract clean-component` writes the first pair from the pilout, is wired into
the CLI, and no pipeline calls it. `clean_component.rs` is unchanged since revision 1 measured it, so
#370's table still holds: six AIRs emit; BinaryAdd, MemAlignByte and MemAlignReadByte produce a
byte-identical `Row.lean`; BinaryAdd's four `assertZero` lines match character for character.

For every AIR the emitter covers, three obligations disappear rather than move: the bus tuple stops
being a hand-written claim, the `assertZero` transcription stops existing, and its `*MirrorWeld.lean`
has nothing left to check. The six weld modules are 5,206 lines today.

The cost is that `Soundness.lean` (973 lines across components) and `Bridge.lean` (5,429) are proofs
written against hand-written text. Regeneration may break proofs that lean on incidental syntax, and
that surfaces only at switch-over.

## Decisions recorded in this revision

1. **Baseline** is this branch, not `019eec25`. Nothing already tied is redone.
2. **One harness**, at `tools/adversarial-mutations/`. `tools/mutation-sweep/` is carried on the
   branch as evidence and as parts to port; W0b empties it and deletes it.
3. **Mutation rounds never run in CI.** A round is about ten minutes of `lake build`; the regression
   subset is hours. They run by hand through `runner.py suite`. The exposure ledger, the coverage
   inventory, the generated-module inventory and the faithfulness report are cheap and run in
   `nix run .#test`, from where CI picks them up.
4. **W6's route** is a kernel `rfl` equality between the transcribed table and the generated rows.
   Defining through the generated type is not required.
5. **W9's route** is executing the pinned pil2-compiler on the upstream builder
   (`tools/virtual-tables/export-mem-align-rom.cjs`). No PIL evaluator is written.
6. **Ledger semantics**: exposed-to-build and exposed-to-root are separate columns; a tie on a bus
   with no provider in `fullRv64imSoundEnsemble` is a third state, "tied, not composed"; residuals
   live in a declaration file with an issue and a PIL citation, never an `exempt` key.
7. **`PLAN_S3_LOOKUP_WIRING.md` is unavailable** on this machine; it was gitignored. The four
   rulings quoted below are the record. If the original resurfaces, add it under `docs/ai/` and cite
   it; do not wait for it.

## Burn-down

1. **Exposure**, `trust/generated/exposure-ledger.txt`, per AIR and per class, two columns. Last
   measured 167 / 355 at `019eec25`; recomputed by W0c. Terminal value is the count of declared,
   cited residuals, printed separately.
2. **Generated share**: components whose `Row.lean` and `Constraints.lean` come from the emitter.
   Today **0 of 10**.
3. **Literal inventory**: constants with a kernel `pin` theorem. Today **3 of about 50**.

---

## What the S3 lookup-wiring plan already settled

The `ValidatedLink` machinery this plan consumes was designed under S3 (issues #249, #259, #263,
#265, #266, #268). Four of its rulings constrain this plan.

**1. A tie is only meaningful once both sides of the interaction are in a balanced ensemble.**
Clean's `RawChannel.Consistent` applies only then. `Table.fromStatic` proves a table's data
membership and cannot by itself prove that an unmodelled sidecar was sent to that table; substituting
a detached static lookup for a missing provider is laundering. Every tie target is classified by
whether its bus has a provider in `fullRv64imSoundEnsemble`. Measured today the ensemble carries six
channels: `MemBus` (10), `OpBus` (5000), `MemAlignRange` (107), `MemAlignRom` (133),
`SpecifiedRangesSlice` (103), `RegisterStepRange` (102). Absent: `BinaryTable` (125),
`BinaryExtensionTable` (124), `ZiskRomBus` (7890), MemAlignByte's read bus (88), Arith's range and
table buses (330/331), `MAIN_CONTINUATION` (1000), and bus 106.

**2. The binding rider.** A hint is a search witness only. Before any manifest tuple is accepted, the
generated constraint term must equal the standard template instantiated with that hint's tuple AST.
On this branch each `ValidatedLink` carries that equality as proof fields
(`constraintEqualsTemplate`, `templateFromShape`) rather than an anonymous `example`. This is the
backstop that makes W4's allowlist widening safe.

**3. The trust-ledger citation format exists.** Each application records the AIR, hint id, side, bus
id, generated manifest entry, accumulator constraint ids, and PIL source lines. W8 uses that list.

**4. Arith's route was designed, not missing.** For buses 330/331: link the structurally available
range tuples to c49-64 rather than parse those terms; the same bridge supplies Arith's selected lookup
facts. W12 finishes a designed bridge.

S3 also recorded that `clean-component` has no generic range, ROM, virtual-table, or
cross-AIR-gsum emitter, and that `docs/extraction/extractor-notes.md` describes older skip/stub
behaviour and needs reconciling.

---

## Sequencing

W0a, W0b, W0c, W0d run first, in that order. W0a because the baseline must be green and on the
remote before anything is built on it; W0c before any tie because without the ledger every later
"closed" is an argument rather than a number. After W0, workstreams run smallest to largest.

---

## W0a · Stabilize the baseline — #369 (part)

*Small. No proof work.*

1. Import `ZiskFv.AirsClean.MemAlign.ExtractedWiring` and
   `ZiskFv.AirsClean.MemAlignByte.ExtractedWiring` from `ZiskFv.lean`. They build; the only defect
   is reachability. Fast gate must read 20/20.
2. Dispose of the worktree leftovers. Each item either lands as a commit that passes the gates or is
   deleted; nothing stays dirty:
   - `../zisk-fv-mutations`: `ZiskFv/AirsClean/Binary/Wiring.lean`, +24 lines pinning the raw
     source value of each byte slot (`expectedByteSlotValue`). Likely worth landing under W3.
   - `../zisk-fv-tables`: `ZiskFv/AirsClean/MemAlignByte/ExtractedWiring.lean` +56 lines (the
     selected-byte push) and a new `MemAlignReadByte/ExtractedWiring.lean`. Continuations of the
     committed MemAlignByte slice.
   - branch `fidelity-validated-links`, commit `b6b09538`: rewrites `tools/mirror-roundtrip/survey.py`
     to classify extracted assertion surfaces. Read it before W0c, since W0c reuses that module.
   Then `git worktree remove` all four and delete the `fidelity-*` branches once their content is on
   this branch or discarded.
3. Take mutation rounds out of CI. The four commits to read are `fe060d1c`, `740bb9e3`, `72223e8c`
   and `01f07e39`. Remove from `.github/workflows/proofs.yml` the mutation-suite step, the hosted
   runner provisioning and swap, and the `run_mutations` classifier output if nothing else reads
   it. Keep the coverage inventory, the generated-module inventory and the fast checks. In the same
   commit correct `docs/extraction/ci-invariant.md` and the `trust/trusted-base.md` paragraph that
   say the proof job runs the suite.
4. Push: `git push -u origin extraction-fidelity-hardening`.
5. Run `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
   `nix run .#test`. Record the results in the PR.

**Exit:** all four gates green on this branch, the branch on `origin`, no worktrees, no dirty files.

---

## W0b · One harness — #369 (part)

*Medium. Port, do not rewrite.*

`tools/adversarial-mutations/runner.py` already does isolated source copies, the pinned compiler
through `.#compile-mutation`, canonical pilout comparison, a green-baseline requirement, and the
seven-way outcome classification. Keep all of it. Port into it from `tools/mutation-sweep/`:

- `mutate.py`: site enumeration and the operators. Add `BUS_ID_SWAP` (44 sites), `SELECTOR_ARG`
  (29), `MULTIPLICITY`, `AIRVAL`. Drop `CONST_PERTURB` on `bits(n)`; pil2-compiler lowers it to a
  `witness_bits` hint, never a constraint (#358). A new operator produces new *sites*; a new round
  exists as evidence only after a real run.
- `semdiff.py`'s per-AIR changed-constraint index output. The runner's canonical comparison stays
  the verdict; the rule check in W0c needs the per-constraint indices.
- `rounds/<n>/{site.json,semdiff.json,note.md,status}` as `evidence/rounds/<n>/`, and `report.py`
  so the sweep report regenerates from them.
- The **round-0 control**: recompiling the unmutated pinned tree must re-extract to byte-identical
  Lean under `build/extraction/`, in addition to the canonical pilout equality the runner already
  checks.

Discard the shell drivers, `make_artifact.py`, `phaseA*.sh` and the `sites*.json` samples once the
enumerator reproduces them. Delete `tools/mutation-sweep/` when it is empty.

Add a `regression` profile: the 11 misses (5, 7, 16, 22, 26, 27, 32, 33, 36, 38, 46), the three
commutativity controls (6, 21, 51), and round 50, which the sweep classed as equivalent only because
the old extractor could not see it and which W9's exit criterion requires. Rounds 8 and 37 stay
equivalent by content.

**Exit:** `runner.py suite --profile regression` runs from a clean checkout; round 0 is
byte-identical; `report.py` reproduces `docs/adversarial-mutation-sweep.md`; the harness self-test
covers the new operators.

---

## W0c · The exposure ledger — #369 (part)

*Medium. The measuring instrument.*

**Output** `trust/generated/exposure-ledger.txt`. For each of the ten extracted AIRs, and for each
class (pure base field, reaches a challenge, air value only), print:

| column | meaning |
|---|---|
| total | constraints declared in `build/extraction/Extraction/<AIR>.lean`; the 355 denominator comes from here and nowhere else |
| exposed-to-build | neither named as `<Air>.extraction.constraint_N_every_row` nor covered by a `link_<Air>_N` consumed in any module reachable from `ZiskFv.lean` |
| exposed-to-root | the same, with reachability taken from `ZiskFv/Soundness.lean` |
| tied, not composed | covered by a consumed link whose bus has no provider in `fullRv64imSoundEnsemble` |
| declared residual | listed in `trust/exposure-residuals.toml` with `issue` and `pil` citation fields |

Print separately, never in the numerator: **wirable**, the generated links consumed by nothing.
That is the counter W4 moves.

**Where it lives.** A new `tools/mirror-roundtrip/exposure.py`, reusing `survey.py`, `lanes.py` and
`mirror_parse.py` for the inventory and `trust/scripts/check-module-reachability.py`'s import walk
for the two closures. `check_mirrors.py`'s verdict is polynomial equality and stays untouched. A new
unnumbered `run` line in `nix/test.nix` beside the mirror round trip; `nix/test.nix` already carries
five unnumbered steps, so the `N/20` labels in `trust/scripts/check-all.sh` are not the reason to
avoid a new check, only a reason to put it in the test recipe rather than the fast gate.

**Gate semantics.** The ledger is a baseline file in the repository's existing style: regenerate and
diff (precedent `check-baseline.sh`), and both exposure columns are monotone non-increasing
(precedent `check-shrinkage.sh`). The gate does not fail on day one because residuals are undeclared;
it fails when exposure grows, when the file is stale, or when a residual entry lacks its citation.
Hand-editing the ledger is laundering.

**The rule check.** `rule_check.py` joins each evidence round's changed constraint indices with the
ledger and predicts caught or missed. It prints, per round, the prediction against the last observed
outcome, and it prints the **re-run set**: rounds whose prediction changed since their last run.
Historical outcomes were observed at `019eec25`, so on this branch the re-run set is non-empty from
the start; that list is what the regression profile runs. The rule is scored only against current
observations. Calibration: run the ledger once at `019eec25` in a throwaway worktree (`nix run
.#populate` there first) and confirm it prints 167 and the rule scores 31/31 against the recorded
rounds. That is the check that the instrument matches the sweep.

**Exit:** the ledger reproduces 167 at `019eec25`; on this branch it prints its own numbers and
the re-run set; the umbrella issue's table is replaced by the ledger's output.

---

## W0d · The faithfulness report — #369 (part)

*Small.*

Run `pil-extract clean-component` for every registered AIR into `build/clean-components/<Air>/` and
diff against `ZiskFv/AirsClean/<Air>/{Row,Constraints}.lean`. Per AIR print: emits or not, the
emitter's reason when not, and the diff line count per file. Needs `build/` but not oleans, so
`nix/test.nix`. **Report-only** until W14: no AIR is byte-identical in `Constraints.lean` today, so a
failing check would be red from day one. A per-AIR `expected = "identical"` entry in
`trust/generated-components.toml` flips that AIR to failing; W14 adds entries.

**Exit:** the report lists the six AIRs that emit and the four that do not, each with its reason.

---

## W1 · ArithTable reachability — #375 (part) — **done on the baseline**

The import is `ZiskFv.Field.Goldilocks`, `Extraction.ArithTable` is in the Lake globs, and the
closed inventory compiles all 18 generated modules. What remains of #375 is the reporting split it
asked for: "compiled" is gated; "consumed" is only a label in `tools/extraction-coverage/manifest.json`.
W0c's ledger carries consumption per generated module. Close #375 when W0c prints it and W6's rounds
re-run CAUGHT.

---

## W2 · Main's three free ties — #373 (part) — **done on the baseline**

c18 has its `MainMirrorWeld` clause; c42 (`Main/RomWiring.lean`) and c46 (`Main/MemoryWiring.lean`)
are tied. Bus 7890 has no provider in the ensemble, so c42 is "tied, not composed"; the ledger says
so. Nothing to do beyond re-running the affected rounds under W0c's re-run set.

---

## W3 · Binary's byte-table lookups — #372 — **mostly done on the baseline**

All eight byte tuples are tied in `Binary/Wiring.lean` through `link_Binary_7/8/9/10/11`, and the
translator returns `Option` with a `rejects_unsupported` theorem. Open:

- **Injectivity.** Check mechanically that no two distinct extraction leaf patterns map to one model
  field; that is exactly the round 7/16/22 defect and `Option` alone does not exclude it. The
  worktree WIP (`expectedByteSlotValue`) pins each slot's raw source value and is one way to get it.
- **The shared `+ 0` arm.** `MemAlign/Bridge.lean`'s `h998ExprToField` still enumerates one strip
  arm per slot and ends in `| _ => 0`. Add the generic `| .add lhs (.constant "0") => f lhs` arm once,
  remove the fallback.
- **Evidence.** Rounds 7, 16 and 22 re-run to CAUGHT with results on disk.

Bus 125 has no provider in the ensemble; `binaryTableConnectionEnsemble` finishes it in a side
ensemble outside the root theorem's closure. The ties pin which tuple ZisK sends and nothing more.
Say so in the PR; the ledger says so in its column.

---

## W4 · Widen the lookup recognizer — #371 — **partly done on the baseline**

`zero_tail_template_scope` now admits BinaryExtension c4, BinaryAdd c5, Arith c61 and Main c43-45
by per-constraint `matches!` arms. Still to do, in this order:

1. Hoist `direct_assumes_neg_form_matches` out of the `if zero_tail_template_scope` block at
   `lookup_wiring.rs:606`; it fires 0 times so it cannot regress. Replace the predicate with a
   per-route × per-AIR table.
2. Widen. Revision 1 expected 124 → 169 links; the baseline emits 130. Re-measure before and after
   and report on the **wirable** counter, not on exposure.
3. The tenth template, the gsum final-row closure `L1 · (airGroupValue − gsum − Σ direct)`, one per
   AIR except Mem.
4. A `reason` on every residual in `AirManifest.unlinked_constraints`.

**Hard coupling still applies.** `derived_mixed_link`, `binary_c10_derived_tuples` and the
`DerivedMixed2` shape are still in the extractor, and `Binary/Wiring.lean` consumes c10 through
`BinaryLookupTuple.ofDerived`. Enabling zero-tail for Binary empties those derived tuples; the
`Binary/Wiring.lean` rewrite lands in the same PR or the build goes red.

**Exit:** rounds 32, 38, 46 tie-able (32 and 38/46 already are, through BinaryAdd c5 and Arith c61);
exposure unchanged; wirable counter moved.

---

## W5 · Main's remaining per-row ties — #373 (part) — **mostly done on the baseline**

c39, c40, c43, c44, c45 and c46 are consumed. Open: **c41**, the last of the three constraints
mixing airValue, witness and fixed operands. Then re-run under the re-run set.

---

## W6 · ArithTable rows from the extraction — #375 (part) — **done on the baseline**

`ZiskFv/AirsClean/ArithTable.lean` imports `Extraction.ArithTable` and proves
`rows.toList = arith_table.map extractedRow` by kernel `rfl`; `ArithTableProjections` is untouched.
Verify the one rule before closing: `extractedRow` is a total field-wise map with no numeric
literals and no per-row `match`. Then rounds 5, 26, 33, 36 re-run to 4/4 CAUGHT.

---

## W7 · Close the emitter's deltas on the six AIRs that emit — #370 (part)

*Medium. Unchanged from revision 1.*

1. Range lookups: emit `lookup (Table.fromStatic rangeTableN) row.field`. BinaryAdd's only gap.
2. Named message builder: emit `opBusMessageExpr` / `memBusMessageExpr` as a `@[reducible] def` and
   `push` it, rather than inlining the literal.
3. Nested sub-structs: Binary's 38 slots exceed the `deriving ProvableStruct` field limit.
4. `ElaboratedCircuit` placement: generated `Constraints.lean` or hand-written `Circuit.lean`. Pick
   one.

**Exit:** BinaryAdd, MemAlignByte, MemAlignReadByte generate byte-identical and W0d's report says so;
Binary's `Row.lean` is accepted by the model.

---

## W8 · The constants registry — #366

*Medium, independent. Unchanged from revision 1.*

`trust/constants.toml` in the shape of `trust/weld-airs.toml`: value, PIL citation, the generated
occurrence it pins against, a `pin` theorem, two-sided discovery so an unregistered matching literal
fails. Subsumes the `grep -Fq` lines in `nix/test.nix`. Covers the `OP_*` table in
`ZiskFv/RowShape/Contract.lean` and its partial copies; bus ids 102/103/106/107/124/1000/7890/10/5000;
the five channels carrying no numeric id. `mainFixedCapacity` and `memFixedCapacity` are pinnable
today; `memAlignFixedCapacity` is an extractor item (emit `numRows`), never an exemption.

---

## W9 · MemAlignRom rows from ZisK's own builder — #376 — **done on the baseline**

`build_rows` is gone from `mem_align_rom.rs`; the rows come from executing the pinned pil2-compiler
on the upstream template and observing its fixed columns (`export-mem-align-rom.cjs`), checked by
`nix run .#virtual-table-check`. Verify the docstrings in `mem_align_rom.rs`, the generated header,
and `MemAlignRomTable.lean` no longer read as if a builder were transcribed. Then round 50 re-runs to
CAUGHT with the result on disk.

---

## W10 · Main's 31 register reloads — #373 (part)

*Large. Unchanged from revision 1.*

Two prerequisites, or the tie is not worth having:

- **The airValue name legend.** `air_value_names()` in `main.rs` computes the `(stage, index, name)`
  table and never emits it into the per-AIR header. Emit it, record it through
  `regenerate-weld-columns.py`, add one `airvalue-map` key to `trust/weld-airs.toml`.
- **Per-AIR link index lists** (`def links_Main_reload : List ValidatedLink`), so the tie is one
  statement over `Fin 31`.

Every airValue tie asserts the pair `(slot.name, slot.value)`, never the value alone.
`Mem/RangeWiring.lean`'s airValue-to-column table is a workaround for a missing Clean `ProverData`
term (S3, and D3 in `docs/clean-fork-divergences.md`); the legend pins the name, which is the cheap
half.

---

## W11 · Unblock the emitter's four remaining AIRs — #370 (part)

*Large. Cheapest first.*

1. BinaryExtension: allow an AIR with no `assertZero`. Note the baseline already ties
   BinaryExtension c0-c5 (`BinaryExtension/ExtractedWiring.lean`), so this AIR's generate route is
   lower priority than revision 1 gave it.
2. Mem: diagnose `gsum_debug_data` hint #881.
3. MemAlign: rotated witness cells; `MemAlign/Bridge.lean` shows the two-row shape.
4. Then switch each component over per W14.

---

## W12 · Arith's missing channels — #374

*Large: modelling, not wiring. Unchanged from revision 1.*

Arith c61 is tied on the baseline (`ArithMul/Wiring.lean`), but buses 330/331 still have no channel:
`grep` for them under `ZiskFv/Channels/` returns nothing. Follow S3's route: a typed surrogate range
channel, extend the `SpecifiedRanges` slice, link to c49-64 rather than parse. Settle whether the
emitter learns sub-components or the model merges `ArithMul`/`ArithDiv`.

**Exit:** rounds 38, 46 CAUGHT with results on disk; Arith's exposed count reaches 0 or a declared,
cited residue.

---

## W13 · Main's emitter path — #370 (part)

*Largest. Unchanged.* `FixedCol` operands, plus the 96 `im_direct` compile-time emitter lanes #354
audits. Expect the #354 modelling decisions to be prerequisites.

---

## W14 · Switch the model over — #370 (part)

Per AIR, once W0d reports it byte-identical:

1. Add the `clean-component` step to `nix/extracted-lean.nix`, writing into
   `build/extraction/Extraction/Components/<Air>/`.
2. Register the new modules in **all three** places that would otherwise reject them: the
   `Extraction` globs in `lakefile.toml`, the closed list in `tools/check-generated-modules.sh`, and
   `tools/extraction-coverage/manifest.json` via `check.py --update`.
3. Re-export the generated module from `ZiskFv/AirsClean/<Air>/{Row,Constraints}.lean`.
4. Flip the AIR's `expected = "identical"` entry in `trust/generated-components.toml`.
5. **Then** delete that AIR's weld clauses; when a weld module empties, delete it and its
   `trust/weld-airs.toml` block.
6. Re-run the AIR's rounds from the re-run set.

`Spec.lean`, `Soundness.lean`, `Circuit.lean`, `Bridge.lean` stay hand-written.

---

## W15 · Record the scope exclusions — #373 (part)

The residual file exists from W0c, so this is data entry rather than a new mechanism: the 34
cross-segment constraints become entries in `trust/exposure-residuals.toml` and declared entries in
`trust/defects.md`. Note #354's caveat on `main.pil:452`: it sends on bus 10, which the model does
model, and an absent message there can distort a balance argument. Confirm before recording.

---

## Present on the baseline, outside this plan

`Main/ExtractedTable.lean`, `*/ExtractedRow.lean` and the row constructions in `MainMirrorWeld.lean`
build Clean tables from extracted rows. They are constructions, not ties or generation; they move no
burn-down counter and the ledger must not count them. Do not extend them under this plan without a
separate decision.

## Blocked, tracked elsewhere

- `main.pil:447`, the 31 boundary range checks: **#348**.
- Per-row register ordering, round 27's real home: **#330** with **#19**.
- `bits(N)` declarations lost from PILOUT: **#358**. Not testable by mutation.

---

## Anti-laundering

1. **W4 is +0 on exposure.** Widening produces generated `rfl` lines and zero fidelity. It moves the
   wirable counter only.
2. **Emitting is not switching.** W0d and W7 produce files; W14 makes the model use them.
3. **Compiling is not consuming.** A compiled generated module still breaks on no data change until
   the model reads it. Only rounds re-run to CAUGHT close a data item.
4. **Never delete a weld before the switch-over.**
5. **No `exempt` key.** Every exposed constraint is tied or a residual with an issue and a PIL
   citation; the denominator comes from the extraction and cannot shrink by declaration.
6. **Generating the bus push does not make balance come from ZisK.** `channels_balanced` stays
   caller-supplied; `trust/trusted-base.md` is explicit that the model's `BalancedInteractions` is
   message-exact while ZisK's is challenge-mixed.
7. **"Tied" is not "composed".** The ledger's third state exists so this is a number, not a
   sentence.
8. **Issue bookkeeping is not progress.** Closing a child requires a ledger delta.
9. **Evidence is on disk or it is a hypothesis.** A CAUGHT claim without a
   `mutation-results/round-NN.json` produced from the current checkout is a prediction.
10. **The ledger is generated.** Regenerate and diff; a hand edit is laundering.

---

## Verification

Per PR: `lake build`, `trust/scripts/check-all.sh`, and for generated artifacts `nix run .#populate`
then `trust/scripts/check-all-semantic.sh`. Extractor changes need `nix run .#test`.

Per workstream, the measurement rather than the argument:

- **Exposure**: the ledger diff in every PR that moves it.
- **Re-run set**: after every workstream, `rule_check.py` prints the rounds to re-run; run them; the
  rule scores against current observations.
- **Emitter faithfulness**: W0d's report, byte-exact per AIR.
- **End state**: all 11 misses and round 50 observed CAUGHT on this branch, with round 27's close
  coming through #330/#348.

## Critical files

- `tools/adversarial-mutations/{runner,selftest,semdiff}.py`, `corpus.json`, `diagnostics.json`
- `tools/mutation-sweep/{mutate,semdiff,report}.py`, `rounds/<n>/semdiff.json` (evidence to port)
- `tools/mirror-roundtrip/{check_mirrors,survey,lanes,mirror_parse}.py`
- `tools/extraction-coverage/{check.py,manifest.json}`, `tools/check-generated-modules.sh`
- `trust/scripts/check-module-reachability.py` (the import walk W0c reuses)
- `tools/pil-extract/src/clean_component.rs`: `CleanExprRenderer`, `resolve_bus_push`,
  `render_row_file`, `render_constraints_file`
- `tools/pil-extract/src/lookup_wiring.rs`: `zero_tail_template_scope`, `derived_mixed_link`,
  `binary_c10_derived_tuples`, `direct_assumes_neg_form_matches`
- `tools/pil-extract/src/main.rs`: `CleanComponentCmd`, `air_value_names`
- `nix/extracted-lean.nix`, `nix/test.nix`, `.github/workflows/proofs.yml`
- `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`,
  `ZiskFv/AirsClean/Main/{Wiring,RomWiring,MemoryWiring}.lean`,
  `ZiskFv/AirsClean/{ArithTable,ArithTableProjections,MemAlignRomTable}.lean`
