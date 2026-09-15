# Close the extraction-fidelity gap

*Working copy of this plan lives at `docs/ai/plan/PLAN_EXTRACTION_FIDELITY.md`, which is
gitignored. This tracked copy exists so the plan travels with the branch; keep them in step or
delete this one once the work lands.*

Tracking: umbrella **#368**, children **#369-#376**. Existing issues this builds on: #354, #366,
#348, #358, #268, #328/#103, #330.

## Context

A 52-round adversarial mutation sweep (`docs/adversarial-mutation-sweep.md`, branch
`adversarial-mutation-sweep`) injected one defect at a time into pinned ZisK v0.17.0, recompiled the
circuit, re-ran `tools/pil-extract`, and rebuilt. Of 35 mutations that genuinely changed ZisK's
compiled constraint system, **24 were caught and 11 were missed**.

A rule held over all 31 rounds carrying a semantic diff, without exception: a mutation is caught iff
it changes a constraint that is either named as `<Air>.extraction.constraint_N_every_row` under
`ZiskFv/`, or covered by one of the 6 consumed `ValidatedLink`s. Applied to the whole population:
**167 of 355 extracted constraints are exposed.**

| constraint class | covered | exposed |
|---|--:|--:|
| pure base field | **151** | **1** |
| reaches a challenge (cubic extension of Goldilocks) | **12** | **157** |
| air value only, no challenge | 25 | 9 |

The base-field layer is finished. The gap is the stage-2 constraints — and what is exposed there is
not the logUp algebra, which the project correctly assumes through `channels_balanced`. It is the
**bus tuple** buried inside those constraints. ZisK has no message column; the message exists only as
an expression folded into the accumulator-update constraint.

**Scope.** Taking scope as single-segment RV64IM, no precompiles, no recursion: **34 of the 167 are
out of scope, all Main's, all cross-segment** — the 31 `main.pil:452` currents, c47/c48 on bus 1000,
c142 on bus 106. **133 are in scope.**

**Correction carried in from the sweep.** The report and the previous version of this plan classified
round 27 as a documented scope exclusion. That was wrong. Round 27 mutated `main.pil:334`, the
*per-row* register ordering check, which is single-segment RV64IM. `trust/trusted-base.md:896`
disclaims the *claim*, not the scope. Register ordering is in-scope missing work at #330/#19/#348.
**The honest tally is 11 of 11 misses that should close**, one of them by modelling rather than
wiring. `docs/adversarial-mutation-sweep.md` still needs this fix.

### Why generating beats tying

`Row.lean` and `Constraints.lean` are a transcription of ZisK. `Spec.lean` (what a constraint means)
and `Soundness.lean` (why it is right) are irreducibly human. `pil-extract clean-component` already
writes the first pair from the pilout, is wired into the CLI, and **no pipeline calls it**. Measured
against all ten extracted AIRs: six emit today; BinaryAdd, MemAlignByte and MemAlignReadByte produce
a **byte-identical `Row.lean`**; BinaryAdd's four `assertZero` lines match character-for-character.

For every AIR the emitter covers, three obligations disappear rather than move: the bus tuple stops
being a hand-written claim, the `assertZero` transcription stops existing, and its `*MirrorWeld.lean`
has nothing left to check. This route deletes code — the six weld modules are 5,053 lines.

**Its cost** is that `Soundness.lean` (973 lines) and `Bridge.lean` (5,429) are proofs written against
hand-written text, and regeneration may break proofs that lean on incidental syntax. That cannot be
seen in a diff; it surfaces only at switch-over.

## Burn-down

1. **Exposure** — `trust/generated/exposure-ledger.txt`, per AIR. Today **167 / 355**. Terminal value
   is the count of declared, cited scope exclusions, printed separately.
2. **Generated share** — components whose `Row.lean` and `Constraints.lean` come from the emitter.
   Today **0 of 10**.
3. **Literal inventory** — constants with a kernel `pin` theorem. Today **3 of ~50**.

---

## What `PLAN_S3_LOOKUP_WIRING.md` already settled

The `ValidatedLink` machinery this plan consumes was designed and built under S3
(`docs/ai/plan/archive/PLAN_S3_LOOKUP_WIRING.md`, issues #249/#259/#263/#265/#266/#268). Read it
before W4 or W10. Four of its rulings constrain this plan.

**1. A tie is only meaningful once both sides of the interaction are in a balanced ensemble.**
Clean's `RawChannel.Consistent` applies only then. S3's boundaries are explicit that
`Table.fromStatic` proves a table's data membership and "cannot by itself prove that an unmodelled
sidecar was sent to that table", and that substituting a detached static lookup for a missing
provider "would be anti-laundering". So every tie target must be classified by whether its bus has a
provider in `fullRv64imSoundEnsemble`.

Measured today, the ensemble carries six channels: `MemBus` (10), `OpBus` (5000), `MemAlignRange`
(107), `MemAlignRom` (133), `SpecifiedRangesSlice` (103), `RegisterStepRange` (102). **This is
progress since S3's PR 2a ruling**, which recorded only the operation and memory channels — four
landed afterwards. Still absent: `BinaryTable` (125), `BinaryExtensionTable` (124), `ZiskRomBus`
(7890), MemAlignByte's read bus (88), Arith's range and table buses (330/331), `MAIN_CONTINUATION`
(1000), and bus 106.

Two other PR 2a blockers are also resolved: `Extraction.LookupWiring` is now in `defaultTargets`, and
`SpecifiedRanges`' absence is now recorded rather than silent.

**2. The binding rider.** "A hint is a search witness only. Before any manifest tuple is accepted,
the generated constraint term must equal the standard template instantiated with that hint's tuple
AST. Hint content that lacks that equality is not emitted." This is why every `ValidatedLink` carries
`example : constraint_X = template_X := by rfl`, and it is the backstop that makes W4's allowlist
widening safe. It also settles the tie-strength question: the `rfl` is deliberate, not incidental.

**3. The trust-ledger citation format already exists.** S3 specifies that each application records
"the AIR, hint id, side, bus id, generated manifest entry, accumulator constraint ids, and PIL source
line(s)". W8's registry should use that field list rather than invent one.

**4. Arith's route was designed, not missing.** S3 says of buses 330/331: "The range tuples are
structurally available; link them to c49-64 rather than parse those terms", and "the same bridge
supplies Arith's selected lookup facts". W12 is finishing a designed bridge, not inventing a
representation.

S3 also records that `clean-component` "has no generic range, ROM, virtual-table, or cross-AIR-gsum
emitter" — the same four capabilities W7/W11 measured empirically — and that
`docs/extraction/extractor-notes.md` still describes older skip/stub behaviour and needs reconciling.

---

## Sequencing

Workstreams below run smallest to largest, **with one exception: W0 goes first regardless of size.**
It is the measuring instrument. Without the ledger, every later "closed" is an argument rather than a
number, and the 167 denominator cannot be recomputed after each change.

---

## W0 · Measurement — #369

*First by necessity. Medium size: the harness exists and works; it needs path-cleaning, new
operators, and two gate extensions.*

- Port to `tools/mutation-sweep/`: `mutate.py`, `semdiff.py` (reuses
  `tools/pilout-roundtrip/{pilout_wire,pilout_atoms,poly}.py`), the round driver, and the **round-0
  byte-identity control**. Not in CI — a round is ~10 min of `lake build`. Ship a `regression/`
  subset: the 11 misses plus the 3 commutativity controls.
- Add the operators the sweep lacked, which is why it missed the unpinned bus ids: `BUS_ID_SWAP`
  (44 sites), `SELECTOR_ARG` (29), `MULTIPLICITY`, `AIRVAL`. Drop `CONST_PERTURB` on `bits(n)` —
  pil2-compiler lowers it to a `witness_bits` hint, never a constraint (#358).
- **Exposure ledger**: extend `tools/mirror-roundtrip/check_mirrors.py`, which is already
  `nix/test.nix` step 4/10 and at `:29-31` explicitly scopes out this population. Do **not** add a
  21st check to `trust/scripts/check-all.sh` — its `N/20` labels renumber.
- **Faithfulness diff**: run `clean-component` per AIR, diff against the checked-in component. Needs
  `build/` but not oleans, so `nix/test.nix` (precedent at steps 3/10 and 4/10).

**Exit:** round 0 byte-identical from a clean checkout; the ledger reproduces 167 per AIR; the rule
re-derives at 31/31.

---

## W1 · ArithTable reachability — #375 (part)

*Smallest unit in the programme: two lines plus a gate extension.*

- `tools/pil-extract/src/arith_table.rs:109` emits `import ZiskFv.Fundamentals.Goldilocks`. That
  module has not existed since `84828e96`; `mem_align_rom.rs:420` has the correct
  `ZiskFv.Field.Goldilocks`.
- Add `Extraction.ArithTable` to `lakefile.toml`'s `Extraction` globs.
- Extend module reachability to the generated library, in `nix/test.nix`.
  `trust/scripts/check-module-reachability.py` walks `ZiskFv/` only; four generated modules sit in
  the blind spot (`ArithTable`, `BinaryExtension`, `Buses`, `MemoryBuses`).

**Report "never compiled" and "never consumed" separately.** Making the module elaborate closes
nothing on its own; a data change still breaks nothing until W6.

---

## W2 · Main's three free ties — #373 (part)

*Small: one weld clause and two ties with no prerequisites.*

- **c18** (`main.pil:410`, pure base field) — one `MainMirrorWeld.lean` clause, existing machinery.
- **c42** — the ROM lookup on bus 7890, 11 slots, model counterpart `romMessageExpr`. Witness-leaf
  shape, already a `ValidatedLink`. **The cheapest Main tie; do it first to prove the pattern there.**
- **c46** — the a-side register-pre push on bus 10, counterpart `aRegPreMessageExpr`.

---

## W3 · Binary's byte-table lookups — #372

*Small-to-medium, and the only workstream with three measured misses behind it.*

`Binary/Circuit.lean` defines all eight `lookupMessage0..7` and is in `root_soundness`'s closure;
`Binary/Wiring.lean` ties exactly one. The extractor already emits `link_Binary_7/8/9/11`, consumed
by nothing. Rounds 4 and 25 landed on c10 and were caught; rounds 7, 16 and 22 landed on c8/c9/c11
and were missed.

Two hygiene fixes first, or they multiply across every later tie:

- **`Option` codomain and `List.mapM`.** The `| _ => 0` fallback at `Binary/Wiring.lean:51` is
  unreachable for c10, but `lookupMessage0.cin = 0`. Once a tie covers it, an unrecognised slot
  translates to `0` and the `rfl` passes because the translator lied.
- **Injectivity.** `Option` does not stop a translator collapsing two extraction leaves onto one model
  field — exactly the round 7/16/22 defect. Check mechanically.
- Add the shared `| .add lhs (.constant "0") => f lhs` arm once, replacing the per-slot enumeration at
  `MemAlign/Bridge.lean:62-65`.

Then six ties (c7, c8, c9, c11, and c12/c13 after W4) reusing one widened translator.

**Caveat from S3.** Bus 125 has no provider in `fullRv64imSoundEnsemble`. `Binary/Wiring.lean:104`
finishes it in a *side* ensemble, `binaryTableConnectionEnsemble`, and that module is outside
`root_soundness`'s import closure. So these ties pin which tuple ZisK sends — which is what rounds 7,
16 and 22 test — but they do not yet compose through the main balance. Say so in the PR; do not let
"tied" read as "composed".

**Exit:** rounds 7, 16, 22 → CAUGHT.

---

## W4 · Widen the lookup recognizer — #371

*Medium: a three-line predicate change, a route split, one new template, and one coupled rewrite.*

Follow-up to #268, which disposed Arith c61/c62/c64 as benign circuit findings — correctly — and left
the recognizer gap unfiled.

1. **Split, then widen.** Hoist `direct_assumes_neg_form_matches` out of the
   `if zero_tail_template_scope` block (`lookup_wiring.rs:606-715`); it fires 0 times so it cannot
   regress. Replace the `matches!` allowlist at `:728-730` with a per-route × per-AIR table.
2. **Widen**: expected **79 → 34 `constraintOnly`, 124 → 169 links**, including Arith c61 and
   BinaryAdd c5.
3. **The tenth template — the gsum final-row closure.** Nine constraints share one shape,
   `L1 · (airGroupValue − gsum − Σ direct)`, one per AIR except Mem. Simpler than the four existing
   routes, and load-bearing out of proportion to its count: every other link says the accumulator
   advances correctly; only this says its final value is the AIR's declared contribution.
4. **Record a reason on every residual.** `grep -n reason lookup_wiring.rs` returns nothing today.

**Hard coupling:** enabling Binary turns c10 into a hint-backed `cluster2ZeroTail`, emptying
`link_Binary_10.derivedTuples`, which `Binary/Wiring.lean:74-86` asserts. **That rewrite lands in the
same PR** or the build goes red. It also deletes `binary_c10_derived_tuples` (~95 lines),
`derived_mixed_link`, and the `DerivedMixed2` shape — the extractor's only per-constraint special case.

**Exit:** rounds 32, 38, 46 become *tie-able*. This workstream is **+0 on exposure** — see
anti-laundering.

---

## W5 · Main's remaining per-row ties — #373 (part)

*Medium, and gated on W4.*

- **c43, c44** — b- and store-side pushes on bus 10.
- **c45** — Main's own **request** tuple on operation bus 5000. The centre of RV64IM dispatch.
- **c39, c40, c41** — the only three constraints mixing airValue, witness and fixed operands.

---

## W6 · ArithTable rows from the extraction — #375 (part)

*Medium, with one real unknown.*

Follow `ZiskFv/AirsClean/MemAlignRomTable.lean:28`: `import Extraction.ArithTable` and **define**
`rows` from `arith_table` instead of transcribing 74 literal rows at
`ZiskFv/AirsClean/ArithTable.lean:106-179`. That module is in `root_soundness`'s closure and
`ArithTableProjections` derives `na = MSB(op1)` from it for the signed-MUL defect entry.

The generated type is `List ArithTableRow` (`op : FGL`, fourteen `Nat` fields); the model's is
`Vector (fields 15 FGL) 74`. Defining through makes the bridge definitional rather than proved — the
cost moves to `ArithTableProjections.lean`'s ten `simp [… .rows]` proofs and five *negative* lemmas.
**Spike one negative lemma before committing.** Field order already agrees; I checked row 0.

**Rule:** the `ArithTableRow → fields 15 FGL` conversion is one total field-wise map with no numeric
literals and no per-row `match`, or the transcription is back inside a conversion function.

**Exit:** rounds 5, 26, 33, 36 → 4/4 CAUGHT.

---

## W7 · Close the emitter's deltas on the six AIRs that emit — #370 (part)

*Medium.*

1. **Range lookups** — emit `lookup (Table.fromStatic rangeTableN) row.field`. BinaryAdd's only
   functional gap.
2. **Named message builder** — emit `opBusMessageExpr` / `memBusMessageExpr` as a `@[reducible] def`
   and `push` it, rather than inlining the literal. Other modules reference that name.
3. **Nested sub-structs** — Binary's 38 slots exceed the `deriving ProvableStruct` field limit.
4. **`ElaboratedCircuit` placement** — generated `Constraints.lean` or hand-written `Circuit.lean`.
   Pick one.

**Exit:** BinaryAdd, MemAlignByte, MemAlignReadByte generate byte-identical; Binary's `Row.lean` is
accepted by the model.

---

## W8 · The constants registry — #366

*Medium, independent of everything else.*

`trust/constants.toml` in the shape of `trust/weld-airs.toml`: value, PIL citation, the generated
occurrence it pins against, a `pin` theorem, two-sided discovery so an unregistered matching literal
fails. Subsumes the eight `grep -Fq` lines at `nix/test.nix:94-112`.

Covers the 35-entry `OP_*` table at `ZiskFv/RowShape/Contract.lean:127+` and its three partial copies;
bus ids 102/103/106/107/124/1000/7890/10/5000; the five channels carrying **no numeric id at all**.
`mainFixedCapacity` and `memFixedCapacity` are pinnable today (`Expr.constant "4194304"` occurs 104
times in `LookupWiring.lean`); `memAlignFixedCapacity` is not — record it as an extractor item (emit
`numRows`), never an exemption.

---

## W9 · MemAlignRom PIL evaluator — #376

*Medium-large Rust, fully independent, and the only data gap under `root_soundness`. Start it in
parallel from day one.*

`mem_align_rom.rs:259-376` reimplements ZisK's ROM row builder, with segment boundaries hard-coded as
41/101/134/189 where PIL derives them from `spsize`. Round 50 swaps `OFFSET`/`WIDTH` in the PIL
generator and `MemAlignRom.lean` comes out byte-identical.

Replace `build_rows` with an evaluator over the PIL source: bounded `for`, `if`/`else`, `%`, array
index, `2**j`; no recursion, no witness references, no field arithmetic. Alternative is invoking
`pil2-compiler` for one table. Also fix the docstrings at `mem_align_rom.rs:1-7`, `:425-429`, and
`MemAlignRomTable.lean:8-12`, which read as if the builder were *read*.

**Exit:** round 50 → CAUGHT. The 256 rows should be unchanged, so nothing downstream moves.

---

## W10 · Main's 31 register reloads — #373 (part)

*Large: two extractor features, then one quantified tie.*

`main.pil:444-453` unrolls once per register; every one of the 31 contributes the same triple. The
reload push (c50+3k) is modelled as `RegisterBoundary.reloadMessageExpr`, linked, and untied.

Two prerequisites, or the tie is not worth having:

- **The airValue name legend.** The generated module already carries
  `{ name := "Main.last_reg_mem_step[0]", value := Expr.add (Expr.airValue 70) }` — ZisK's own symbol
  from pilout's `name_exprs` (`lookup_wiring.rs:462-481`), and it moves with a mutation.
  `air_value_names()` at `main.rs:2954` already computes the table; it is never emitted into the
  per-AIR header the way the witness legend at `Extraction/Main.lean:13-59` is. Emit it, record it
  through `regenerate-weld-columns.py`, add one `airvalue-map` key to `trust/weld-airs.toml`. Same
  registry, same regenerator, no new check number. This also closes the exclusion `[air.MainExposed]`
  states in prose.
- **Per-AIR link index lists** (`def links_Main_reload : List ValidatedLink := [...]`), so the tie is
  one statement over `Fin 31` rather than 31 copies, and 31 generated names do not enter the TCB.

Every airValue tie asserts the **pair** `(slot.name, slot.value)`, never the value alone.

**Why `Mem/RangeWiring.lean`'s airValue-to-column table looks like fiat.** S3's PR 2a ruling records
the cause: the Clean expression language has no `ProverData` term, while the selected Mem segment
reads its values from shared `ProverData`. The hard-coded mapping is a workaround for a missing Clean
facility, and S3 flags that closing it properly may need a third fork divergence (D3 in
`docs/clean-fork-divergences.md`). The airValue legend above pins the *name*, which is the cheap half;
the `ProverData` term is the expensive half and should be scoped separately if it blocks.

---

## W11 · Unblock the emitter's four remaining AIRs — #370 (part)

*Large. Cheapest first; each unlocks a bigger AIR.*

1. **BinaryExtension** — allow an AIR with no `assertZero` constraints; it is pure bus traffic. The
   model also has eight inline anonymous structure literals
   (`BinaryExtension/Constraints.lean:76-110`) that need naming.
2. **Mem** — diagnose `gsum_debug_data` hint #881. (Mem's exposure is already 0; this is for the
   generate route, which would delete its weld.)
3. **MemAlign** — rotated witness cells. `MemAlign/Bridge.lean:208-235` shows the two-row shape.
4. Then switch each component over per W12.

---

## W12 · Arith's missing channels — #374

*Large: modelling, not wiring.*

Arith has 16 exposed constraints and 13 emitted links, and **none can be tied, because the model has
no channel to tie them to.** Buses 330/331 go through an in-component
`lookup (Table.fromStatic rangeTable16)` (`ArithMul/Constraints.lean:272-287`); `grep` for 330 or 331
under `ZiskFv/Channels/` returns nothing.

S3 designed the route and did not build it: map a recognised range entry to a typed surrogate range
channel `(range-id, value, multiplicity, provenance)`, extend the `SpecifiedRanges` slice that
already maps range ids 102/103 to the constructive `RangeTables`, and "link them to c49-64 rather
than parse those terms". Follow that rather than inventing a representation. Note S3's two-part
component route: row inputs keep the local `lookup (Table.fromStatic table)` pattern with component
soundness projecting the fact, while sidecar values need the recognised assumes-side message plus
full-ensemble balance to select the provider row.

Also settle whether the emitter learns named sub-components or the model merges its
`ArithMul`/`ArithDiv` split, since `clean-component` emits a single `Arith`.

**Exit:** rounds 38, 46 → CAUGHT; Arith's exposed count reaches 0 or a declared, cited residue.

---

## W13 · Main's emitter path — #370 (part)

*Largest. Main is 106 of the 167.*

`FixedCol` operands, plus the 96 `im_direct` compile-time emitter lanes #354 audits. Expect the #354
modelling decisions to be prerequisites, not side work.

---

## W14 · Switch the model over — #370 (part)

Per AIR, once it generates byte-identical:

1. Add the `clean-component` step to `nix/extracted-lean.nix`, writing into
   `build/extraction/Extraction/Components/<Air>/`.
2. Re-export the generated module from `ZiskFv/AirsClean/<Air>/{Row,Constraints}.lean`.
3. **Then** delete that AIR's weld clauses; when a weld module empties, delete it and its
   `trust/weld-airs.toml` block.
4. Re-run that AIR's regression rounds.

`Spec.lean`, `Soundness.lean`, `Circuit.lean`, `Bridge.lean` stay hand-written.

---

## W15 · Record the scope exclusions — #373 (part)

Do this last, when the in-scope set has stopped moving. The 34 cross-segment constraints —
31 × `main.pil:452`, c47/c48 on bus 1000, c142 on bus 106 — become declared, cited entries in
`trust/defects.md`, which is what #354 asks for. Note #354's caveat on `main.pil:452`: it sends on
bus 10, which the model *does* model, and an absent message there can distort a balance argument
rather than merely narrow the claim. Confirm before recording.

---

## Blocked, tracked elsewhere

- **`main.pil:447`**, the 31 boundary range checks — **#348**. Modelling it makes `RegisterBoundary` a
  bus-102 consumer, deletes `registerBoundary_table_interactionsWith_registerStepRange_nil`, changes
  the provider case split, and adds a provider row per register to all seven witnesses.
- **Per-row register ordering / the bus-102 descent** — **#330**, with #19. Round 27's real home.
- **`bits(N)` declarations lost from PILOUT** — **#358**. Not testable by mutation.

---

## Anti-laundering

1. **W4 is +0 on exposure.** Widening the allowlist produces 45 more generated `rfl` lines and zero
   fidelity — the module already carries 124 and 11 mutations still got through. Report it on a
   separate "wirable" counter. The ledger numerator is *constraints named-or-consumed by `ZiskFv/`*,
   never *constraints the extractor linked*.
2. **Emitting is not switching.** W7 produces files; W14 makes the model use them. Two numbers.
3. **W1 is not W6.** A compiled `Extraction.ArithTable` still breaks on no data change until the model
   reads it. Only rounds 5/26/33/36 at 4/4 CAUGHT closes it.
4. **Never delete a weld before the switch-over.** That is a straight loss of coverage.
5. **No `exempt` key in any registry.** Every exposed constraint is `tied` or
   `blocked-by = <issue> + <cited prerequisite>`; the count prints in the pass line; the 167
   denominator comes from the extraction, so it cannot shrink by declaration.
6. **Generating the bus push does not make balance come from ZisK.** `channels_balanced` stays
   caller-supplied; `trust/trusted-base.md:785` is explicit that the model's `BalancedInteractions`
   is message-exact while ZisK's is challenge-mixed. Generating pins *which tuple* is in the argument
   and nothing more. Say both sentences in the PR.
7. **"Tied" is not "composed".** A tie on a bus with no provider in the ensemble pins which tuple
   ZisK sends and nothing more. Per S3, a detached `Table.fromStatic` standing in for the missing
   provider is laundering. State the channel's ensemble status in every tie PR.
8. **Issue bookkeeping is not progress.** #368-#376 record gaps. Closing a child requires a ledger
   delta.

---

## Verification

Per PR: `lake build`, `trust/scripts/check-all.sh`, and for generated artifacts
`nix run .#populate` then `trust/scripts/check-all-semantic.sh`. Extractor changes need
`nix run .#test`.

Per workstream, the measurement rather than the argument:

- **Emitter faithfulness** — generated versus checked-in component, per AIR, byte-exact.
- **Ties and switch-overs** — re-run that AIR's `tools/mutation-sweep/regression/` rounds, require
  CAUGHT. W3 closes 7/16/22; W4+W5 closes 32; W12 closes 38/46; W6 closes 5/26/33/36; W9 closes 50.
- **Exposure** — `trust/generated/exposure-ledger.txt` diff in every PR that moves it.
- **The decision rule** — re-derive 31/31 after each workstream; every one changes its inputs, so a
  rule that stops holding is itself a finding.
- **End state** — all 11 misses re-run to **11 CAUGHT**, with round 27's close coming through
  #330/#348 rather than this plan.

## Critical files

- `tools/pil-extract/src/clean_component.rs` — `render_row_file:518`, `render_constraints_file:607`,
  `resolve_bus_push:376`, `CleanExprRenderer:115`
- `tools/pil-extract/src/main.rs` — `CleanComponentCmd:170` (the `--channel` flag that makes the three
  `MemAlign*Byte` AIRs emit), `air_value_names:2954`
- `tools/pil-extract/src/lookup_wiring.rs` — `:606-730` route gating, `:462-481` slot-name provenance,
  `:739-830` the c10 special case W4 deletes
- `tools/pil-extract/src/{arith_table.rs:109,mem_align_rom.rs:259-376}`
- `nix/extracted-lean.nix` — where the `clean-component` step goes
- `trust/scripts/check-weld-column-maps.py` + `trust/weld-airs.toml` — the gate template to copy
- `tools/mirror-roundtrip/check_mirrors.py:29-31` — the scope exclusion the ledger extends
- `ZiskFv/AirsClean/Binary/{Wiring,Circuit,Row}.lean` — the translator, the eight messages, the
  nested sub-struct shape
- `ZiskFv/AirsClean/{ArithTable,ArithTableProjections,MemAlignRomTable}.lean`
