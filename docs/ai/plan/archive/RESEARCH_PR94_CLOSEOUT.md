# Research Report — Properly Closing Out PR #94 (Endgame P4-PR1)

Status: research input for the PR #94 fix plan. Author: reviewer (opus-manager).
Date: 2026-06-14. Subject: `origin/endgame-p4-pr1` @ `da0dfc2c` (PR #94) and the
`origin/endgame-p4-pr2` @ `6c414ffa` stack built on top of it.

This report is the evidence base for a bulletproof fix plan. It is deliberately
blunt: the headline conclusion overturns the premise of my own original review
("a relabel that just needs the derivation wired in").

---

## 0. Executive verdict

**PR #94 is not fixable by a small patch, and it must not be merged as written.**

Three findings, each independently load-bearing:

1. **The execution bus does not exist in the formal model.** The Clean ensemble
   `fullRv64imEnsemble` finishes exactly two channels — OpBus and MemBus. The
   four "branch" facts PR #94 carries (`h_exec_len`, `h_e0_mult`, `h_e1_mult`,
   `h_nextPC_matches`) are assertions about a legacy `ExecutionBusEntry` list
   (`execRow`) that is wired to no channel and constrained by nothing. They are
   **not derivable from `trace.constraints`/`trace.balanced` today** — there is
   no trace object to derive them from. The bucket-(a) classification of
   "exec-row shape / PC-nextPC bridge" in `trust/envelope-burden-audit.md` is
   **aspirational and currently false** against the real ensemble.

2. **The laundering is systemic, not a PR1 stumble.** PR2 (which adds +10,733
   lines to `AcceptedTrace.lean`) built a *genuine* balance-fed derivation — but
   **only for the op-bus provider-row match**. The four exec-bus facts are
   carried as caller-supplied fields in **all 37** `*RowBinding` structures and
   forwarded through `.promises` into the envelope constructor, never derived.
   PR2 therefore contains **no template** that would fix the branch facts.

3. **The branch next-PC is genuine multi-piece work; extracting more does NOT
   shortcut it.** [VERIFIED 2026-06-14 — this supersedes BOTH my original vague
   "large prerequisite" AND my over-optimistic §5a "≈rfl wiring". The verified
   middle is detailed in §5b.] ZisK's cross-row PC constraint IS extracted, but
   only into the **legacy `Circuit` model that nothing live imports**; the LIVE
   Clean `Air.Flat.Component` ensemble that `trace.constraints` ranges over is
   **structurally single-row** and cannot represent a cross-row constraint at
   all. So `pc_handshake` is NOT in `trace.constraints` and is NOT derivable
   today — getting it there needs a framework change (rotation-capable component
   or shadow-column encoding), which is **general to every opcode's next-PC**,
   not branch-specific. Separately, the branch `flag` (`a==b`) needs a **missing
   Binary-EQ 8-byte aggregation lemma + an EquivCore re-plumb** (templated by the
   existing SLT path, but real). Plus the `bus_effect`/`ExecutionBusEntry`
   conclusion-form decision (a foreign openvm import — ZisK has no execution
   bus). None of the three is shortened by extracting more production code.

Net: PR #94 "constructs the BEQ arm from an accepted trace" only nominally. Its
trust content is identical to the pre-P4 `OpEnvelope` hypotheses — the trust was
**moved** from top-level promise binders into deep `BeqRowBinding` /
`MainRowProvenance` fields, not **discharged**. By the project's own
anti-laundering metric this PR is net-zero on the facts it claims to derive.

What IS real and worth salvaging: PR2's op-bus provider-row derivation
(zero new axioms, genuinely consumes `trace.balanced`).

---

## 1. What PR #94 claims vs. what it does

Claim (PR body / `AcceptedTrace.lean` design): define `AcceptedTrace =
EnsembleWitness (fullRv64imEnsemble …) + constraints + balanced`, then build a
construction `construction_beq : AcceptedTrace → … → OpEnvelope` that
**discharges derivable bucket-(a) evidence from the accepted trace**, leaving
only named bucket-(b) residuals.

Reality (`git show origin/endgame-p4-pr1:ZiskFv/Compliance/AcceptedTrace.lean`):

```
def construction_beq (trace) (binding : ProgramBinding trace) (i) (h_tag) : OpEnvelope … :=
  let b := binding.beq i h_tag
  OpEnvelope.beqOfExtractedShape
    b.input b.ops b.provenance
    b.h_op b.h_external b.h_m32 b.h_set_pc b.h_store_pc b.h_jmp_offset2
    b.promises
```

- The body uses **only** `binding.beq i h_tag` (a fully caller-supplied
  `BeqRowBinding`). It threads those fields straight into the existing
  `OpEnvelope.beqOfExtractedShape` (`AeneasBridgeTrust.lean:483-503`), which
  builds `BranchPromises` via `of_aligned_BEQ` — a **1:1 field passthrough**
  (`EquivCore/Promises/BranchHelpers.lean:60-102`).
- `trace.constraints` — **DEAD** (only the declaration at `AcceptedTrace.lean:30`).
- `trace.balanced` — **DEAD** (only the declaration at line 31).
- `ProgramBinding.mainTable_mem`, `.mainTable_component` — **DEAD**.
- `mainOfTable` is used only as the **type-level** `m` index of `OpEnvelope`,
  never its row content.
- The new bridge lemmas `rowAt_mainOfTable` (`Balance.lean:1961`) and
  `opBus_row_Main_mainOfTable` (`Balance.lean:1973`) — the lemmas that would
  actually connect `mainOfTable`'s columns to concrete trace rows — are **dead
  code** (`opBus_row_Main_mainOfTable` has zero callers tree-wide).

The `constraints`/`balanced` fields and the `mainTable_*` membership fields make
the signature *look* trace-grounded; the proof term ignores all of them.

---

## 2. Finding 1 — the execution bus is not in the model

- `fullRv64imEnsemble` finishes exactly two channels (`AirsClean/FullEnsemble.lean:124-125`):
  ```
  |>.addFinishedChannel OpBusChannel.toRaw
  |>.addFinishedChannel MemBusChannel.toRaw
  ```
  `witness.BalancedChannels` quantifies only over `[MemBusChannel.toRaw,
  OpBusChannel.toRaw]` (hard-coded in `opBus_balanced_of_witness` /
  `memBus_balanced_of_witness`).
- The Clean Main component emits interactions only on those two channels
  (`AirsClean/Main/Circuit.lean:577-581`); there is no exec-bus emission
  anywhere under `AirsClean/Main/`.
- `Interaction.ExecutionBusEntry` (`Airs/Bus/Interaction.lean:38-46`) is a legacy
  openvm-fv/RV32-derived struct; its own docstring says so. It is not a channel
  message and is connected to nothing.
- In `BeqRowBinding`, `execRow : List (Interaction.ExecutionBusEntry FGL)` is a
  bare field (`AcceptedTrace.lean:53`); nothing ties it to `mainTable` or any
  constraint. `h_exec_len`/`h_e0_mult`/`h_e1_mult` (lines 70-72) and
  `h_nextPC_matches` (lines 73-75) are assertions about this phantom list.

**Consequence:** these four facts cannot be derived from the current
`AcceptedTrace`. The audit row in `trust/envelope-burden-audit.md` ("Branch …
exec-row shape, PC/nextPC bus bridge" = bucket-(a)) describes a derivation that
the current model cannot perform. The audit needs correction (see §7).

---

## 3. Finding 2 — the laundering is systemic (PR1 + PR2, 37×), with a real op-bus core

PR2 architecture has **two tiers**, only one of which is genuine:

- **Tier 1 (REAL): op-bus provider-row match.** `exists_construction_<op>_from_balance`
  wrappers (e.g. `exists_construction_sub_from_balance`,
  `AcceptedTrace.lean:10046`) take only `(trace, binding, i, h_tag)`, genuinely
  consume `trace.witness/constraints/balanced`, call
  `exists_<...>_provider_row_matches_<op>_from_binding`
  (`AcceptedTrace.lean:9492`), which bottoms out in real, axiom-free permutation
  theorems in `Balance.lean` (`exists_staticBinary_provider_row_matches_legacy_main_of_sub_active_main_row_interaction`,
  `Balance.lean:2612`). Conclusion: existence of a provider row whose
  `opBusMessage` matches the Main row's `opBus_row_Main`, and the op-bus
  multiplicity `mainInteraction.mult = -1`. **This is honest trust reduction.**
  Baseline axioms unchanged (6 lines → 6 lines; 0 axioms in `Balance.lean`).

- **Tier 2 (FAKE): exec-bus bucket.** `h_exec_len`/`h_e0_mult`/`h_e1_mult`/
  `h_nextPC_matches` remain caller-supplied **fields** in every `*RowBinding`
  (SUB `AcceptedTrace.lean:941-946`, XOR `:520-524`, SLTU `:1723-1727`), copied
  verbatim into the promises bundle (`SubRowBinding.promises`,
  `AcceptedTrace.lean:1097-1100`). A tree-wide count: each of the four strings
  appears exactly **37** times — once per binding — and **never as a discharged
  proof obligation**. There is no theorem anywhere proving
  `execRow[0]!.multiplicity = -1` etc.

**Implication for the fix:** "apply PR2's template to BEQ" does **not** fix the
branch facts — the template only derives the op-bus match, which BEQ branches
don't even use (the branch `ops`/`OpEnvelope` arm carries no `Valid_Main`/`r_main`
payload; see §5). The op-bus salvage matters for the *arithmetic/logic* families,
not for branches.

---

## 4. Finding 3 — the deepest leak is the `MainRowProvenance` bundle

`BeqRowBinding` field 7 is `provenance : MainRowProvenance main r_main`
(`AcceptedTrace.lean`), and `MainRowProvenance` (`Compliance/RowProvenance.lean:123-169`)
is itself a fully caller-supplied record with ~27 `Prop` equality fields
(`row_eq : mainRow.core = Main.rowAt main r_main`, `op_eq`, `is_external_op_eq`,
`m32_eq`, …). None are derived. So `BeqRowBinding` transitively smuggles the
**entire Main-row decode/activation bundle** as premises. The six explicit row
pins on the binding (`h_op … h_jmp_offset2`) plus `h_target_aligned` are likewise
bucket-(a) facts handed in for free.

This is the part that **is** derivable today (unlike the exec bus): the bridge
lemmas `rowAt_mainOfTable` / `opBus_row_Main_mainOfTable` exist precisely to
connect `mainOfTable`'s columns to concrete trace rows, and `trace.constraints`
carries the Main component's per-row constraints. They were simply never wired
in. **Caveat to verify before the plan finalizes:** confirm that the Main-row
pins for BEQ actually close from `trace.constraints` via these bridge lemmas
(the lemmas exist; the closing proof has not been attempted).

---

## 5. Finding 4 — `nextPC_matches` is cross-row; the correct proof is orphaned

This is the scope crux.

- **What the four facts are FOR** (in the proven `equiv_BEQ`,
  `EquivCore/Beq.lean:85-112` → `bus_effect_matches_sail_beq`,
  `Airs/Bus/BusEmission.lean:78-114`):
  - `exec_len=2`, `e0_mult=-1`, `e1_mult=1` only gate the structural `if` in
    `bus_effect` (`SailSpec/BusEffect.lean:42`) — they assert the *shape* of a
    list the real Clean circuit never produces. **Pure artifacts** of the
    `bus_effect`/`ExecutionBusEntry` interpreter.
  - `nextPC_matches` is the one semantically real fact: `bus_effect` writes
    `Register.nextPC ← exec_row[1]!.pc` (`BusEffect.lean:121-127`); Sail writes
    `execute_BEQ_pure.nextPC`; this equates them (`BusEmission.lean:110`).
- **Why it's hard:** the Main row (`AirsClean/Main/Row.lean:32-51`) has `pc`,
  `set_pc`, `jmp_offset1/2`, `flag` columns but **no next-PC column** — next-PC
  is the *next row's* `pc`, tied by the cross-row handshake `next_pc = pc +
  jmp_offset2 + flag*(jmp_offset1 − jmp_offset2)` (`Airs/Main/Main.lean:185-207`,
  `main.pil:410`).
- **The correct derivation exists and is proven** — `branch_eq_compositional`
  (`ZiskCircuit/BranchEqual.lean:77-85`) derives exactly the BEQ taken/not-taken
  next-PC — **but it is orphaned**: it appears only in docstrings of the six
  branch EquivCore proofs (`Beq.lean:22`, `Bne.lean:25`, …), never in a proof
  body; it operates on the v1 opaque-thunk `Valid_Main`; `pc_handshake_at` is
  itself a caller-supplied hypothesis (`AirsClean/Main/CrossRow.lean:34-36`); and
  the Clean Main component is single-row, with cross-row PC continuity explicitly
  "outside these proofs" (`Circuit.lean:26`, `CrossRow.lean:9-12`).
- It also defers the Binary-SM `flag = (a==b)` correctness as an external
  `h_flag_correct` parameter (`BranchEqual.lean:46-50`) — another undischarged
  obligation, routed through the OpBus.

**Honest scope to discharge `nextPC_matches` from the trace:**
1. Add a cross-row/adjacency obligation to the Clean ensemble (currently absent).
2. Discharge the Binary-SM flag link through the OpBus.
3. Re-root `branch_eq_compositional`/`pc_handshake` onto the Clean single-row
   component + the new adjacency layer.
4. Re-state the canonical conclusion away from `bus_effect`/`exec_row` (this
   touches all 63 opcodes, since `state_effect_via_channels = bus_effect.2` by
   `rfl`, `StateEffect.lean:81-97`) — at which point `exec_len/e0_mult/e1_mult`
   vanish as artifacts.

This is a **large prerequisite**, not a branch-local fix. The good news: the
mathematical core is already proved; the work is re-rooting it onto Clean +
adjacency, not inventing it.

> **NOTE — superseded by §5a.** The "large prerequisite / add a cross-row
> adjacency obligation to the Clean ensemble" framing above was WRONG. The
> cross-row constraint is already extracted; see §5a for the corrected scope.

---

## 5a. Finding 4 (corrected) — "extract more?" → the constraint is ALREADY extracted; the gap is consumption, not extraction

The project lead asked the right question: *are we working around something not
being extracted?* For the cross-row PC handshake, **yes — but the fix is to
consume what is already extracted, not to extract more.** Two investigations
(extractor mechanics + ZisK architecture) establish:

**(1) The cross-row PC-transition constraint is in the extracted output.**
`build/extraction/Extraction/Main.lean:96-99` (`constraint_18_every_row`) is the
verbatim render of the production PIL `main.pil:409-410`:
```
const expr expected_current_pc =
    'set_pc * ('c[0] + 'jmp_offset1)
  + (1 - 'set_pc) * ('pc + 'jmp_offset2)
  + 'flag * ('jmp_offset1 - 'jmp_offset2);
(1 - SEGMENT_L1) * (pc - expected_current_pc) === 0;
```
The extractor handles negative row rotations faithfully: each `'`-cell becomes a
`(column := k) (row := row - 1)` access (`tools/pil-extract/src/main.rs:736-765`),
documented in `docs/extraction/extractor-notes.md:373-394`, which names this very
PC-handshake constraint as the motivating case. So this is **not** an extractor
limitation and **not** under-extraction — it is extracted (verdict:
ALREADY-EXTRACTED-UNUSED).

**(2) The Clean layer ignores it.** `constraint_18_every_row` is referenced
nowhere under `ZiskFv/AirsClean/`. The Clean Main component is deliberately
single-row and emits only the 9 per-row asserts + ROM/mem/op-bus channels
(`AirsClean/Main/Constraints.lean:12-13`: "Cross-row pc_handshake stays in Bridge
as a separate adjacency theorem"). `pc_handshake_at` (`AirsClean/Main/CrossRow.lean:68-73`)
is hand-transcribed and only proven `rfl`-equal to the v1 predicate; it enters
every downstream branch proof as a **free caller hypothesis** (`h_handshake`,
consumed at `BranchArchetype.lean:98`, `BranchEqual.lean:83-85`). Nothing proves
it from `constraint_18`.

**(3) ZisK has no execution bus — `bus_effect`/`ExecutionBusEntry` is foreign.**
ZisK has exactly three buses: `OPERATION_BUS_ID=0`, `ROM_BUS_ID=1`,
`MEM_BUS_ID=2` (`zisk/common/src/bus/data_bus_*.rs`). The op-bus payload is
`[op, op_type, a, b]` — **no next-PC on any bus**. The branch next-PC is the
committed Main `pc` column, related row-to-row by `constraint_18`; the comparison
`flag` is produced by the Binary SM (`binary.pil:156`, `proves_operation(…,
flag:cout)`) and consumed by Main over the operation bus (`main.pil:367-374`),
then feeds the PC multiplexer. The Lean `exec_row[1]!.pc` has no ZisK counterpart
— it is an openvm import (`Airs/Bus/Interaction.lean:38-46`).

**Corrected scope to discharge the branch next-PC (pure Lean; no extractor work,
no new infrastructure):**
1. **Bind named Main accessors to the extracted projections.** In the P4 world
   this already exists in embryo: `mainOfTable` defines `Valid_Main` columns as
   projections of the trace rows, and `rowAt_mainOfTable` (`Balance.lean:1961`,
   currently dead) binds `Main.rowAt (mainOfTable …)` to the evaluated row. The
   missing link is `constraint_18_every_row (from trace.constraints) →
   pc_handshake_at (mainOfTable …)` — an ≈`simp`/`rfl` derivation because
   `pc_handshake_at` is the literal closed form of `constraint_18`.
2. **Wire the proven-but-orphaned `branch_eq_compositional`** (`BranchEqual.lean:77-85`)
   into the actual equiv path to turn the handshake into the BEQ taken/not-taken
   next-PC.
3. **Discharge the `flag` link via the modeled op-bus.** `flag = (a==b)` is the
   Binary-SM result served on the operation bus. The op-bus IS an ensemble
   channel and PR2 built genuine balance-fed op-bus provider-match derivation;
   the residual is Binary-SM comparison correctness (`cout = (a==b)` for OP_EQ),
   which is in-scope existing AIR-equivalence work, not new infrastructure.
   **Verify whether that Binary comparison-correctness lemma already exists.**
4. **Handle the `bus_effect` conclusion form.** This is the one genuine remaining
   design choice: either (i) ground `exec_row` as a projection of the real Main
   next-row pc so `h_nextPC_matches` becomes derivable while keeping the current
   conclusion shape, or (ii) restate the canonical conclusion off `bus_effect`
   onto the ZisK-native channels (touches all 63 opcodes; the proper long-term
   retirement of the openvm import). `exec_len/e0_mult/e1_mult` are artifacts
   that vanish either way.

**Net correction to §0/§5/§8:** the branch next-PC is **not** a large
build-new-infrastructure prerequisite. It is consumption of an already-extracted
constraint + already-proven lemmas + the already-modeled op-bus. The only open
design decision is the `bus_effect` conclusion form (step 4). This materially
strengthens Option A (the residual can be genuinely *derived*, not just named)
and shrinks Option B to "wire up existing pieces + decide the conclusion form."

**Generalization worth flagging:** `pc_handshake`/`constraint_18` being
assumed-not-derived affects **every** opcode's next-PC, not just branches.

> **§5a is partially SUPERSEDED by §5b.** The §5a claim that deriving the
> handshake is "pure Lean wiring" / "≈rfl" and that "P4's `trace.constraints` is
> the natural place to discharge it" is WRONG — verified below. The constraint is
> extracted, but the live Clean model can't hold it. The §5a facts about *where
> the constraint lives* and *ZisK having no exec bus* stand; the §5a *difficulty
> estimate* does not.

---

## 5b. Verification (2026-06-14) — the §5a "≈rfl wiring" estimate was wrong on two counts

I ran two targeted checks before locking the plan (the discipline paid off — they
overturned the optimistic §5a difficulty estimate).

### Check A — is `constraint_18` actually in `trace.constraints`? **NO.** Verdict: NEEDS-FRAMEWORK-CHANGE.
- The Clean Main component used by the ensemble
  (`Main.componentWithRomMemAndOpBus` → … → `main`,
  `AirsClean/Main/Constraints.lean:27-36,427-431`) is **nine single-row
  `assertZero`s + ROM/mem/op-bus channels — zero cross-row constraints.** The
  header says it outright (`Constraints.lean:12-13`).
- `trace.constraints` = `EnsembleWitness.Constraints` = `∀ table, ∀ row,
  component.ConstraintsHold (environment row)`, and `environment row =
  Environment.fromArray row table.data` is built from a **single row**
  (`Clean/Air/FlatComponent.lean:147,170-172`; `FlatEnsemble.lean:210`). The live
  Clean component model has **no rotation channel** — the previous row is
  structurally invisible; there is no `Var` that reaches `row-1`.
- The extracted `constraint_18_every_row` (`build/extraction/Extraction/Main.lean:96-99`)
  is parameterized over the **legacy `[Circuit F ExtF C]` typeclass** with
  `(row := row - 1)` accessors, and **nothing under `ZiskFv/` imports
  `Extraction.*`** — it is a dead reference rendering of `main.pil`, not a live
  constraint.
- Consequence: `trace.constraints → pc_handshake_at (mainOfTable …) row` has **no
  source for its conclusion** — it is not ≈rfl, it is *unprovable from the current
  ensemble*. The `mainOfTable`/`rowAt_mainOfTable` column bridge is fine (single-
  row), but there is nothing cross-row to bridge *from*.
- To make it derivable you must FIRST give the Clean model cross-row capability:
  (a) a real previous-row rotation accessor in `Air.Flat.Component` /
  `Table.environment` (a framework change + re-prove the ensemble wiring), or
  (b) previous-row shadow witness columns + an inter-row equality (not per-row
  expressible → reduces back to (a) or a trusted copy argument). Either is a
  genuine model change. **This ceiling is general** — it blocks every cross-row
  property (all next-PCs, segment continuation), so it is a foundational endgame
  item, not a branch fix.

### Check B — is the Binary EQ flag correctness proven? **PARTIAL — effectively a gap.** Verdict: NEEDS-AGGREGATION-LEMMA.
- Proven: the **per-byte** EQ rule `wf_EQ` (`Airs/Tables/BinaryTable.lean:221-231`,
  proof `rowOfIndex_wf_EQ` at `AirsClean/BinaryTable.lean:1149-1241`).
- Missing: any **8-byte aggregation** `binary_eq_chunks_eq_bv_eq_of_wf`. The
  signed/unsigned comparison analogs exist (`binary_lt_chunks_eq_bv_slt_of_wf`
  `BinaryPackedCorrect.lean:1910`, `binary_ltu_…:1654`) — EQ has none.
- `equiv_BEQ` (`EquivCore/Beq.lean:85-112`) never touches the Binary SM; it takes
  the flag's effect as the free `BranchPromises.nextPC_matches` promise. Zero
  `consumer_byte_match_chain` hypotheses. `h_flag_correct` is **comment text
  only** (`BranchEqual.lean:19,49,74`), and the row-shape contract leaves `flag`
  unconstrained ("output of the Binary SM", `RowShape/Contract.lean:761,805,863`).
- Even with PR2's op-bus provider-match, a match lands you on the 8 per-byte
  `wf_EQ` facts; nothing turns them into `flag = 1 ↔ a == b` over 64 bits. This is
  case (ii): a real gap.
- Scope to fill (moderate, well-templated): write the EQ aggregation lemma
  mirroring the proven LT/LTU chain (8-byte induction with the final-byte
  polarity flip), a `BinaryCompare`-style consumer, and re-plumb Beq/Bne EquivCore
  to take byte-chain hypotheses and **derive** `nextPC_matches` — exactly the
  shape `equiv_SLT_of_wf` (`EquivCore/Slt.lean:71`) already follows.

### Combined verdict
Deriving the branch next-PC honestly = **framework cross-row capability (general,
real) + Binary-EQ aggregation lemma & re-plumb (moderate, templated) + bus_effect
conclusion-form decision.** Extraction does not shortcut any of it. For PR #94's
immediate closeout, derive the genuinely-cheap bucket-(a) facts (Main-row pins;
op-bus matches for the ALU families that use them) and treat the branch next-PC as
an **explicitly named residual**, with the cross-row Clean-model capability filed
as the foundational prerequisite that gates ever moving it to derived.

---

## 6. Finding 5 — the audit gate is blind; fix = Option X

`check-construction-theorem-binders.sh` runs `lake exe trust-gate
print-construction-binders` and diffs against
`baseline-construction-theorem-binders.txt`. The subcommand dispatches
(`bin/TrustGate/Main.lean:332-333`) to `cmdPrintGlobalBinders` on
`construction_beq`, which uses `Meta.forallTelescope` over the theorem **type**
and prints one row per top-level Π-binder (`TypeWalk.lean:117-135`). It **never
recurses into a binder's structure fields.** The baseline is just the 4
top-level binders (`trace`, `binding`, `i`, `h_tag`); every smuggled fact lives
*inside* `ProgramBinding → BeqRowBinding (24 fields) → MainRowProvenance (~27
fields)` and is invisible. A maintainer can add any number of bucket-(a) fields
and the diff stays empty. **The gate gives false assurance against exactly the
vector this PR uses.**

**Recommended fix — Option X (recursive field enumeration):** after
`forallTelescope`, for each binder whose type head is a structure, enumerate
`getStructureFields`, telescope function-valued fields (the `beq : ∀ i, … →
BeqRowBinding …` field), recurse with a path prefix + visited set, and emit one
baseline row per leaf field (`path :: fieldName :: ppExpr fieldType`). Mechanics
reuse existing `runMeta`/`forallTelescope`/structure introspection. Changes:
`bin/TrustGate/TypeWalk.lean` (new deep renderer), `bin/TrustGate/Main.lean` (new
subcommand or replace body), regenerate the (~50-line) baseline,
`check-construction-theorem-binders.sh` (point at deep subcommand). Fits the
repo's "snapshot + diff is the audit surface" model exactly.

Option Y (whitelist bucket-(b) shapes, reject bucket-(a) patterns
`multiplicity|.length =|nextPC|rowAt|opBus_row|execRow[`) is stronger (no
regenerate escape hatch) but encodes policy and needs a CODEOWNER-protected
pattern file. Layer Y on later, once all arms exist; X first.

---

## 7. Corrected per-field bucket classification for `BeqRowBinding`

Audit definitions: (a) derivable by the construction from accepted trace data;
(b) genuine named premise (program binding, profile invariants, `aeneasBridgeTrust`,
`NoKnownDefect`); (c) neither — a finding.

| Field | PR #94 status | Honest bucket | Note |
|---|---|---|---|
| `input`, `imm`, `r1`, `r2`, `misaVal` | caller-supplied | (b) program-binding data | Legitimate decode/profile data. |
| `provenance : MainRowProvenance` (~27 eqs) | caller-supplied | **(a)** | Derivable from `trace.constraints` via `rowAt_mainOfTable`; biggest single leak. Verify it actually closes. |
| `h_op,h_external,h_m32,h_set_pc,h_store_pc,h_jmp_offset2` | caller-supplied | **(a)** | Main row pins; derive from constraints/decode. |
| `h_input_imm` | caller-supplied | (b) | Decode-consistency equation. |
| `h_input_r1,h_input_r2,h_input_pc,h_input_misa` | caller-supplied | (b) | Sail state reads — legitimate program/state premises. |
| `h_misa_c` | caller-supplied | (b) | `misa.C = 0` profile invariant — explicitly named in audit. |
| `h_target_aligned` | caller-supplied | (a)/(c)-risk | Branch alignment; derivable in principle, borderline. |
| `execRow` | caller-supplied | **(c) → must be reclassified** | Phantom object; not derivable today (no exec bus). |
| `h_exec_len,h_e0_mult,h_e1_mult` | caller-supplied | **(c)** | Artifacts of `bus_effect` interpreter; carry no real-circuit content. |
| `h_nextPC_matches` | caller-supplied | **(b)-pending-infra** | Cross-row fact; honestly a NAMED premise until the cross-row PC-handshake infra lands. |

**Audit correction required:** `trust/envelope-burden-audit.md` must move the
"Branch exec-row shape" and "PC/nextPC bus bridge" entries out of bucket-(a). The
exec-row shape facts are bucket-(c) artifacts (to be eliminated by re-stating the
conclusion); `nextPC_matches` is a bucket-(b) named premise with a documented
infrastructure prerequisite to return it to (a). This correction is itself an
honest, auditable act — it does not reduce trust, it stops the audit from
*claiming* a derivation that does not exist.

---

## 8. Strategic options for closing out PR #94

The decision among these is the project lead's — it sets P4's scope. Each is
internally honest; they differ in how much infrastructure P4 builds now.

**Option A — Honest named-residual reframe (smallest sound step).**
Rework `construction_beq` to (i) DERIVE the genuinely-derivable bucket-(a) subset
from the trace — the `MainRowProvenance` pins via `rowAt_mainOfTable` +
`trace.constraints` (verify first), and for arithmetic/logic families the op-bus
match via PR2's real Tier-1 template; (ii) expose the irreducible facts
(`nextPC_matches`, and the structural exec artifacts until the conclusion is
restated) as **explicit, named, top-level binders** on `construction_beq` — not
smuggled inside deep records; (iii) correct the audit (§7); (iv) fix the gate
(Option X); (v) write honest STATUS/PROJECTS/self-check. Framing: "P4-PR1 derives
the Main-pin (and op-bus, for ALU families) bucket-(a) subset from the trace; the
branch next-PC remains a named premise with a tracked cross-row prerequisite."
*This reduces real trust (the pins) and stops the laundering, without
overclaiming.*

**Option B — Genuinely derive the branch next-PC by consuming the
already-extracted constraint (revised down from "large prerequisite" by §5a).**
No new infrastructure: bind the named Main accessors to the extracted rows
(`rowAt_mainOfTable`, already written), derive `pc_handshake_at` from
`constraint_18_every_row` via `trace.constraints` (≈`rfl`), wire the
already-proven `branch_eq_compositional`, and discharge the `flag` link through
the modeled op-bus (PR2's machinery + Binary-SM comparison correctness — verify
that lemma exists). The only genuine design decision is the `bus_effect`
conclusion form (§5a step 4): either ground `exec_row` to the real next-row pc
(keeps the conclusion shape) or restate the conclusion off `bus_effect` (the
proper openvm retirement, touching the 63-opcode shared form). With this, the
branch arm is *genuinely constructed from the trace*, not named as residual.

**Option C — Close PR #94 + the PR2 stack; re-plan P4.** Given the laundering is
systemic across 37 bindings and the branch facts need infra, treat the current
stack as the wrong shape: close it, salvage PR2's Tier-1 op-bus derivation
machinery into a fresh P4 plan whose PR1 is the cross-row prerequisite (Option B
work) and whose construction PRs derive rather than relabel.

**Recommendation (FINAL — after §5b verification).** Do not merge PR #94. The
verification (§5b) shows deriving the branch arm is NOT cheap: the cross-row PC
handshake is blocked by the live Clean model's single-row ceiling (a foundational
framework change), and the Binary-EQ aggregation lemma is missing. So the right
immediate move is the honest-residual Option A for branches, deriving only what
is genuinely cheap today:

1. **Derive the cheap bucket-(a) facts from the trace** in the construction:
   Main-row pins via `rowAt_mainOfTable` + `trace.constraints` (single-row —
   verify these close), and the op-bus provider-match for the ALU families that
   use it via PR2's already-real Tier-1 machinery. This is genuine trust
   reduction and removes the corresponding smuggled fields.
2. **Name the branch next-PC as an EXPLICIT top-level residual**, removed from
   the deep `BeqRowBinding`/`MainRowProvenance` smuggling — a visible bucket-(b)
   premise, honestly reported, NOT faked or axiomatized. Its later discharge
   depends on (a) the cross-row Clean-model capability and (b) the Binary-EQ
   aggregation lemma.
3. **Fix the gate (Option X)** and **correct the audit (§7)** — reclassify the
   exec-row artifacts → (c) and PC/nextPC → (b)-pending-infra, citing §5b.
4. **File two tracked endgame prerequisites** (do not bury them): the **cross-row
   component capability** (general — gates every opcode's next-PC and segment
   continuation; this is a foundational model change, candidate for its own
   phase) and the **Binary-EQ 8-byte aggregation lemma + Beq/Bne re-plumb**
   (moderate, templated by `equiv_SLT_of_wf`). The `bus_effect` conclusion-form
   decision rides on the first.

This captures the real, available trust reduction (Main-row pins; ALU op-bus),
eliminates the laundering and the two false assurance signals, tells the truth
about the branch residual, and records — rather than hides — the foundational
cross-row gap that the "extract more?" question productively surfaced.

A pure Option-C reset (close PR #94 + the PR2 stack, re-plan P4 around this
corrected understanding, salvaging PR2's real op-bus machinery) is defensible and
arguably cleaner given the laundering is systemic across 37 bindings. The only
outcome to reject is merging the stack as-is, which bakes a net-zero relabel plus
two false assurance signals (audit + gate) into `main`.

---

## 9. What a bulletproof fix plan must contain (checklist for the next step)

1. **Pre-flight verification (do before writing mechanical recipes):**
   - Confirm the BEQ `MainRowProvenance` pins actually close from
     `trace.constraints` via `rowAt_mainOfTable`/`opBus_row_Main_mainOfTable`
     (lemmas exist, proof unattempted). If they don't close, the "derivable now"
     subset shrinks and the plan must say so.
   - Confirm PR2's Tier-1 op-bus template is reusable as-is for the ALU families
     it covers (it appears so; spot-check one end-to-end).
   - Decide the closeout option (A / B / C) — this is the lead's call and gates
     everything below.
2. **Derive what is derivable**, with the exact lemma chain per fact (pins via
   bridge lemmas; op-bus via Tier-1). No new axioms; cite each lemma.
3. **Name the residual visibly:** `nextPC_matches` (and structural exec facts
   until the conclusion is restated) become explicit top-level binders, removed
   from `BeqRowBinding`/`MainRowProvenance` smuggling. `BeqRowBinding`/
   `ProgramBinding` trimmed to a minimal decode record + genuine (b) premises.
4. **Correct `trust/envelope-burden-audit.md`** per §7 (reclassify exec-row shape
   → (c) artifact; PC/nextPC → (b)-pending-infra) with citations to the cross-row
   gap. Honest, non-trust-reducing, auditable.
5. **Fix the gate (Option X)**: recurse structure fields into the baseline so any
   future smuggling shows in the diff. Regenerate the deep baseline.
6. **Anti-laundering self-check (verbatim in the executor prompt):** the PR must
   show net REMOVALS in the caller-burden / construction-binder diff for the
   facts it claims to derive; any fact that cannot be derived must be a NAMED
   premise + reported, never axiomatized or hidden; no new `Valid_<AIR>`
   constraint or non-reducible `def` may hide a hypothesis.
7. **Honest STATUS/PROJECTS/ENDGAME_ROADMAP update:** P4 reduces the Main-pin
   (and ALU op-bus) trust subset now; the branch next-PC and cross-row continuity
   are a named residual with a scheduled prerequisite. Do not claim trace-level
   construction of the branch arm.
8. **Scope discipline:** if Option A, the cross-row prerequisite (Option B work)
   must be filed as the explicit next P4 item, not deferred silently.

---

## 10. Confidence and open items

- The data-flow findings (dead `trace.constraints`/`balanced`, 37× exec-bus
  field smuggling, blind gate, orphaned `branch_eq_compositional`) are
  **high-confidence** — they are unambiguous from source reading; multiple
  independent investigations agreed. Static analysis only (no `lake build` of a
  proposed fix).
- **To confirm before finalizing the plan:** (a) the BEQ pins actually close
  from `trace.constraints` via the bridge lemmas; (b) the precise binder shape
  the gate's deep renderer will emit (so the baseline is right first time); (c)
  whether any non-branch family's construction *also* needs cross-row facts
  (i.e. whether the residual is branch-only or wider).
- **Decision owed by the lead:** closeout Option A vs B vs C (§8).
