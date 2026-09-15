# PLAN_ENDGAME_P4_SWEEP — sweeping the sound §2 template across the non-blocked families

> **Role:** this is the re-scoped P4 SWEEP plan called for by `PLAN_ENDGAME_P4_SPINE.md`
> §3 / PR4 and tracked by `PLAN_ENDGAME_P4_METAPLAN.md`. The SPINE established the
> infra (`AcceptedTrace`, the salvaged Layer-A op-bus wrappers, the byte-chains,
> the recursive Option-X gate) and proved the honest §2 construction template
> end-to-end on **two** families (SUB + AND). This plan extends that *proven*
> template across the remaining families that are **not** blocked on a foundational
> prerequisite.
> **Status (2026-06-15):** EXECUTED for all buildable families. READY front
> (OR/XOR/SLT/SLTU, the 5 I-types, all 12 shifts) on PR #99; NEEDS-WORK families
> (ADD/ADDI, ADDW/SUBW/ADDIW) on stacked PR #102. **28 of 63 opcodes sound** (23 on
> #99 incl. SUB/AND from SPINE; 5 on #102); all waves adversarially `pass`, 0
> PROJECT axioms. NOT done here: M-extension (separate sub-stream, new extractors);
> families blocked on #76/#100/#101 (loads/stores, branches, JAL/JALR); FENCE
> (defect); LUI/AUIPC (out of scope — reconsider).

> **WHERE THINGS LIVE (read this first — split checkout):** the proven templates,
> the salvage, and the recursive gate are on branch `p4-closeout-construction`
> (PR #99, HEAD `bdd8cca9`), read via the worktree
> `/home/cody/zisk-fv/.worktrees/p4-pr2` (or `git show origin/p4-closeout-construction:<path>`).
> The plan files (`PLAN_ENDGAME_P4_SPINE.md`, `_METAPLAN.md`, this file) live in the
> **main checkout** at `/home/cody/zisk-fv/docs/ai/plan/` and are **local-excluded**
> (`docs/ai` not in git). A future agent reads PLANS from main-checkout paths and
> CODE from the worktree.

---

## 0. TL;DR and goal

**Goal (one line):** extend the proven §2 honest construction template — the one
realised as `construction_sub_sound` + `construction_and_sound` — across every
non-blocked ALU/I-type/W/shift family, producing one `construction_<fam>_sound`
per family with the same shape (data-effect DERIVED from `trace.balanced` /
`trace.constraints`; the control-flow next-PC, decode pins, Sail reads, lane
bridges, and exec artifacts NAMED as explicit top-level residual binders),
appending each to the recursive gate.

**The work is mechanical *only where the four building blocks already exist*.**
The two proven templates are byte-for-byte structurally identical except for five
DELTA points (op pin, Layer-A wrapper + its op-pin shape, byte-chain data-effect
lemma, equiv wrapper, Sail pure spec). For a family where all four blocks exist,
writing its `construction_<fam>_sound` is a ~300-line application of the SPINE §2
template via that DELTA, plus the gate-append. Where a block is **missing** (an
extractor, an aggregation lemma, a derivation lemma) the family is NOT
salvage-ready and is carved out honestly below.

**What this plan delivers** = sound constructions for the in-scope families,
grouped by archetype in build order, each gated. **What it does NOT deliver** =
any family blocked on a foundational prerequisite (branches → #100/#101; loads /
stores → #76; all next-PC discharge → #100), or the M-extension (which needs new
infra — its own sub-stream / NEEDS-WORK, not pure salvage).

**Trust framing (non-negotiable phrasing — SPINE §4.1):** every sound construction
here introduces **0 PROJECT (`ZiskFv.*`) axioms; Sail-translation + Lean-kernel
axioms present as documented external trust**. Never write "0 axioms" unqualified.

**Per-family progress signal (the ONLY mechanical one):** the deep-baseline diff —
appending a family grows `trust/generated/baseline-construction-theorem-binders.txt`
by EXACTLY that family's honest flat top-level binders (17 named residuals +
`execRow`), with the pre-existing SUB/AND blocks byte-identical and ZERO
dotted-path leaf lines. A net-zero diff, or any dotted-record leaf, is laundering,
not progress (SPINE §8; METAPLAN "How to read progress" #4).

---

## 1. Scope

**IN scope (sound constructions to write):**

| Archetype | Opcodes | All four blocks exist? |
|---|---|---|
| 1 — R-type logic | **OR, XOR** | yes (XOR with one confirmed wrinkle, §PR1) |
| 1 — R-type compare | **SLT, SLTU** | yes |
| 2 — I-type logic | **ANDI, ORI, XORI** | yes (XORI inherits XOR's wrinkle) |
| 2 — I-type compare | **SLTI, SLTIU** | yes |
| 1 — R-type ADD / 2 — I-type ADD | **ADD, ADDI** | salvage-rich but provider-AMBIGUOUS (disjunction wrapper) — NEEDS-WORK, §PR4 |
| 3 — W-type | **ADDW, SUBW, ADDIW** | **NO** — missing the m32=1 binary 32-bit lane-binding lemma, §PR5 NEEDS-WORK |
| 4 — shifts | **SLL/SRL/SRA, SLLI/SRLI/SRAI, SLLW/SRLW/SRAW, SLLIW/SRLIW/SRAIW** (12) | yes (separate BinaryExtension template instantiation), §PR6 |

**OUT of scope (blocked — do NOT attempt here; route to their owners):**
- **Branches** (BEQ, BNE, BLT, BGE, BLTU, BGEU) → blocked on **#100** (cross-row
  next-PC) and BEQ/BNE additionally on **#101** (Binary-EQ 8-byte aggregation
  lemma `binary_eq_chunks_eq_bv_eq_of_wf`, absent).
- **Loads / stores** (LD, LBU, LHU, LWU, LB, LH, LW; SD, SB, SH, SW) → blocked on
  **#76** (discharge `memoryTimelineConstructionEvidence`).
- **U/J control flow** (LUI, AUIPC, JAL, JALR + the 2 no-rd-write variants) →
  jump-target next-PC blocked on **#100**.
- **FENCE** → correctness gated by `Defects.NoKnownDefect` (FENCE carve-out).
- **ALL next-PC discharge, every family** → `nextPC_matches` stays a bucket-(b)-
  pending-infra residual binder, blocked on **#100**. The sweep families above are
  in scope only because the *data effect* is derivable; their next-PC residual is
  named, not derived (same as SUB/AND).

**M-extension (13 opcodes)** is carved out as a separate NEEDS-WORK sub-stream, NOT
part of this sweep — see §M. Its salvage is the data-effect side only; the op-bus
construction spine (extractor + `_from_binding` wrapper + `_of_static_row`
intermediate) does **not** exist for arith and must be built first.

---

## 2. Invariants and the per-family recipe (point to the SPINE; do not duplicate)

**Invariants** — obey **SPINE §4 verbatim** (zero new project axioms with the
mandated phrasing §4.1; anti-laundering metric must shrink or hold honestly §4.2;
CRITICAL REPORTING RULE §4.3; manual worktrees + `lake exe cache get` first §4.4;
build/verify gates §4.5; PR protocol §4.6; anti-laundering principle in every
sub-agent prompt §4.7; **ANTI-VACUITY §4.9 — `execRow` MUST stay a genuine
∀-binder; hard-coding `[]` makes `h_exec_len : [].length = 2` contradictory →
vacuous**). The honest three-bucket model and the validated SUB residual budget
are **SPINE §2** — read it before writing any Lean.

**Non-negotiable (SPINE §2 close):** the construction theorem's residuals are
**top-level binders**. No `*RowBinding` / `MainRowProvenance`-style deep record may
carry a bucket-(a) or bucket-(c) fact. The recursive gate enforces this; a human
reviewer confirms the spirit.

**The per-family mechanical recipe** is the distilled DELTA between the two proven
templates. Rather than re-state it, this plan points to the two proven sources and
records only the **corrections** discovered while verifying the inventory against
the worktree at `bdd8cca9`:

- **Template sources to copy:** `ZiskFv/Compliance/ConstructionSub.lean`
  (`construction_sub_sound`, the sub byte-chain route) and
  `ZiskFv/Compliance/ConstructionAnd.lean` (`construction_and_sound`, the logic
  route). They are structurally identical; the op-agnostic infra `busSub`
  (`ConstructionSub.lean:131`) and `mainRowWithRomSub` (`:121`) is reused VERBATIM
  by every R-type construction (do NOT introduce `busAnd`/`busOr`/etc.). The shared
  derivation blocks (op-bus provider match via the Layer-A wrapper; `row_eq` via
  `FullEnsemble.rowAt_mainOfTable` + `mainTableRowAtOrZero_get`; `h_core_store_pc`;
  `h_lane_rd` via `cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero`;
  the six `m*_*` MemBus fields `by rfl`; the lane→Sail binding `h_input_r1_row`/
  `h_input_r2_row` via `input_r1_packed_a_row`/`input_r2_packed_b_row`) are copied
  unchanged.

- **The five DELTA points** (op pin literal D1; Layer-A wrapper + op-pin shape D2;
  byte-chain data-effect lemma D3; equiv wrapper D4; Sail pure spec D5) are
  per-family and are listed in each PR section below from the verified inventory.

### RECIPE DELTA — corrections verified against the worktree (supersede the prompt's RECIPE where they conflict)

These were grep/source-confirmed at `bdd8cca9` and **override** the RECIPE text in
the spawning prompt; the executor must follow these:

1. **OP literal values (verified, `BinaryTable.lean`):** `OP_AND = 0x0E = 14`,
   `OP_OR = 0x0F = 15`, `OP_XOR = 0x10 = 16`, `OP_LT = 0x07 = 7`, `OP_LTU = 0x06 = 6`,
   `OP_ADD = 0x0A = 10`. (The prompt's claim `OP_LT = 10` is wrong; immaterial since
   LT < 16 still holds. The decisive one is **OP_XOR = 16, NOT < 16** — see #2.)

2. **The AND construction body uses the `_op_lt_16` SUB-route lemmas, NOT the
   EquivCore `_logic` lemmas.** `construction_and_sound` (`ConstructionAnd.lean:270,
   275`) derives `h_row_m32`/`h_bop` via
   `logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` (precondition `op_val < 16`,
   discharged `by simp [OP_AND]`) and then `byte_chain_discharge_64_of_static_row`.
   This precondition **HOLDS for OR (15) but FAILS for XOR (16)**. Confirmed: the
   lemma signature at `Bridge/Binary.lean:1559` carries `(h_op_lt : op_val < 16)`.
   Consequence: **OR is a clean line-for-line clone of `construction_and_sound`;
   XOR is NOT** — its construction body must instead use the op=16-capable route
   that `EquivCore/Xor.lean:113-119` uses:
   `ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit row … OP_XOR
   (.inr (.inr rfl)) h_emit` + `byte_chain_discharge_logic_of_static_row` (the
   `_logic` byte-chain, NOT the `_64` one). This is the ONE genuinely non-mechanical
   wrinkle in the logic group and it propagates to XORI.

3. **The final `exact equiv_<FAM>` call does NOT pass `h_row_m32`/`h_bop`.** Verified
   at `ConstructionAnd.lean:295-298`: `equiv_AND` receives
   `state and_input r1 r2 rd m providerTable providerRow i.val bus pins h_component
   h_table_spec h_provider_row h_match h_input_r1_row h_input_r2_row h_lane_rd
   promises`. The wrapper re-unpacks `staticLookupComponent_spec` internally
   (`Wrappers/And.lean:42-53`). The construction body derives `h_row_m32`/`h_bop`/
   `h_out`/`h_matches` **only** to feed the lane→Sail binding step
   (`h_input_r1_row`/`h_input_r2_row` via `input_r1_packed_a_row`). So the prompt's
   RECIPE risk #2 ("SUB passes `h_row_m32 h_bop`; AND does not") resolves cleanly:
   **for a new family, copy AND's call shape** (it is the logic-route shape) and
   ensure the internal `h_matches` derivation uses the op-correct mode-pin/byte-chain
   route (the `_op_lt_16`+`_64` pair for op < 16; the `static_table_logic_mode_pins
   _of_emit`+`_logic` pair for op = 16). **Always read the target
   `Compliance/Wrappers/<Fam>.lean` to confirm its exact argument order before
   wiring the `exact`** — do not assume SUB's or AND's transfers blindly.

4. **equiv wrappers are `lemma`, not `theorem`** (e.g. `Wrappers/Or.lean:132`
   `lemma equiv_OR`). Cosmetic, but the executor will grep for them by the right
   keyword.

---

## 3. The PRs (grouped by archetype, in build order)

Build order follows tractability and shared route: logic (OR/XOR) → compare
(SLT/SLTU) → I-type (ANDI/ORI/XORI then SLTI/SLTIU) → ADD/ADDI (provider
disjunction, NEEDS-WORK) → W-types (NEEDS-WORK, gated on a new lemma) → shifts
(separate template instantiation). One construction per family per commit is
acceptable; group same-archetype families into one PR.

Each PR section gives: opcodes; per-opcode building blocks (verified present);
wrinkles; the gate-append step; a per-PR checklist; gates.

### Shared gate-append step (every PR that adds a `construction_<fam>_sound`)

Per the verified gate protocol (against `bin/TrustGate/Main.lean`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-construction-theorem-binders.sh`):

1. **Append the family to the gate list.** Edit `soundConstructionTheorems` in
   `bin/TrustGate/Main.lean:245-247` (currently `[construction_sub_sound,
   construction_and_sound]`), adding `, \`ZiskFv.Compliance.construction_<fam>_sound`.
   This is the ONLY code edit the gate requires; the
   `print-construction-binders-deep` subcommand is already wired
   (`Main.lean:373-374`).
2. **Rebuild** so the gate exe sees the new olean: `lake build` (after
   `lake exe cache get` if the worktree is fresh).
3. **Regenerate the DEEP baseline:** `trust/scripts/regenerate.sh` (refreshes all
   eight baselines), or run the single load-bearing line directly:
   `lake exe trust-gate print-construction-binders-deep > trust/generated/baseline-construction-theorem-binders.txt`.
4. **Confirm the diff grows by EXACTLY the family's honest flat binders.** Run
   `trust/scripts/check-construction-theorem-binders.sh`. CORRECTNESS CRITERION: the
   diff ADDS exactly one new `# ZiskFv.Compliance.construction_<fam>_sound` block —
   a flat list of the 17 named residuals + `execRow`, with the family-specific
   substitutions (op pin `OP_<FAM>`, input type `PureSpec.<Fam>Input`, nextPC
   against `execute_..._<fam>_pure`); the pre-existing SUB/AND blocks stay
   byte-identical; **ZERO dotted-path leaf lines** (no `…RowBinding.…` /
   `…MainRowProvenance.…`). Reference: each R-type archetype family grows the file
   by ~34 lines (the count observed when AND was added: 34→71).
5. **Run the rest of the gate suite** (`trust/scripts/check-all-semantic.sh` runs
   this check in V2; `nix run .#test` runs V1+V2). Commit the
   `bin/TrustGate/Main.lean` edit + the new `Construction<Fam>.lean` + the
   regenerated baseline (and any other baselines `regenerate.sh` touched) together.

---

### PR1 — R-type logic: OR, XOR (near-mechanical clones of `construction_and_sound`)

**Opcodes:** OR, XOR. Both share the `_logic` Layer-A route. Build OR first
(cleanest), then XOR (one wrinkle).

**Per-opcode building blocks (verified present at `bdd8cca9`):**

- **OR** — Layer-A: `exists_staticBinary_provider_row_matches_logic_from_binding`
  (`AcceptedTrace.lean:74`; serves AND/OR/XOR; op pin is the 3-way disjunction
  `OP_AND ∨ OP_OR ∨ OP_XOR`, OR discharged by `Or.inr (Or.inl _)`). Byte-chain:
  `binary_or_chunks_eq_bv_or_of_wf` (`BinaryPackedCorrect.lean:496`). Equiv wrapper:
  `Compliance.equiv_OR` (`Wrappers/Or.lean:132` — structurally identical to
  `equiv_AND`; delegates to `EquivCore/Or.lean` `equiv_OR_of_static_row`). Sail
  spec: `PureSpec.execute_RTYPE_or_pure` (`SailSpec/or.lean`). Mode-pin/byte-chain
  route in the construction body: **OP_OR = 15 < 16**, so reuse AND's exact body
  route (`logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` discharging
  `by simp [OP_OR]` + `byte_chain_discharge_64_of_static_row`).
  **DELTA from `construction_and_sound`:** `Or.inl h_main_op → Or.inr (Or.inl
  h_main_op)`; `OP_AND → OP_OR` (both `Trusted.OP_OR` in `h_main_op` and
  `BinaryTable.OP_OR` in `h_emit`/mode-pins/byte-chain); `AndInput → OrInput`;
  `equiv_AND → equiv_OR`; `execute_RTYPE_and_pure → execute_RTYPE_or_pure`. **No
  other change.**

- **XOR** — Layer-A: same `_logic_from_binding` (op pin = `OP_XOR` disjunct,
  discharged by `Or.inr (Or.inr h_main_op)`). Byte-chain:
  `binary_xor_chunks_eq_bv_xor_of_wf` (`BinaryPackedCorrect.lean:573`). Equiv
  wrapper: `Compliance.equiv_XOR` (`Wrappers/Xor.lean:30`; delegates
  `EquivCore/Xor.lean` `equiv_XOR_of_static_row`). Sail spec:
  `PureSpec.execute_RTYPE_xor_pure` (`SailSpec/xor.lean`).
  **WRINKLE (verified real, the single non-mechanical step in this PR):**
  `OP_XOR = 0x10 = 16` does **NOT** satisfy the `op_val < 16` precondition of
  `logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` (`Bridge/Binary.lean:1559`).
  So XOR's construction body **cannot** reuse AND's `_op_lt_16`+`_64` mode-pin/
  byte-chain route. Instead mirror `EquivCore/Xor.lean:113-119`:
  - `h_emit` (the `b_op + 16*mode32 = OP_XOR` fact) exactly as AND but with OP_XOR;
  - mode-pins via `ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
    row h_row_spec h_static OP_XOR (.inr (.inr rfl)) h_emit` (3-way selector, no
    `< 16` bound);
  - byte-chain via `byte_chain_discharge_logic_of_static_row` (the `_logic` variant
    at `Bridge/Binary.lean:2376`), NOT `byte_chain_discharge_64_of_static_row`.
  The `h_matches`/lane-binding plumbing downstream is otherwise the AND shape. The
  rest of the DELTA is mechanical (`AndInput → XorInput`, `equiv_AND → equiv_XOR`,
  pure spec swap).

**Per-PR checklist:**
- [ ] worktree off `p4-closeout-construction` (the salvage/template branch); `lake exe cache get` first
- [ ] `ConstructionOr.lean` written via the OR DELTA (clean clone)
- [ ] `ConstructionXor.lean` written via the XOR DELTA + the `static_table_logic_mode_pins_of_emit` / `byte_chain_discharge_logic_of_static_row` route (the verified op=16 wrinkle)
- [ ] `execRow` is a genuine ∀-binder in BOTH (anti-vacuity §4.9); residuals = the 17 named + execRow, no `*RowBinding` leaf
- [ ] gate-append (both families) per §3 shared step; deep baseline grows by exactly two honest blocks; SUB/AND blocks byte-identical; zero dotted leaves
- [ ] anti-laundering self-check in PR body: data effect derived (not caller-supplied); 0 PROJECT (`ZiskFv.*`) axioms / Sail+kernel external; no `Valid_AIR` strengthened; no hidden def
- [ ] PR opened with first body line `Queued for Claude review — do not merge.` then STOP

**Gates:** `lake build` green; `trust/scripts/check-all.sh` (V1); after build
`trust/scripts/check-all-semantic.sh` (V2, includes the deep-binder check);
`nix run .#test` before claiming complete.

---

### PR2 — R-type compare: SLT, SLTU

**Opcodes:** SLT, then SLTU (clone of SLT). The data effect routes through the
c-lane / carry-flag compare chain rather than the flat logic byte rule.

**Per-opcode building blocks (verified present):**

- **SLT** — Layer-A: `exists_staticBinary_provider_row_matches_compare_from_binding`
  (`AcceptedTrace.lean:376`; serves SLT/SLTU; op pin disjunction `OP_LT ∨ OP_LTU`,
  SLT = `Or.inl`). Byte-chain: `binary_lt_chunks_eq_bv_slt_of_wf`
  (`BinaryPackedCorrect.lean:1910`), routed via the compare c-lane/carry chain
  (`compare_c_lanes_LT_of_static_chain` + `chain7_carry_flag_of_static_row_out`).
  Equiv wrapper: `Compliance.equiv_SLT` (`Wrappers/Slt.lean:30`; does INLINE pin
  extraction — `logic_row_mode_pins` for `OP_LT < 16` then
  `equiv_SLT_of_static_row` → `equiv_SLT_of_wf`). Sail:
  `PureSpec.execute_RTYPE_slt_pure` (`SailSpec/slt.lean`). **OP_LT = 7 < 16**, so
  the `_op_lt_16` mode-pin route applies.
  **WRINKLE:** the compare carry-flag / c-lane chain (carry_7 sign-bit, 8-byte SLT
  polarity) replaces the flat logic byte rule; the construction must derive
  `h_row_m32`/`h_bop` via the inline `logic_row_mode_pins` call (as the SLT wrapper
  does) — a minor extra inline prologue versus AND. Otherwise the template
  (`busSub`, row_eq, `h_lane_rd`, MemBus rfl, lane→Sail binding) is reused verbatim.
  DELTA: Layer-A `_compare` (`Or.inl h_main_op`); `OP_LT`; `SltInput`;
  `equiv_SLT`; `execute_RTYPE_slt_pure`.

- **SLTU** — Layer-A: same `_compare_from_binding` (op = `OP_LTU`, `Or.inr`).
  Byte-chain: `binary_ltu_chunks_eq_bv_ult_of_wf` (`BinaryPackedCorrect.lean:1654`).
  Equiv wrapper: `Compliance.equiv_SLTU` (`Wrappers/Sltu.lean:30`; mirrors SLT,
  delegates `equiv_SLTU_of_static_row` → `_of_wf`). Sail:
  `execute_RTYPE_sltu_pure` (`SailSpec/sltu.lean`). **WRINKLE:** unsigned compare
  (`ult`, no sign-bit polarity flip). OP_LTU = 6 < 16. DELTA from SLT:
  `Or.inl → Or.inr`; `OP_LT → OP_LTU`; `SltInput → SltuInput`;
  `equiv_SLT → equiv_SLTU`; pure-spec swap.

**Gate-append + checklist:** as PR1 (per §3), for SLT and SLTU. Confirm the inline
compare-prologue does not introduce a new top-level binder (it must stay derived);
deep baseline grows by exactly two honest blocks.

**Gates:** as PR1.

---

### PR3 — I-type logic + compare: ANDI, ORI, XORI, SLTI, SLTIU

**Opcodes:** ANDI, ORI, XORI (clone the PR1 logic constructions through the I-type
delta), then SLTI, SLTIU (clone the PR2 compare constructions through the same
delta).

**The I-type immediate delta (uniform across all six — verified):** the second
operand is NOT a register read. It is sourced as (1) a structural pin
`itype_imm_subset_holds_main m r_main imm` (`Tactics/ALUITypeArchetype.lean:128`)
asserting Main's `b_0`/`b_1` lanes pack to `BitVec.signExtend 64 imm` — this is a
bucket-(b) program/decode residual (a `ProgramBinding` decode artifact; carried as
a NAMED top-level binder, **never** derived from Main constraints/balance, **never**
hidden in a record — SPINE §8 + CRITICAL REPORTING RULE), and (2) the lane bridge
`h_input_imm_row : BitVec.signExtend 64 input.imm = binaryRowB64 row` (replaces
RTYPE's `h_input_r2_row`). The `ITypePromises` record
(`EquivCore/Promises/IType.lean:40`) carries `input_imm_eq : input_imm = imm` in
place of RTYPE's r2 read. The Layer-A op-bus wrapper is the SAME `_logic` /
`_compare` `_from_binding` (the op-bus match is operand-source-agnostic). So the
construction delta versus the corresponding R-type construction is: **drop the
`h_b_lo_t`/`h_b_hi_t` register lane bridges for r2; ADD a `BitVec 12` imm binder +
the `itype_imm_subset_holds_main` residual binder + `h_input_imm_row`; swap
`RTypePromises → ITypePromises`; route via `equiv_<OP>I`.** Residual budget grows
by ~1 (the imm pin) versus the R-type sibling. This delta is identical across all
six (proven by `itype_imm_subset_holds_main` being opcode-agnostic + every I-type
wrapper using the same `BitVec.signExtend 64 imm` packing), so once ONE I-type
construction is written the other five are pure literal swaps.

**Per-opcode building blocks (verified present):**

- **ANDI** — Layer-A `_logic_from_binding` (`OP_AND`, `Or.inl`); byte-chain
  `binary_and_chunks_eq_bv_and_of_wf` (`BinaryPackedCorrect.lean:419`, same chain
  AND uses); equiv `Compliance.equiv_ANDI` (`Wrappers/Andi.lean:90` — `= equiv_AND`
  + `imm : BitVec 12` + `h_input_imm_row` + `h_andi_subset`
  (`itype_imm_subset_holds_main`) + `ITypePromises`; delegates `EquivCore/Andi.lean`);
  Sail `execute_ITYPE_andi_pure` (`SailSpec/andi.lean`). OP_AND = 14 < 16 →
  `_op_lt_16` route. **Write this one first** (it is the AND construction + the
  uniform I-type delta; `Andi.lean`'s doc states the pattern transfers verbatim to
  ORI/XORI).
- **ORI** — `_logic_from_binding` (`OP_OR`, `Or.inr (Or.inl _)`); byte-chain
  `binary_or_chunks_eq_bv_or_of_wf`; equiv `Compliance.equiv_ORI`
  (`Wrappers/Ori.lean:32`, `EquivCore/Ori.lean`); Sail `execute_ITYPE_ori_pure`
  (`SailSpec/ori.lean`). OP_OR = 15 < 16 → `_op_lt_16` route. Clone of ANDI +
  literal swaps.
- **XORI** — `_logic_from_binding` (`OP_XOR`, `Or.inr (Or.inr _)`); byte-chain
  `binary_xor_chunks_eq_bv_xor_of_wf`; equiv `Compliance.equiv_XORI`
  (`Wrappers/Xori.lean:32`, `EquivCore/Xori.lean`); Sail `execute_ITYPE_xori_pure`
  (`SailSpec/xori.lean`). **WRINKLE: inherits XOR's OP_XOR = 16 ≥ 16 wrinkle** — its
  construction body must use the `static_table_logic_mode_pins_of_emit` +
  `byte_chain_discharge_logic_of_static_row` route, NOT `_op_lt_16`+`_64` (see PR1
  XOR). So XORI = (XOR construction body route) + (I-type delta).
- **SLTI** — `_compare_from_binding` (`OP_LT`, `Or.inl`); byte-chain
  `binary_lt_chunks_eq_bv_slt_of_wf`; equiv `Compliance.equiv_SLTI`
  (`Wrappers/Slti.lean`, `EquivCore/Slti.lean`); Sail `execute_ITYPE_slti_pure`
  (`SailSpec/slti.lean`). WRINKLE: SLT compare chain + immediate routing combined.
  = (SLT construction) + (I-type delta).
- **SLTIU** — `_compare_from_binding` (`OP_LTU`, `Or.inr`); byte-chain
  `binary_ltu_chunks_eq_bv_ult_of_wf`; equiv `Compliance.equiv_SLTIU`
  (`Wrappers/Sltiu.lean`, `EquivCore/Sltiu.lean`); Sail `execute_ITYPE_sltiu_pure`
  (`SailSpec/sltiu.lean`). WRINKLE: SLTIU sign-extends the 12-bit imm to 64 then
  does an UNSIGNED compare (RISC-V quirk); the `h_input_imm_row` uses
  `BitVec.signExtend 64 imm` uniformly, so imm packing is unchanged; the
  unsigned-compare data effect is the `binary_ltu` chain. = (SLTU construction) +
  (I-type delta).

**Per-PR checklist (beyond §3 shared gate-append):**
- [x] ANDI written first (AND construction + I-type delta); ORI/SLTI/SLTIU follow as literal swaps; XORI uses the XOR op=16 body route — all in `ConstructionIType.lean`
- [x] `itype_imm_subset_holds_main` is a NAMED top-level binder in EVERY I-type construction — NOT derived, NOT in a record; deep baseline shows `h_<op>_subset :: ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main …` as a flat binder line in all 5
- [x] `execRow` ∀-binder present; per-family residual = 16 hyp binders + `imm` + execRow (the immediate-decode equality `h_input_imm : input.imm = imm` joins the budget; `h_input_imm_row` 8-byte form is DERIVED in-body for all five, not a binder). Deep leaves: 33/family vs 34 R-type, net -1 (honest -4 r2/lanes, +3 imm pins)
- [x] gate-appended all five to `soundConstructionTheorems`; deep baseline grew +175 lines = 5 honest blocks; SUB/AND/OR/XOR/SLT/SLTU blocks byte-identical (verified prior-prefix bytes equal)
- [x] anti-laundering self-check; 0 PROJECT (`ZiskFv.*`) axioms per new theorem / Sail+kernel external; baseline diff purely additive (175 add / 0 remove)
- [ ] PR already open (#99); pushed Wave 2 commit to update it; do-not-merge held

**Gates:** as PR1.

---

### PR4 — ADD, ADDI (provider disjunction — NEEDS-WORK, not a clone)

**Opcodes:** ADD then ADDI. **These are NOT clones of SUB/AND.** Honest status:
**salvage-rich but the ambiguity resolution is unwritten — there is no
`construction_add_sound` and writing one requires a genuine design decision.**

**The characterized ambiguity (verified):** `OP_ADD = 0x0A = 10` may be served by
EITHER the lookup-aware Binary provider (`staticLookupComponent`) OR the
`BinaryAdd` provider (`BinaryAdd.component`) — two distinct AIRs with two distinct
`opBusMessage` shapes. The salvaged Layer-A wrapper
`exists_add_provider_row_matches_from_binding` (`AcceptedTrace.lean:252`) RESOLVES
this by deriving from `trace.balanced` both `add_subset_holds` AND a DISJUNCTION
`(staticLookup provider match) ∨ (BinaryAdd provider match)`. This is a **different
obtain shape** than SUB/AND (which get a single unambiguous provider), so the
construction body cannot reuse the SUB/AND provider-match block verbatim.

**Building blocks that EXIST (both arms):**
- Equiv wrappers BOTH present: `Compliance.equiv_ADD` (`Wrappers/Add.lean:43`,
  lookup arm, OP_ADD pin, mode32 = 0, delegates `equiv_ADD_of_static_row`, uses
  `logic_row_mode_pins` with op literal 10 < 16) and
  `equiv_ADD_via_binaryadd` (`Wrappers/Add.lean:110`, BinaryAdd arm, needs
  `add_subset_holds` + lane bridges `h_a_lo_t`/`h_a_hi_t`).
- Data-effect: lookup arm `binary_add_chunks_eq_bv_add_of_wf`
  (`BinaryPackedCorrect.lean:1528`); BinaryAdd arm
  `binary_add_chunks_eq_bv_add_via_component` (`AirsClean/BinaryAdd/Bridge.lean:145`).
- Sail: `execute_RTYPE_add_pure` (`SailSpec/add.lean`).
- ADDI: equiv wrappers BOTH present — `Compliance.equiv_ADDI`
  (`Wrappers/Addi.lean:36`, lookup arm) + `equiv_ADDI_via_binaryadd`
  (`Wrappers/Addi.lean:107`, BinaryAdd arm) — each = the ADD arm + the PR3 I-type
  immediate delta; the SAME `exists_add_provider_row_matches_from_binding`
  disjunction serves ADDI's op-bus. Same `binary_add` chains. Sail
  `execute_ITYPE_addi_pure` (`SailSpec/addi.lean`).

**The unwritten design decision (the reviewer/executor must choose, then report):**
- **(a) Case-split the disjunction and prove BOTH arms** — discharge the lookup arm
  via `equiv_ADD` and the BinaryAdd arm via `equiv_ADD_via_binaryadd`, concluding
  the same goal in each branch. Honest and complete but is genuinely new reasoning
  (a two-arm construction with branch-specific provider plumbing). OR
- **(b) Pick one provider arm and name the other-arm-exclusion as an explicit
  residual binder.** Honest but weaker (carries an exclusion premise); must be a
  named top-level binder, not hidden.

**METAPLAN guard (do not miscount):** the `via_binaryadd` ADD/ADDI OpEnvelope arms
that already exist on PR #99 are a KEPT op-bus ROUTE, **NOT** a
`construction_*_sound`. They do not count as a sound ADD construction.

**Per-PR checklist:**
- [ ] **DECISION RECORDED FIRST** (in the PR body / a doc note): approach (a) two-arm or (b) one-arm-plus-exclusion-residual — this is a reviewer-facing design call per SPINE §4.3
- [ ] `construction_add_sound` written under the chosen approach; if (b), the exclusion is a NAMED top-level binder
- [ ] `construction_addi_sound` = ADD construction + PR3 I-type delta (`itype_imm_subset_holds_main` named; `ITypePromises`)
- [ ] both arms' data effect DERIVED (not caller-supplied); `execRow` ∀-binder
- [ ] gate-append; deep baseline grows by the honest binders of each — NOTE the budget MAY differ from the R-type archetype (extra `add_subset_holds` and/or the exclusion residual); the reviewer confirms the new block is flat (no dotted leaf) and matches the chosen approach
- [ ] anti-laundering self-check; 0 PROJECT (`ZiskFv.*`) axioms / Sail+kernel external
- [ ] PR opened `do not merge`, STOP

**Gates:** as PR1. **If the disjunction case-split does not close on compile, STOP
and report (CRITICAL REPORTING RULE) — do not relabel or pick an arm silently.**

---

### PR5 — W-types: ADDW, SUBW, ADDIW (NEEDS-WORK — blocked on a new lane lemma)

**Honest status: NOT salvage-ready as drop-in clones. A prerequisite derivation
lemma is MISSING and must be authored first.** Three of the four blocks exist; the
fourth — the m32=1 32-bit lane→Sail binding lemma — does not.

**The principal trap (verified — the one real gap):** there is NO Binary-bridge
lemma deriving the W-type 32-bit operand binding
`(Sail.BitVec.extractLsb r1_val 31 0).toNat = binaryRowA32 row % 2^32` from main
lanes + match in the **m32 = 1** case. Confirmed: `binaryRowA32`/`binaryRowB32`/
`input_r1_packed_a32` do **not** appear anywhere in `EquivCore/Bridge/Binary.lean`
(grep count 0). The only binary lane-binding lemma, `input_r1_packed_a_row`
(`Bridge/Binary.lean:2817`), HARD-REQUIRES `h_m32 : m.m32 r_main = 0` and uses
`one_sub_zero_mul` — exactly CLAUDE.md trap #3 (`(1-0)*x` does not reduce over
`Fin p`), sidestepped only for m32 = 0. Consequence: the W-type equiv wrappers take
the binding as INPUT binders — confirmed `Wrappers/Addw.lean:52-58` requires
`h_input_r1_extract`/`h_input_r2_extract`
(`(Sail.BitVec.extractLsb addw_input.r1_val 31 0).toNat = …`). A sound W
construction must FIRST author a new lemma `input_r1_packed_a32_row` (the binary
analog of the shift bridge's `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range`,
`Bridge/BinaryExtension.lean:402`), discharging the m32 = 1 high-lane term `(1-1)*a_hi`
the way the shift bridge does (via the op-bus selector + `ring`, NOT simp/decide).
**This is genuinely new reasoning, not salvage. Until it exists, "salvage exists"
is FALSE for W-types**; they can only be assembled by carrying
`h_input_r{1,2}_extract` as residual binders (honest, but enlarges the residual
budget versus SUB — flag this if the new lemma is deferred).

**Building blocks that DO exist:**
- Layer-A: `exists_staticBinary_provider_row_matches_w_from_binding`
  (`AcceptedTrace.lean:465`; op pin disjunction `OP_ADD_W ∨ OP_SUB_W`, single
  `staticBinary` provider). **WRINKLE: m32 = 1 not 0** — the SUB §2 `h_m32 := 0`
  specialization does NOT transfer; conclusion carries the `writeReg nextPC`
  prelude (like SUB); 32-bit operands via `extractLsb _ 31 0` + a 32-bit
  sign-extend of the result.
- ADDW: equiv `Compliance.equiv_ADDW` (`Wrappers/Addw.lean:32` →
  `EquivCore/Addw.lean`); Sail `execute_RTYPE_addw_pure` (`SailSpec/addw.lean`);
  byte-chain `binary_addw_chunks_eq_bv_add_w_of_wf` (`BinaryPackedCorrect.lean:2098`)
  + signExtend finishers. Emits `OP_ADD_W` (shared with ADDIW).
- SUBW: equiv `Compliance.equiv_SUBW` (`Wrappers/Subw.lean` →
  `EquivCore/Subw.lean`); Sail `execute_RTYPE_subw_pure` (`SailSpec/subw.lean`);
  byte-chain `binary_subw_chunks_eq_bv_sub_w_of_wf` (`BinaryPackedCorrect.lean:2290`)
  + signExtend finishers. Emits `OP_SUB_W` (UNIQUE to SUBW — no ADD/sail-form
  ambiguity).
- ADDIW (HARDEST): equiv `Compliance.equiv_ADDIW` (`Wrappers/Addiw.lean:36` →
  `EquivCore/Addiw.lean`); Sail `execute_ITYPE_addiw_pure` (`SailSpec/addiw.lean`);
  reuses ADDW signExtend finishers. ITYPE → needs `ITypePromises` +
  `itype_imm_subset_holds_main` + an immediate-byte-decomposition `h_input_imm_extract`
  (derived in-wrapper `Wrappers/Addiw.lean:150-169` from `h_addiw_subset` + `b_lo`
  of `h_match`). Shares `OP_ADD_W` with ADDW → bus-INDISTINGUISHABLE from ADDW,
  discriminated only by Sail instruction form (RTYPEW vs ADDIW), supplied as a
  construction residual binder.

**Build order within PR5:** prerequisite lemma `input_r1_packed_a32_row` (+ r2
mirror) FIRST. Then **SUBW** (unique `OP_SUB_W`, no ambiguity). Then **ADDW**
(mechanical `OP_SUB_W → OP_ADD_W`, `0x1B → 0x1A` diff of SUBW once the lemma
exists). Then **ADDIW** (ITYPE + immediate-byte decomposition on top of ADDW).

**Cross-cutting W wrinkles to confirm before claiming the budget:** the
ADDW/ADDIW Sail-form discriminator residual must pin the form (reviewer confirms
it is not vacuously satisfiable, SPINE §4.9); ADDIW's `h_addiw_subset` dependency
of the imm decomposition must be sourced as a residual or derived from Main Spec —
verify which.

**Per-PR checklist (DONE — Sweep Wave 6, on `p4-sweep-needswork` / PR #102):**
- [x] **`input_r1_packed_a32_row` (+ r2 mirror) AUTHORED** in `EquivCore/Bridge/Binary.lean` and GENUINELY PROVEN (0 PROJECT axioms; closure `[propext, Classical.choice, Quot.sound]`; no sorry/axiom). FINDING that supersedes the trap framing: the m32 = 1 high-lane `(1-1)*a_hi` term does NOT need to be discharged at all for the 32-bit operand binding — for the staticBinary provider the `a_lo` conjunct of `matches_entry` is m32-independent, so `(extractLsb r1_val 31 0).toNat = binaryRowA32 row % 2^32` derives from the low-4-byte `a_lo` equation alone (`m.a_0 = packed low 4 a-bytes`, each `< 256` ⇒ sum `< 2^32` ⇒ the `a_1 * 2^32` high summand drops under `% 2^32`). No `one_sub_one_mul`/`ring` on the high lane is consumed. The lemmas take 4 explicit a/b byte-range (`< 256`) hyps, sourced in-construction from `h_facts` (`StaticBinaryTableWfFacts`).
- [x] W bus harness: m32 = 1 (NOT the §2 m32 := 0 specialization); writeReg-nextPC prelude retained (the W-ALU wrappers carry it, unlike the bare-execute W-shifts).
- [x] SUBW → ADDW → ADDIW written in `ConstructionWAlu.lean`; ADDIW carries the I-type imm delta (`imm : BitVec 12` + `h_input_imm` + the NAMED `h_addiw_subset : itype_imm_subset_holds_main` pin + `ITypePromises`). The `equiv_ADDIW` wrapper derives the immediate byte decomposition internally from `h_addiw_subset` + `b_lo` of `h_match`, so the construction supplies only the r1 lane extract. ADDW/ADDIW share `OP_ADD_W` (Sail form discriminated by `instruction.RTYPEW` vs `instruction.ADDIW` in the goal conclusion, a genuine binder, not vacuous).
- [x] `execRow` ∀-binder genuine in all three; residual budgets honest and EQUAL to the SUB R-type archetype (no enlargement — the lane lemma was NOT deferred): SUBW 34, ADDW 34, ADDIW 33 deep binders.
- [x] gate-append (all three to `soundConstructionTheorems`, 25 → 28); deep baseline grew by exactly 3 honest flat blocks (no dotted leaf); prior 25 blocks byte-identical (old file is a byte-exact prefix of the new file).
- [x] anti-laundering self-check; 0 PROJECT (`ZiskFv.*`) axioms per new theorem (`[cancel_reservation, propext, Classical.choice, Quot.sound]` = Sail+kernel external); the new lane lemmas add 0 axioms (`baseline-axioms.txt` UNCHANGED).
- [x] lake build green (8688 jobs); check-all.sh 18/18; check-all-semantic.sh 12/12. Committed + pushed to PR #102 (do-not-merge held).

**Gates:** as PR1. (Trap note: the m32 = 1 high-lane term did NOT need reduction —
the low-half binding is m32-independent. No simp/decide papered over anything.)

---

### PR6 — Shifts: SLL/SRL/SRA, SLLI/SRLI/SRAI, SLLW/SRLW/SRAW, SLLIW/SRLIW/SRAIW (12)

**Honest status: all 12 are salvage-READY (all four blocks + the lane-binding
derivation exist), but this is a SEPARATE TEMPLATE INSTANTIATION, not the
`busSub`/`staticLookupComponent` path** — the provider is the BinaryExtension
`shiftStaticLookupComponent` with a different `opBusMessage` and a different
byte-chain. So PR6 clones the SHAPE of the §2 template but against the
BinaryExtension route.

**Shared route (verified) for all 12:** Layer-A
`exists_binaryExtension_provider_row_matches_shift_from_binding`
(`AcceptedTrace.lean:554`; op pin = 6-way disjunction
`OP_SLL/SRL/SRA/SLL_W/SRL_W/SRA_W`); serves ALL 12. **WRINKLES (route-level):**
(i) the BinaryExtension provider uses `op_is_shift` as the op-bus selector; the
lane-binding bridge differs by m32 sub-group — the **m32=0** shifts (SLL/SRL/SRA +
their I-forms) route through `packed_a_eq_of_shift_match_m32_0_of_a_range`
(`Bridge/BinaryExtension.lean:240`), which DOES use `simp only [one_sub_zero_mul]`
(line 269); the **m32=1** W-shifts route through
`packed_a_lo32_eq_of_shift_match_m32_1_of_a_range` (`:402`), which closes the lane
term by `ring` (line 429). Do NOT tell the executor to avoid `one_sub_zero_mul`
universally — it is the correct route for the m32=0 group; (ii) the conclusion is
the BARE `execute_instruction (...) = (bus_effect ...).2` with **NO** `writeReg
nextPC` prelude (differs from SUB/AND/W) → the construction goal shape must drop
the prelude, and the exec-bus bookkeeping (`h_exec_len`/`h_e0_mult`/`h_e1_mult`/
`busSub`-style bus / `h_nextPC_matches`) must be re-derived against the bare-execute
form (a parallel harness, low risk but not a literal copy of the SUB harness).

**Sub-group building blocks (verified present):**

- **SLL/SRL/SRA (R non-W, m32 = 0, shift-amount `% 64`, rowA64):** equiv
  `Compliance.equiv_{SLL,SRL,SRA}` (`Wrappers/Sll.lean:77`, `Srl.lean`, `Sra.lean`
  → `EquivCore/{Sll,Srl,Sra}.lean`); Sail `execute_RTYPE_{sll,srl,sra}_pure`
  (`SailSpec/{sll,srl,sra}.lean`); byte-chains
  `binary_extension_{sll,srl,sra}_chunks_eq_bv_{shl,ushr,sshr}_of_wf`
  (`BinaryExtensionPackedCorrect.lean:830/1035/2010`); lane binding
  `packed_a_eq_of_shift_match_m32_0_of_a_range` (rowA64,
  `Bridge/BinaryExtension.lean:240`) + shift-pin
  `shift_pin_eq_of_shift_match_m32_0_of_b0_range` (rowShiftAmount `% 64`, `:299`).
  WRINKLE: shift-amount masked `% 64`; pins OP_SLL/SRL/SRA (m32 = 0). **Build these
  three first** (closest to SUB modulo the bare-execute goal + the `op_is_shift`
  lane route).
- **SLLI/SRLI/SRAI (immediate non-W):** equiv `Compliance.equiv_{SLLI,SRLI,SRAI}`
  (`Wrappers/Slli.lean:34`, `Srli.lean`, `Srai.lean` → `EquivCore/{Slli,Srli,Srai}.lean`);
  Sail `execute_SHIFTIOP_{slli,srli,srai}_pure`; reuse the sll/srl/sra chunk
  lemmas; lane binding `packed_a_eq_of_shift_match_m32_0_of_a_range` (rowA64) +
  immediate shift-pin `shift_pin_immediate_eq_of_shift_match_of_b0_range`
  (`Bridge/BinaryExtension.lean:349`). WRINKLE: SHIFTIOP (`shamt : BitVec 6`, no
  `% 64` mask since already 6-bit); `ShiftImmPromises`; shares OP_SLL/SRL/SRA with
  the register variants (bus-indistinguishable, discriminated by Sail form). Clone
  of the prior sub-group: swap RTYPE → SHIFTIOP + the register shift-pin for the
  immediate one.
- **SLLW/SRLW/SRAW (W register, m32 = 1, `% 32`, rowA32):** equiv
  `Compliance.equiv_{SLLW,SRLW,SRAW}` (`Wrappers/Shift.lean:26`, `ShiftR.lean:26`,
  `ShiftRA.lean:26` → `EquivCore/{Sllw,Srlw,Sraw}.lean`); Sail
  `execute_RTYPE_{sllw,srlw,sraw}_pure` (`SailSpec/{sllw,srlw,sraw}.lean`, 32-bit
  signExtend); byte-chains `binary_extension_{sllw,srlw,sraw}_chunks_eq_bv_{shl_w,
  ushr_w,sshr_w}_of_wf` (`BinaryExtensionPackedCorrect.lean:3508/2839/4123`); lane
  binding `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range` (32-bit
  `extractLsb = rowA32`, `Bridge/BinaryExtension.lean:402`) + shift-pin
  `shift_pin_w_eq_of_shift_match_of_b0_range` (rowShiftAmount32 `% 32`, `:452`).
  WRINKLE: m32 = 1; 32-bit operand extract; `% 32`; pins OP_SLL_W/SRL_W/SRA_W.
  **NOTE: the m32 = 1 lane-binding lemma that the binary W-types LACK, the shifts
  HAVE** — so W-shifts are READY where binary W-types are NEEDS-WORK.
- **SLLIW/SRLIW/SRAIW (W immediate):** equiv `Compliance.equiv_{SLLIW,SRLIW,SRAIW}`
  (`Wrappers/ShiftLI.lean:27`, `ShiftRLI.lean:27`, `ShiftRAI.lean:27` →
  `EquivCore/{Slliw,Srliw,Sraiw}.lean`); Sail `execute_SHIFTIWOP` family
  (`SailSpec/{slliw,srliw,sraiw}.lean`); reuse W chunk lemmas; lane binding
  `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range` + immediate W shift-pin
  `shift_pin_w_immediate_eq_of_shift_match_of_b0_range`
  (`Bridge/BinaryExtension.lean:503`). WRINKLE: SHIFTIWOP immediate + m32 = 1 +
  32-bit extract; shares OP_SLL_W/SRL_W/SRA_W with the W-register variants. Clone of
  the W-register sub-group + the W-immediate shift-pin.

**Build order within PR6 (each later sub-group is a near-mechanical diff of the
prior; all 12 share ONE Layer-A wrapper + ONE Layer-B theorem, so the provider-match
block is copy-paste across all 12):** SLL/SRL/SRA → SLLI/SRLI/SRAI → SLLW/SRLW/SRAW
→ SLLIW/SRLIW/SRAIW.

**Per-PR checklist (PR6a — m32 = 0 group SLL/SRL/SRA + SLLI/SRLI/SRAI — DONE Sweep Wave 3):**
- [x] bare-execute conclusion confirmed: the m32 = 0 shift wrappers (`equiv_SLL` etc.) ALREADY have the bare `execute_instruction (…) = (bus_effect …).2` conclusion (no writeReg prelude), so the construction concludes it verbatim; no parallel harness was needed — the exec-bus bookkeeping rides inside `RTypePromises`/`ShiftImmPromises`. `execRow` stays a ∀-binder under the bare goal (anti-vacuity §4.9)
- [x] the 6 m32 = 0 constructions written via the BinaryExtension template; lane terms closed via `packed_a_eq_of_shift_match_m32_0_of_a_range` (`one_sub_zero_mul`, `:240/269`); shift-pin via `shift_pin_eq_of_shift_match_m32_0_of_b0_range` (register) / `shift_pin_immediate_eq_of_shift_match_of_b0_range` (immediate). Wrinkle discovered: an inline `set row := …rowInput…` + final `exact equiv_<OP>` TIMED OUT at `whnf` — solved by factoring the lane/op-is-shift derivations into five opaque-`row` helper theorems (`shift_op_pin_eq_of_match`, `shift_op_is_shift_of_facts`, `shift_m32_0_input_r1_row_of_facts`, `shift_m32_0_shift_pin_row_of_facts`, `shift_imm_shift_pin_row_of_facts`) so `simp` never unfolds the giant provider term
- [x] register-vs-immediate Sail-form discriminator: register variants take r2 read + b-lane bridges → `RTypePromises`; immediate variants take `shamt : BitVec 6` + `h_input_shamt` + the `b_0 = shamt_b_lo shamt` decode pin → `ShiftImmPromises`. Residuals non-vacuous (execRow ∀-binder; bus from real trace row)
- [x] gate-append (6 m32 = 0 families); deep baseline grew 11 → 17 blocks (+201 lines, 6 honest flat blocks, no dotted leaf); SUB/AND/OR/XOR/SLT/SLTU/ANDI/ORI/XORI/SLTI/SLTIU blocks byte-identical
- [x] anti-laundering self-check; 0 PROJECT (`ZiskFv.*`) axioms / Sail+kernel external (closure = `[cancel_reservation, propext, Classical.choice, Quot.sound]`)
- [x] PR #99 already open (`do not merge`); pushed Wave 3 commit to update it

**Per-PR checklist (PR6b — m32 = 1 W-shifts SLLW/SRLW/SRAW + SLLIW/SRLIW/SRAIW — NOT this wave):**
- [ ] m32 = 1 lane route via `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range` (`ring`, `:402/429`); shift-pin via the `% 32` W variants; 32-bit `extractLsb` operand
- [ ] gate-append (6 W families); same gate

**Gates:** as PR1. (PR6 split into PR6a non-W (6 ops, DONE Wave 3) + PR6b W (6 ops,
pending) per the suggested chunking — same gate per chunk.)

---

## M. M-extension — carved out honestly (separate NEEDS-WORK sub-stream, NOT salvage)

**This is NOT part of the sweep.** None of the 13 M-ext opcodes is a near-mechanical
clone of SUB/AND. The sweep (Archetypes 1-4) reuses three salvaged things that ALL
exist for binary/shift but are ALL **MISSING** for arith. This sub-stream must
build that spine as new infra before any "pure template application" is possible.
File it as `PLAN_ENDGAME_P4_ARITH.md` (or an M-ext sub-section of the metaplan); do
NOT attempt it inside the sweep PRs.

**Global gaps verified MISSING at `bdd8cca9` (grep-confirmed empty):**
1. **Layer-A op-bus CONSTRUCTION wrapper for arith** — no `arithMul…_from_binding`
   / `arithDiv…_from_binding` in `AcceptedTrace.lean` (the 5 salvaged wrappers
   cover only `staticBinary` + `binaryExtension`). What exists is only
   branch-EXCLUSION support (`arithMul_provider_branch_ne_*` — proving arithMul is
   NOT the provider when op is binary); the POSITIVE provider-match direction is
   unassembled. **Do not mistake exclusion lemmas for a provider-match derivation.**
2. **`arithMulOfTable` / `arithDivOfTable` extractors** — MISSING (empty in
   `ZiskFv/`, `bin/`, `tools/`).
3. **`_of_static_row` intermediate** — MISSING for every M-ext opcode (the binary
   route's intermediate, present for Archetypes 1-4).
4. **Witness-from-balance derivations** — the lookup-range witnesses the
   construction must DERIVE (`Chunk/Carry/RemainderBound`) are caller-supplied
   `ConstraintsHold.Soundness` structures with NO `_of_balance`/`_of_trace`/`_of_lookup`
   derivation. This is the central missing infra (the arith analog of
   `staticBinary_core_and_wf_of_table_spec`); building it is genuinely new reasoning.
5. **`arithDiv_table_interactionsWith_opBus_nil`** (`Balance.lean:280`) — ArithDiv
   pushes NIL to OpBus in the full ensemble; div/rem op-bus is bridged by dedicated
   primary/secondary ArithDiv.Bridge messages "outside the full ensemble". So div/rem
   construction needs a **genuinely-new op-bus finder**, not a wrapper around the
   existing one — the single biggest M-ext risk. **Open question to resolve first:**
   whether the live `trace.balanced` even represents div/rem op-bus pushes; if not,
   div/rem may be partially BLOCKED on missing ensemble plumbing, not just unwritten
   proof.

**What DOES exist (the data-effect / salvage side is substantial):** all 13
`equiv_<OP>` canonical wrappers (`Equivalence/{Mul,…,Remuw}.lean`) + EquivCore
proofs, no sorries; the data-effect packed/chunk/carry CORRECTNESS lemmas
(`arith_mul_unsigned_packed_correct`, `arith_div_unsigned_packed_correct`, the
carry identities, the `*_chain_witnesses_of_carry_ranges` derivations, the
remainder-bound lemmas, and their W + signed variants); the op-bus message defs +
eval + rowAt-equality lemmas; and the branch-exclusion support. **But "salvage
exists" for the op-bus CONSTRUCTION direction is FALSE** — the four blocks the
sweep relies on (extractor, `_from_binding` wrapper, `_of_static_row`, witness
derivation) are absent.

**Sub-stream build order (none is mechanical):**
1. **INFRA FIRST:** `arithMulOfTable` + `arithDivOfTable` extractors; the converse
   branch-narrowing wrapper (exclude binary/shift/binaryAdd branches when op IS
   arith — mirror of the existing `arithMul_provider_branch_ne_*` exclusion lemmas);
   and the witness-from-balance derivations (Chunk/Carry/RemainderBound from
   trace lookup-channel satisfaction — the genuinely-new reasoning).
2. **MULW first** (the arith exemplar — its data-effect chain
   `mul_w_chain_witnesses` is built, and the live finder disjunction in
   `Balance.lean` (~`:490`/`:572`) carries an `arithMulProviderComponent` arm).
   CAVEAT: that arm only means arithMul *appears* as a disjunction branch — there
   is NO positive `arithMul…_from_binding` provider-match wrapper assembled (gap #1
   above); "serves" ≠ "has a usable wrapper". Treat it as "the SUB of arith" only
   after that wrapper + the `arithMulOfTable` extractor exist. WRINKLE: m32 = 1 (no §2 m32 := 0 specialization; the `(1-0)*x` trap does
   NOT apply) + W sign-extension on bytes 4..7 via `h_sext_choice`.
3. **MULHU** (same provider, but needs NEW secondary-entry finder coverage — the
   disjunction is primary-only; high-64 output via d-chunks). Then **DIVU/REMU**
   (genuinely-new div/rem op-bus finder per gap #5; remainder-bound + witness
   derivations; DIV/REM share a row → two op-bus entries). Then **DIVUW/REMUW** (add
   the W wrinkle once DIVU lands).
4. **Signed (MUL, MULH, MULHSU, DIV, DIVW, REM, REMW) LAST and only for
   constructible bucket-(a) fields:** their correctness field is **defect-BLOCKED**.
   `Defects.MaliciousSignedMulWitnessShape` (`Defects.lean:53`) returns True for
   `.mul/.mulh/.mulhsu` → `NoKnownDefect` (`Defects.lean:89`) EXCLUDES them; the
   comment records this as a real ZisK circuit defect ("false static product-sign
   shortcut"). **The signed-product correctness field is NOT constructible without
   an upstream circuit fix** — a CRITICAL-REPORTING finding, not fakeable; construct
   only bucket-(a) and name the defect. `Defects.ArithDivDynamicWitnessShape`
   (`Defects.lean:68`) returns True for `.div/.divw/.rem/.remw` → excluded "until
   their extra sign and overflow/div-by-zero facts are proved" — dischargeable in
   principle once those facts are proved (then retire the defect), but still blocked
   on all the unsigned-path op-bus-finder + extractor + witness gaps above.

**M-ext anti-laundering flags (must hold):** never forward the lookup-range
witnesses as new top-level binders to "make it compile" — that just renames the
promise; they must be DERIVED from `trace.balanced` / lookup-channel satisfaction
(SPINE §8 #3). Never introduce a `ZiskFv.*` axiom to stand in for the missing
witness derivation (axiom inflation, SPINE §8 #1). Phrase trust as **0 PROJECT
(`ZiskFv.*`) axioms; Sail+kernel external** (the M-ext equiv-wrapper closure is
currently axiom-clean modulo that external trust).

---

## V. Verification commands (run from the worktree root, inside `nix develop`)

```bash
lake exe cache get                          # FIRST, after `git worktree add`
lake build                                  # the FV check — every theorem typechecks
trust/scripts/check-all.sh                  # V1 syntactic (seconds, no build)
trust/scripts/check-all-semantic.sh         # V2 semantic (needs oleans; runs the deep-binder check)
nix run .#test                              # full suite — before claiming any PR complete
# Inspect / regenerate the deep construction-binder snapshot (the per-family signal):
lake exe trust-gate print-construction-binders-deep
lake exe trust-gate print-construction-binders-deep > trust/generated/baseline-construction-theorem-binders.txt
trust/scripts/regenerate.sh                 # refresh all eight baselines after adding a family
trust/scripts/check-construction-theorem-binders.sh   # diff -u baseline vs current; must add exactly the new family's flat block
```

---

## A. Anti-laundering principle — VERBATIM (copy into every sub-agent prompt; from SPINE §8)

> **Promise discharge exists to REDUCE residual trust, not rearrange it.** Refuse
> these laundering patterns: (1) **Axiom inflation** — a hypothesis becomes an
> axiom of the same shape; every new axiom must fit a documented `trusted-base.md`
> class with a citation to a specific PIL line / Rust fn / soundness theorem.
> (2) **Hypothesis splitting/renaming** — one promise becomes N; the
> hypothesis-count and caller-burden gates must show net REDUCTION. (3)
> **Universalizing too eagerly** — `(h_x : P r)` → `(h_univ : ∀ r, P r)` just
> moves trust to a stronger caller-supplied universal unless it is actually
> dischargeable from the trust ledger. (4) **Overstrong AIR validators** — a
> `Valid_AIR` constraint stronger than the circuit enforces makes equivalences
> vacuous; any change needs a PIL citation + constructibility sketch. (5)
> **Definitional aliasing** — `def Foo := <promise>` hides a hypothesis; mark new
> defs `@[reducible]` so V2 unfolds them, or justify.
>
> **The operational metric:** every promise-discharge PR must REDUCE or hold both
> the hypothesis-count baseline and the caller-burden ledger, with the diff
> visibly REMOVING more than it adds. A "net zero" PR discharged nothing.
>
> **CRITICAL REPORTING RULE:** if a fact you expected to derive cannot be derived,
> NAME it as an explicit premise and REPORT it — never axiomatize, strengthen a
> validator, or hide it in a record to make a metric move. Reporting a genuine
> residual is success, not failure.
>
> Before declaring a step complete, verify: the metric shrank (or residuals are
> explicit & named); any new axiom fits an existing class with citation; any new
> `Valid_AIR` constraint or top-level `def` was reviewed for hidden-promise risk;
> and the PR/commit text uses the canonical glossary terms (`trust/README.md`).

**Project-specific addendum (this sweep):** every sound construction's residuals
(decode pins, Sail reads, lane bridges, `nextPC_matches`, exec artifacts, and any
I-type imm pin / W extract / Sail-form discriminator) MUST be **top-level binders**
of the construction theorem — never carried inside a `*RowBinding` /
`MainRowProvenance`-style record. The recursive (Option X) deep gate enforces this
mechanically (a smuggled record surfaces immediately as dotted-path leaf lines);
the executor enforces the spirit. The single per-family progress signal is the deep
baseline diff growing by EXACTLY the family's honest flat binders.

---

## R. Risks & open items

- **The deep-baseline diff is the ONLY mechanical per-family progress signal.** A
  net-zero diff, or one that adds dotted-path leaf lines (record fields), is
  laundering not progress. The reviewer confirms each new block is a FLAT list of
  named top-level binders and the existing blocks are byte-identical.
- **Anti-vacuity is a per-family check, not inherited (SPINE §4.9).** Each new
  construction must keep `execRow` a genuine ∀-binder; the bus must be built from
  the real trace row so the residuals stay jointly satisfiable. Hard-coding
  `execRow := []` makes the exec hypotheses contradictory → vacuous, and the deep
  gate does NOT catch this (it inspects binder TYPES, not satisfiability) — a human
  review obligation.
- **XOR / XORI op = 16 wrinkle (verified real).** OP_XOR = 16 fails the `op_val < 16`
  precondition of `logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` that the AND
  construction body uses. XOR/XORI must use the
  `static_table_logic_mode_pins_of_emit` (3-way selector) +
  `byte_chain_discharge_logic_of_static_row` route instead. Confirm on compile.
- **ADD/ADDI provider ambiguity is REAL and the resolution is unwritten.** The
  Layer-A wrapper returns a genuine disjunction; there is no `construction_add_sound`.
  The two-arm-vs-one-arm-plus-exclusion choice is a reviewer-facing design decision
  (PR4). Do not miscount the existing `via_binaryadd` op-bus arms as a sound ADD.
- **W-types are NEEDS-WORK, not salvage.** The m32 = 1 binary 32-bit lane-binding
  lemma (`input_r1_packed_a32_row`) does not exist and must be authored (the
  binary analog of the shift bridge's m32 = 1 lemma). Until then "salvage exists"
  is FALSE for W-types; if deferred, the W constructions carry `h_input_r{1,2}_extract`
  as enlarged residuals — honest, but flag it.
- **Shifts are a separate template instantiation, not the busSub path.** Bare-execute
  goal (no nextPC prelude) + BinaryExtension provider + `op_is_shift` lane route +
  different byte-chain. Ready, but the bus harness is parallel, not a literal copy.
- **M-extension is NOT in the sweep.** Its op-bus construction spine (extractor,
  `_from_binding` wrapper, `_of_static_row`, witness-from-balance derivation) is
  absent; div/rem additionally face the ArithDiv-OpBus-nil ensemble gap; signed M-ext
  is defect-BLOCKED. Separate sub-stream.
- **All next-PC stays a residual (#100).** No family here derives `nextPC_matches`;
  it is a named bucket-(b)-pending-infra binder, same as SUB/AND. Branches, loads,
  stores, U/J, FENCE are OUT of scope (blocked on #100/#101/#76/defects).
- **Trust phrasing.** Every PR states **0 PROJECT (`ZiskFv.*`) axioms;
  Sail-translation + Lean-kernel axioms present as documented external trust** —
  never "0 axioms" unqualified (SPINE §4.1).
- **Build status not independently re-run here (read-only).** Existence/absence of
  every file/lemma/OP-value above was grep/source-verified on the worktree at
  `bdd8cca9`; the STATUS/PR claims of green builds were not re-executed.

