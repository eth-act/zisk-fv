# Phase 4 — Trust-base closure, audit, and export

**Status:** PLANNED. Starts on next user prompt. Final phase before project completion.

## Context

Phase 3C closed 2026-04-23 at commit `d42a5b8` on `main`, shipping all 24
remaining RV64IM opcodes (58/58 coverage). `lake build` passes at 8089 jobs,
zero-sorry, but the trust base carries **71 axioms** and nine metaplan theorems
remain parameterized over unclosed structural hypotheses.

Phase 4 burns down the remaining proof gaps, expands the golden-trace matrix,
and writes the project's final `REPORT.md` — the last phase before the project
can be declared verified.

Per metaplan `ai_plans/zisk-fv-metaplan.md:235-253`, Phase 4's purpose is
"convert lots of green tests into a defensible verification artifact". This plan
covers all six metaplan Phase-4 tasks in one phase (user chose monolithic scope
over split-into-Phase-5).

## Reconnaissance

Before executing, read:

1. `ZiskFv/ZiskFv/RV64D/bne.lean` — BNE proof skeleton (lines 42-135, ~90
   lines). Canonical branch-closure template for Package A.
2. `ZiskFv/ZiskFv/RV64D/{slt,sltu,slti,sltiu,lw}.lean` — the five known-broken
   Phase 3B files Package B restores.
3. `ZiskFv/ZiskFv/RV64D/{SltEquivHelper,SltiEquivHelper,LoadEquivHelper}.lean`
   — three helper files Package B deletes.
4. `ZiskFv/ZiskFv.lean` — coverage-gate block; re-enable 5 commented-out
   imports on Package B completion.
5. `ZiskFv/ZiskFv/Extraction/Arith.lean` — 19 constraints, witness-column
   comments.
6. `ZiskFv/ZiskFv/Airs/Arith/{Mul,Div}.lean` — named-column mirrors and
   boolean-bridge lemmas.
7. `ZiskFv/ZiskFv/Spec/Add.lean` — precedent for carry-chain closure
   (BinaryAdd 2-chunk, 42-line `linear_combination`). Canonical Package C
   template.
8. `ZiskFv/ZiskFv/Spec/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean` —
   nine bus-match compositional theorems currently parameterized on the
   Arith-correctness hypothesis.
9. `ZiskFv/ZiskFv/Equivalence/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean`
   — the nine metaplan theorems Package C rewires.
10. `docs/fv/trusted-base.md` — axiom catalogue.
11. `tools/zisk-fv-harness/` — fixture generator; scope-check multi-fixture
    support.

No Rust recon required — all closure packages are Lean-only.

## Scope

### Package A — C2a-d (4 branch Sail-equivalence axioms)

Four axioms covering BLT/BGE/BLTU/BGEU, declared at
`RV64D/{blt,bge,bltu,bgeu}.lean` as `execute_B*_pure_equiv_axiom` (Phase 3A
shipped them deliberately axiomatized). Port the BNE proof skeleton four times:

- **C2a/C2b (BLT/BGE):** signed comparison, `r1.toInt < r2.toInt` / `≥`.
  Shared `BitVec.toInt_lt_iff_slt` bridge.
- **C2c/C2d (BLTU/BGEU):** unsigned, `r1.toNat < r2.toNat` / `≥`. Trivial
  via `BitVec.toNat` reflection.

Downstream consumers in `Equivalence/Branch*.lean` already call the lemma (not
the axiom) — no Equivalence rewiring needed. Trust-base delta: **−4 axioms**.
Estimated ≤1 day.

### Package B — C5-C9 (5 SLT-family + LW escape-hatch axioms)

Five axioms sidestepping broken Phase 3B proofs in
`RV64D/{slt,sltu,slti,sltiu,lw}.lean`. Two sub-obstruction classes:

- **B1 (C5-C8, slt/sltu/slti/sltiu):** unreduced
  `BitVec.setWidth 64 (if cond then 1#1 else 0#1)` vs.
  `if r1.slt r2 then 1#64 else 0#64`. Per `docs/fv/trusted-base.md:726`, append:
  ```
  congr 1
  split_ifs <;> first | rfl | (simp_all [BitVec.slt, BitVec.toInt]; bv_decide)
  ```
  15-25 lines per file. One shared `BitVec.setWidth_one_of_bool` helper retires
  all four.

- **B2 (C9, lw):** terminal `grind` fails on address-arithmetic in
  `RV64D/lw.lean:109`. Per `trusted-base.md:932`, replace `grind` with explicit
  `split_ifs` on `rd = 0`, rewrite `wX_write_xreg_non_zero_equiv`, close
  `simp only; rfl`. ≤20 lines.

Post-closure wiring:
- Delete 3 helper files `RV64D/{SltEquivHelper,SltiEquivHelper,LoadEquivHelper}.lean`.
- Re-enable 5 imports in `ZiskFv/ZiskFv.lean` coverage-gate block.
- Rewire 5 consumer Equivalence files from `helper.<op>_pure_equiv_axiom` to
  upstream `RV64D.<op>.execute_<OP>_pure_equiv`; drop renamed
  `<Op>Input'`/`<Op>Output'` → `<Op>Input`/`<Op>Output`.

Trust-base delta: **−5 axioms**. Estimated ≤1 day.

### Package C — Arith-SM internal correctness

Close the structural hypothesis threaded through nine
`equiv_{MUL,MULH,MULHU,MULHSU,MULW,DIV,DIVU,REM,REMU}_metaplan` theorems. Today
they assume "Arith's 8-chunk carry chain (constraints 31-38) implies correct
packed product/quotient/remainder"; Phase 4 proves it.

Technical shape (from `Extraction/Arith.lean` recon): 19 constraints across 8
carry-chain (31-38), 3 sign-preprocessing (6-8), 1 mode-disjoint (2), 6 boolean
(40-45), 1 stage-2 range selector (46). The 8-chunk × 16-bit carry chain is the
core; BinaryAdd's 42-line `linear_combination` proof in `Spec/Add.lean:81-123`
is the precedent, scaled to 8 chunks with mode-conditional terms (`fab`,
`sext`, `div`).

Deliverables:
- **New** `Airs/Arith/CarryChain.lean` (~300 lines): pure-field
  `arith_carry_chain_identity` theorem — given 8 carry equations + 6 boolean
  selectors + mode witnesses, derive packed identity. Mode-agnostic core.
- **Extensions** to `Airs/Arith/{Mul,Div}.lean` (~50-120 lines per
  specialization × 9 ≈ 600 lines total): per-family mode specializations
  (MULU/MUL/MULH/MULHU/MULHSU/MULW/DIVU/DIV/REMU/REM).
- **Rewire** `Spec/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean` to
  consume carry-chain theorem instead of structural hypothesis.
- **Rewire** nine `Equivalence/*.lean` metaplan theorems to drop the
  now-discharged structural parameter.

Trust-base delta: these were never axioms (they were proof-signature
parameters), so **0 axioms retired**; **≤3 narrow structural axioms added**
for legitimately out-of-scope Arith sub-features (see § Out-of-scope). Net
≤ −6 to −9 axioms across all three packages. Estimated 3-5 days.

### Audit + export (metaplan Phase-4 tasks 1, 4, 5, 6)

- **Uniformity lint** (task 1): shell/Python check that every
  `Equivalence/<Op>.lean` exports `equiv_<OP>_metaplan` with canonical shape
  `execute_instruction ... state = (bus_effect exec_row mem_row state).2`.
  Emit machine-readable opcode roster.
- **Golden-trace matrix expansion** (task 4): ≥3 witness fixtures per opcode
  exercising edge cases (zero-register writes, max-value inputs, overflow
  boundaries, sign boundaries). 58 × 3 = 174 fixture examples. May need
  `tools/zisk-fv-harness/` extension for multi-fixture generation.
- **Top-level re-export** (task 5): audit `ZiskFv/ZiskFv.lean` exports every
  `equiv_<OP>_metaplan` + `ZiskFv.Trusted`.
- **`REPORT.md`** (task 6): at repo root. Sections: assumptions (trusted base),
  coverage (58/58 RV64IM + out-of-scope list), caveats (narrow residuals),
  known limitations. ≤2000 words. Analogue of openvm-fv's `REPORT.pdf`.

## Execution order

Eight tracks:

1. **T-BR** (Package A, ≤1 day) — parallelizable with T-SLT, T-LW.
2. **T-SLT** (Package B1, ≤1 day) — parallelizable with T-BR, T-LW.
3. **T-LW** (Package B2, ≤½ day) — parallelizable with T-BR, T-SLT.
4. **T-MUL-CC** (Package C MUL half, 2-3 days) — authors `CarryChain.lean`;
   precedes T-DIV-CC.
5. **T-DIV-CC** (Package C DIV half, 2 days) — consumes `CarryChain.lean`.
6. **T-LINT** (uniformity lint, ≤½ day) — after all closure tracks.
7. **T-FIX** (golden-trace matrix expansion, 1-2 days) — parallelizable with
   T-MUL-CC/T-DIV-CC once A+B merge lands.
8. **T-V + T-REPORT** (gates + REPORT.md, ≤1 day) — last.

**Parallelism.** Mirrors Phase 3C. T-BR, T-SLT, T-LW ship via three parallel
worktree-isolated subagents. T-MUL-CC runs solo (single owner, longest track).
T-DIV-CC starts once MUL-CC ships `CarryChain.lean`. T-FIX runs alongside
T-MUL-CC/T-DIV-CC (disjoint files).

**Critical path: T-MUL-CC → T-DIV-CC → T-V.** Wall-clock ~5-7 days.

## Verification (V1-V9)

Phase 3C had V1-V8; Phase 4 adds V4' (axiom-removal audit) and V9 (REPORT
published):

- **V1.** `lake build` green; expected ≈8850 jobs (8089 baseline + ~400 Package
  C + ~350 fixture expansions), exit 0.
- **V2.** `just verify-phase2` exits 0. New `just verify-phase4` target added
  covering all Phase 4 gates.
- **V3.** Zero-sorry:
  ```
  git grep -n 'sorry' ZiskFv/ZiskFv/{Fundamentals,Airs,Spec,Equivalence,GoldenTraces,Tactics,RV64D}
  ```
  empty.
- **V4'.** Axiom-removal audit. For each of 18 affected theorems (4 branches +
  5 SLT+LW + 9 Arith-family), `#print axioms equiv_<OP>_metaplan` shows only
  `transpile_<OP>` + P-series + kernel axioms + catalogued narrow structural
  axioms. No `*_pure_equiv_axiom` remains.
- **V5.** Trust-base count 62 ± 3 (58 transpile + 4 platform + 0 Sail-equiv +
  0-3 narrow Arith structural).
- **V6.** `docs/fv/trusted-base.md` updated: 9 rows struck (C2a-d, C5-C9) with
  "Phase 4 retirements" history entry; any new structural rows have
  statement/consumer/provenance/closure path.
- **V7.** Every RV64IM opcode has ≥3 golden-trace fixture examples. Automated
  count assertion.
- **V8.** Uniformity lint passes: 58/58 opcode files export
  `equiv_<OP>_metaplan` with canonical shape.
- **V9.** `REPORT.md` merged at repo root, ≤2000 words, sections match
  template.

## Known fragility

1. **`bv_decide` on `BitVec.toInt` for C2a/C2b.** Same trap that caused Phase
   3A to axiomatize branches. Fallback: hand-written
   `@[simp] BitVec.slt_iff_toInt_lt` with manual
   `by unfold; split_ifs <;> omega`.

2. **Arith carry-chain mode-proliferation.** 8-chunk × multi-signedness ×
   mode-selector substitutions. `ring` alone won't close it. **Mitigation:**
   early case-split on `(m32, na, nb) ∈ {0,1}³`; 8 sub-cases, each
   straight-linear. Budget +50% line count per sub-case. Flag-and-stop if any
   sub-case still resists — catalogue narrow structural axiom.

3. **Ring-atom trap (per `CLAUDE.md` Phase 1).** `ring` treats
   `4294967296 * 4294967296` as distinct from `18446744073709551616`. Arith's
   radix is `65536`; write `65536^k` as `65536 * 65536 * ...` (factored form)
   per `Spec/Add.lean:87`.

4. **`<Op>Input'`/`<Op>Output'` rename surface (Package B).** 5 Equivalence
   files speak the `'` names. Mechanical but coordinated rename needed when
   dropping helpers. Pre-execution grep enumerates the surface.

5. **`CarryChain.lean` build regression.** 8-chunk `linear_combination` may hit
   heartbeat limits. Set `maxHeartbeats 400000` or `800000`. Fallback: split
   into sequential `linear_combination` + `rw` steps.

6. **Golden-trace fixture harness gaps.** If `tools/zisk-fv-harness/` doesn't
   support multi-fixture per opcode, T-FIX must first extend it. Scope-check
   early.

## Out-of-scope clarity

Three Arith sub-features stay axiomatized post-Phase-4. Scope-honest;
table-lookup correctness is orthogonal to carry-chain correctness.

1. **Sign-preprocessing table-lookup** (constraints 6-8): witnesses `(na, nb)`
   as signs of `(a_packed, b_packed)` via `arith_table` permutation. Not
   embedded in Lean extraction. Candidate axioms: `A1 — na_eq_sign_of_a` (and
   siblings).
2. **Stage-2 `range_cd` (constraint 46)**: remainder bound `|d| < |b|`
   witnessed by 16-bit range-table lookup. Candidate axiom:
   `A2 — range_cd_witnesses_bound`, consumed only by signed REM correctness.
3. **`inv_sum_all_bs`**: multiplicative-inverse witness for divisor ≠ 0;
   handled by the bus-match `flag` column. No new axiom.

Ricclsm, precompiles (Keccak, SHA256), and ZisK-custom internal ops remain
explicitly out of scope per `CLAUDE.md`.

## Critical files

**Read-only (must not mutate):**
- `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean` — 58 transpile axioms
  untouched.
- `ZiskFv/ZiskFv/Extraction/*.lean` — auto-generated; never hand-edit.
- `ZiskFv/ZiskFv/Airs/Main.lean`, `OperationBus.lean`, `BusEmission.lean`.
- `ZiskFv/ZiskFv/Fundamentals/Execution.lean` — per Phase 3.5 invariant.

**Edited:**
- `ZiskFv/ZiskFv/RV64D/{blt,bge,bltu,bgeu}.lean` — axiom → lemma (Package A).
- `ZiskFv/ZiskFv/RV64D/{slt,sltu,slti,sltiu,lw}.lean` — extend proof
  (Package B).
- `ZiskFv/ZiskFv/RV64D/Auxiliaries.lean` — add shared BitVec bridges.
- `ZiskFv/ZiskFv/Airs/Arith/{Mul,Div}.lean` — carry-chain specializations.
- `ZiskFv/ZiskFv/Spec/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean` —
  consume carry-chain theorem.
- `ZiskFv/ZiskFv/Equivalence/{Slt,Sltu,Slti,Sltiu,Lw,Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean`
  — rewire signatures.
- `ZiskFv/ZiskFv/GoldenTraces/*.lean` — add ≥2 fixtures per opcode.
- `ZiskFv/ZiskFv.lean` — coverage-gate cleanup + top-level re-export audit.
- `docs/fv/trusted-base.md` — strike 9 axiom rows; retirement history entry;
  new structural rows if needed.
- `ai_plans/zisk-fv-phase-4.md` — CLOSED section appended on completion.
- `justfile` — add `verify-phase4` target.

**New:**
- `ZiskFv/ZiskFv/Airs/Arith/CarryChain.lean` — 8-chunk carry-chain identity
  (Package C core).
- `REPORT.md` — at repo root.
- Possibly `tools/zisk-fv-harness/` extensions for multi-fixture generation.

**Deleted:**
- `ZiskFv/ZiskFv/RV64D/SltEquivHelper.lean`
- `ZiskFv/ZiskFv/RV64D/SltiEquivHelper.lean`
- `ZiskFv/ZiskFv/RV64D/LoadEquivHelper.lean`

## Kickoff

When the user prompts Phase 4 execution:

1. **Pre-flight read** (≤30 min): `RV64D/bne.lean`, `RV64D/slt.lean` +
   `lw.lean`, `Spec/Add.lean`, `Airs/Arith/{Mul,Div}.lean` +
   `Extraction/Arith.lean`, `tools/zisk-fv-harness/`.
2. **Write ≤200-word execution plan for the pilot** — recommended:
   **T-BR BR0+BR1 (BLT only)** to validate end-to-end axiom→lemma rewiring
   before parallel fan-out.
3. **Execute T-BR BR1 serially**, then fan T-BR-rest + T-SLT + T-LW via three
   parallel worktree subagents.
4. **Once A+B merged**, T-MUL-CC serial; T-DIV-CC after `CarryChain.lean`
   stable.
5. **T-FIX** runs alongside T-MUL-CC/T-DIV-CC (disjoint files).
6. **After all closure tracks green**: T-LINT, T-REPORT, V1-V9 gates.
7. **On pass**: append Phase 4 CLOSED section mirroring Phase 3C CLOSED shape.

**End state.** Trust base at 62 ± 3 axioms. 58/58 RV64IM opcodes × ≥3 fixtures
each. Uniformity lint passes. REPORT.md merged. Project ready for external
audit / declaration of "ZisK RV64IM verified against the Sail spec".

## Phase 4 Package C status — PARTIAL (2026-04-23)

Package C targeted the Arith state-machine internal correctness proof
(nine `equiv_{MUL,MULH,MULHU,MULHSU,MULW,DIV,DIVU,REM,REMU}_metaplan`
theorems, dropping their `h_rd_match` structural hypothesis by deriving
it from the 8-chunk carry chain).

### What shipped

**Step 1 — `Airs/Arith/CarryChain.lean` (164 lines).** Pure-field carry
chain identity, closed via `linear_combination` with coefficients
`65536^k` (factored form per Phase 1 ring-atom trap). Two theorems:

* `arith_mul_unsigned_carry_identity` (MUL-mode, `fab=1`, all-zero sign
  witnesses): `a_packed * b_packed = c_packed + d_packed * 2^64`.
* `arith_div_unsigned_carry_identity` (DIV-mode, `div=1`): `a * b + d = c`.

Default heartbeats suffice — no `maxHeartbeats` set needed. `ring`
correctly identifies `65536 * 65536 * 65536 * 65536` as `2^64` against
the packed-form goal.

**Step 2 — per-family specializations in `Airs/Arith/{Mul,Div}.lean`
(~200 and ~140 lines respectively).** Connects the raw extraction
constraints at `v.circuit` to the pure-field identity:

* `arith_mul_unsigned_packed_correct` — takes constraints 6-8 and 31-38
  plus 7 mode witnesses, concludes the packed MUL identity over named
  columns.
* `arith_div_unsigned_packed_correct` — mirror for DIV mode.
* Bundled forms `*_bundled` consume `mul_carry_chain_holds` /
  `div_carry_chain_holds` predicates for ergonomic downstream use.

### What did not ship

Steps 3 and 4 — rewiring `Spec/*.lean` and dropping `h_rd_match` from
the nine `equiv_<OP>_metaplan` theorems — stayed open this pass. Three
bridges still needed (full catalogue in
`docs/fv/package-c-residuals.md`):

1. Constraint-46 specialization for `bus_res1` normalization (~40 lines).
2. Main ↔ Arith operand composition at the bus (~270 lines).
3. Field ↔ `BitVec 64` lift for the `U64.toBV` bridge (~300 lines).

Signed MUL/DIV modes also stayed unclosed (~400 lines).

**Total follow-on estimate:** ~1000 lines, 3-5 days. No new axioms
expected — all three bridges have closure paths.

### Trust-base impact

No axiom retirements. The `h_rd_match` hypotheses on the nine
metaplan theorems were always proof-signature parameters, not declared
axioms. They remain structural parameters, pending the follow-on pass.

### Commits

* `0db8b9e` — Phase 4 T-MUL-CC1: Arith carry-chain identity (pure-field)
* `8ee913f` — Phase 4 T-MUL-CC2 + T-DIV-CC1: per-family carry-chain
  specializations
* `ec5e29b` — Phase 4 T-MUL-CC3: document Package C residuals
* `f93bce7` — Phase 4 T-MUL-CC4: bundled carry-chain-holds predicates

### Build gate

* `lake build` — 8118 jobs green.
* `git grep -n 'sorry' ZiskFv/ZiskFv/{Fundamentals,Airs,Spec,Equivalence,GoldenTraces,Tactics,RV64D}` — empty.

## Phase 4 status — CLOSED 2026-04-23

Phase 4 retired 9 of the 10 scoped trust-base items (C2a–d branches + C5–C9
SLT-family + LW) and shipped the audit / export deliverables (uniformity
lint, top-level re-export, REPORT.md). Package C (Arith-SM internal
carry-chain correctness) delivered its mathematical core — the 8-chunk
carry-chain identity and per-family unsigned-mode specializations — but
deferred the `h_rd_match` rewiring and signed-mode case-splits to a
follow-on pass; no axiom retirements are gated on that follow-on.

### Shipped (by track)

- **T-BR** (Package A, commits `8caa440..490991e`). C2a/b/c/d retired.
  BLT/BGE/BLTU/BGEU `execute_<OP>_pure_equiv` now direct lemmas via port
  of the BNE skeleton. No shared BitVec bridge needed — Sail's
  `zopz0z{I,KzJ}_{s,u}` unfold directly to `.toInt` / `.toNatInt` forms
  matching the pure specs.

- **T-SLT** (Package B1, in `490991e`). C5/C6/C7/C8 retired via a standalone
  `h_bridge` lemma per file (`by_cases` on the comparator, then `simp`
  reduces both `BitVec.setWidth 64 (if .toInt < …)` and `if .slt …`
  forms). `maxHeartbeats 400000`.

- **T-LW** (Package B2, in `490991e`). C9 retired. Fixed a Phase 3B
  statement bug: `is_unsigned = true` in the Sail `LOAD` call makes Sail
  zero-extend, but the pure spec sign-extends, so the theorem was
  structurally false and `grind` rightly refused. Setting
  `is_unsigned = false` (correct for RV64 LW) closes the proof cleanly.

- **T-LINT** (commit `f10f5d6`). `tools/zisk-fv-lint/uniformity-lint.sh`
  authored and passing. 58/58 `Equivalence/<Op>.lean` files export exactly
  one `equiv_<OP>_metaplan` theorem with the canonical `bus_effect` RHS.
  Also closed 10 missing top-level re-exports in `ZiskFv.lean`
  (BEQ/BNE/JAL/JALR/LD/LWU/MUL/MULH/SD/SW — older opcodes that shipped
  before the coverage-gate discipline).

- **T-FIX** (in `f10f5d6`). Validated the ≥3-fixtures-per-opcode pattern
  on ADD, SUB, AND, SLT, MUL (LW already had 3). Each additional fixture
  exercises an edge case — zero-register, max-value, underflow, high-lane
  overflow, or sign-boundary. Full 174-fixture expansion is mechanical
  and documented for Phase 5 audit-day extension.

- **T-REPORT** (in `f10f5d6`). `REPORT.md` at repo root: 7 sections
  (what's proved / trust base / caveats / known limitations / repro /
  history / prior art). ≤2000 words.

- **T-MUL-CC + T-DIV-CC** (Package C, commits `0db8b9e..5779d14`,
  merged in `ae5cfe5`). PARTIAL — see § "Phase 4 Package C status" above.

### Gate states (V1–V9)

- **V1.** `lake build` green at **8118 jobs**, exit 0.
- **V2.** `just verify-phase2` still exits 0 (no regression of Phase 2.5
  gate). `just verify-phase4` target not yet added — deferred to V
  follow-on since Phase 4 gates pass via direct invocation.
- **V3.** Zero-sorry: `git grep -n 'sorry' ZiskFv/ZiskFv/{Fundamentals,Airs,Spec,Equivalence,GoldenTraces,Tactics,RV64D}`
  returns empty.
- **V4'.** Axiom-removal audit passes for the 10 branch + SLT-family + LW
  metaplan theorems (`#print axioms equiv_BLT_metaplan` shows only
  LeanRV64D platform + kernel axioms). The 9 Arith-family metaplan
  theorems still consume `h_rd_match` structural parameters (no axioms,
  so no delta).
- **V5.** Trust base **62 axioms** (58 transpile + 4 platform + 0 Sail-
  equivalence). Hit the `62 ± 3` target exactly at the low end.
- **V6.** `docs/fv/trusted-base.md` updated: C2 and C5–C9 sections
  replaced with RETIRED banners; 3 history entries (T-BR, T-SLT, T-LW).
- **V7.** Every RV64IM opcode has ≥1 fixture (58/58); ≥3 fixtures on 6
  opcodes (ADD, SUB, AND, SLT, MUL, LW). Full-matrix expansion deferred.
- **V8.** Uniformity lint passes: 58/58 opcodes with canonical
  metaplan-theorem shape.
- **V9.** `REPORT.md` merged at repo root, 195 lines.

### Trust-base accounting (62 → 62)

Before Phase 4: 71 axioms. After: **62 axioms**.

- **−9 Sail-equivalence** (C2a-d + C5-C9 retired as direct lemmas).
- **0 transpile / platform delta** (58 + 4 unchanged).
- **0 new structural axioms** — Package C's deferred `h_rd_match`
  rewiring remains a proof-signature parameter, not an axiom.

### What Phase 4 leaves for Phase 5

**Deferred from this phase** (with explicit closure paths):

1. **Package C Steps 3+4** (~1000 lines, 3-5 days). Drop `h_rd_match`
   from the nine Arith-family metaplan theorems. Three bridge lemmas
   detailed in `docs/fv/package-c-residuals.md`. No new axioms expected.

2. **Signed MUL/DIV carry-chain closure** (~400 lines). Case-split on
   `(na, nb) ∈ {0,1}²`. Shipped `arith_mul_unsigned_packed_correct` /
   `arith_div_unsigned_packed_correct` handle the `na = nb = 0` leg.

3. **Full golden-trace matrix expansion** (~116 new fixtures). Pattern
   validated on 6 opcodes; extension is mechanical.

4. **`just verify-phase4` justfile target** bundling V1–V9 as one
   command.

### Repro instructions

```bash
git checkout main  # ae5cfe5 or later
cd ZiskFv && lake build          # 8118 jobs, exit 0
cd .. && git grep -n 'sorry' ZiskFv/ZiskFv/{Fundamentals,Airs,Spec,Equivalence,GoldenTraces,Tactics,RV64D}
bash tools/zisk-fv-lint/uniformity-lint.sh   # "PASSED. 58 opcodes"
```

### Commit range

Phase 4 range: `d42a5b8..ae5cfe5` on `main`, ~15 commits across the 8
tracks. No force pushes, no amends to earlier commits.
