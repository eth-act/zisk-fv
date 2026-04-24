# Phase 4.5 — Residual closure (Package C + Signed Arith + LD/SD shapes + fixtures)

## Context

Phase 4 closed 2026-04-23 at `a1595bf` on `main`: `lake build` green at
8118 jobs, zero-sorry, 62 axioms (58 transpile + 4 platform), uniformity
lint passing, `REPORT.md` shipped. The project is at a "defensible
completion point."

The openvm-fv parity audit (`docs/fv/openvm-fv-parity.md`) identifies
three structural-parity gaps vs. the openvm-fv template:

- **Gap 1 — Sail input state derivation** (h_input_r1/r2/pc/rd parameters)
- **Gap 2 — `h_rd_match` derivation** (bus-bytes ↔ pure-spec rd)
- **Gap 3 — Unwired transpile axioms** (58 declared-but-unused)

**Phase 4.5 scope** is *not* the full parity closure. It ships the
completeness work that was intentionally deferred from Phase 4 (Package
C Steps 3+4, signed Arith modes, LD/SD bus shapes, full 174-fixture
matrix, `just verify-phase4` target) plus closes **Gap 2** for the 9
Arith-family metaplan theorems. **Gaps 1 and 3** require a
~2500-4000-line transpile-axiom refactor (discovered session 1 — the
axioms have shape `∃ row : ZiskInstructionRow, …` with no connection to
the concrete `Valid_Main` row); that refactor is scoped as **Phase 5**
at `ai_plans/zisk-fv-phase-5.md` and blocks both Gap 1 and Gap 3 closure.

**End state after Phase 4.5:**
- Trust base unchanged at 62 axioms (plus possibly +1 narrow vmem axiom if Track C needs it).
- 9 Arith-family `equiv_<OP>_metaplan` theorems drop `h_rd_match`.
- 51 MEM-family metaplan theorems decompose `h_bus_execute_matches_sail` into shape-(d/e) structural parameters (matching the ALU/branch/jump shape-a/c pattern).
- Signed MUL/DIV carry-chain polynomial identity closed.
- 58 × 3 = 174 golden-trace fixtures.
- `just verify-phase4` reproducibility gate.
- Gap 1 (h_input_*) and Gap 3 (unwired transpile axioms) remain — explicitly Phase 5 scope.

## Session-1 progress

Committed to `main`:
- `2b354e7` Bridge 1 (`Airs/Arith/Bridge1.lean`): constraint-46 normalization.
- `5a68556` Bridge 2 (`Spec/MulField.lean`): Main↔Arith field composition
  + `main_mul_unsigned_field_correct` theorem.

Not yet shipped:
- **Bridge 3** (`Fundamentals/PackedBitVec.lean`) — field→BitVec 64 lift.
  Session 1 attempt hit a `bv_decide` vs `omega` tactic gap on the
  shift-or-to-multiplication-addition conversion. Needs more careful
  proof plumbing — either pure `BitVec`-form using `bv_decide` exclusively,
  or `Nat`-form with `Nat.shiftLeft_eq` + disjoint-bits-or lemmas.
- Tracks B, C, D, E, F — untouched.

## Scope — six tracks

### Track A — Package C closure (Arith bridges, unsigned) — Gap 2

**Status:** A1, A2 shipped (session 1). A3 + rewiring remain.

- **Bridge 3** (A3, remaining) — field → `BitVec 64` lift. New file
  `ZiskFv/ZiskFv/Fundamentals/PackedBitVec.lean`, ~350 lines. Three
  sub-lemmas:
  1. `u64_toBV_eq_ofNat_bytesum` — `U64.toBV #v[x0..x7]` equals
     `BitVec.ofNat 64` of the little-endian byte-sum.
  2. `fgl_chunks_packed_val_eq_natsum` — given chunk bounds
     `< 2^16`, the packed Goldilocks value has `.val` equal to the
     natural-number chunk-sum, no wraparound.
  3. `arith_c_equals_product_bitvec` — composed: the 8-byte bus-row
     register-write value equals `BitVec.ofNat 64 (c_chunks_packed.val)`.

- **A-rewire** — drop `h_rd_match` from
  `Equivalence/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean`
  (9 theorems). Proof body discharges via `Bridge1 ∘ Bridge2 ∘ Bridge3 ∘
  arith_mul_unsigned_packed_correct`. ~200 lines mechanical.

**Effort (remaining):** ~550 lines. 2-3 days.

### Track B — Signed MUL/DIV carry-chain closure

Extend unsigned carry-chain identity to `(na, nb) ∈ {0,1}²` via
per-quadrant sign-adjustment through `np`/`nr` witnesses. Author
`arith_mul_signed_packed_correct` and `arith_div_signed_packed_correct`
in `Airs/Arith/{Mul,Div}.lean`.

Closes signed-mode carry-chain polynomial identity. Does **not** close
the `arith_table` permutation dependency (that stays scope-honest).

**Effort:** ~400 lines. 2-3 days. Blocks: none (Bridge 1 already shipped).

### Track C — Shape (d) and (e) LD/SD bus-emission lemmas

Per `Airs/BusEmission.lean:309-323`, Shape (d) (LD) and Shape (e) (SD)
bus-emission reductions were deferred. 51 MEM-family metaplan theorems
currently parameterize on the monolithic `h_bus_execute_matches_sail`.

Author:
- `bus_effect_matches_sail_load_rrrw` — Shape (d): exec rs1, mem-read 8
  bytes, reg-write rd.
- `bus_effect_matches_sail_store_rrrw` — Shape (e): exec rs1, reg-read
  rs2, mem-write 8 bytes.

Mirror shape-(a)/(c) closure pattern. Memory helpers
(`vmem_read_aligned_equiv` / `vmem_write_aligned_equiv`) may need
authoring or a narrow vmem axiom (audit LeanRV64D first).

Rewire 51 MEM-family Equivalence files.

**Effort:** ~700 lines. 2-3 days. Parallelizable with A, B.

### Track D — Golden-trace matrix expansion

Target 58 × 3 = 174 fixtures. Current: 6 × 3 + 52 × 1 = 70. Need ~104
new fixtures via harness extension + generation.

**Effort:** ½ day harness + 1-2 days generation. Parallel with proof tracks.

### Track E — `just verify-phase4` target

Bundle V1–V11 gates into a justfile target.

**Effort:** ~1 hour at end.

### Track F — Memory + CLOSED + REPORT deltas

- Append **Phase 4.5 CLOSED** section to this file.
- Update `project_phase_status.md`.
- `REPORT.md` §3.1: strike Arith-carry-chain caveat (Package C closed).
- `REPORT.md` §3.3: reflect full fixture matrix.
- `docs/fv/package-c-residuals.md`: mark closed or retire.
- `docs/fv/openvm-fv-parity.md`: mark Gap 2 closed; flag Gaps 1 and 3 as Phase 5 scope.
- `docs/fv/trusted-base.md`: Phase 4.5 history entry.

**Effort:** ½ day at end.

## Execution order

Six-track Gantt. Critical path: A3 (Bridge 3) → A-rewire.

1. **A3 (Bridge 3)** serial in main session (hardest piece; ~2 days).
2. After A3: **A-rewire** (9 Arith files) + **B** (signed) + **C** (LD/SD) in parallel worktree subagents.
3. **D** (fixtures) runs any time, parallel.
4. **E** + **F** at the end.

**Wall-clock:** 5-7 days single-threaded; 3-4 days with subagent parallelism.

## Critical files

**New:**
- `ZiskFv/ZiskFv/Fundamentals/PackedBitVec.lean` — Bridge 3.

**Shipped session 1:**
- `ZiskFv/ZiskFv/Airs/Arith/Bridge1.lean`
- `ZiskFv/ZiskFv/Spec/MulField.lean`

**Edited:**
- `ZiskFv/ZiskFv/Airs/Arith/{Mul,Div}.lean` — signed-mode specializations.
- `ZiskFv/ZiskFv/Airs/BusEmission.lean` — Shape (d/e) lemmas.
- `ZiskFv/ZiskFv/Equivalence/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean` — drop `h_rd_match`.
- `ZiskFv/ZiskFv/Equivalence/{LD,SD,LB,LH,LW,LBU,LHU,LWU,SB,SH,SW,LoadBU,LoadHU,LoadD,LoadWU,StoreD,StoreW}.lean` — shape (d/e) rewire.
- `ZiskFv/ZiskFv/GoldenTraces/*.lean` — +2 fixtures per under-covered opcode.
- `tools/zisk-fv-harness/src/main.rs` — multi-fixture generation.
- `REPORT.md`, `docs/fv/{trusted-base,package-c-residuals,openvm-fv-parity}.md`.
- `justfile`.

## Verification gates (V1–V11)

- **V1.** `lake build` green (~8500 jobs).
- **V2.** `just verify-phase4` exits 0.
- **V3.** Zero-sorry.
- **V4.** 9 Arith `equiv_<OP>_metaplan` theorems have no `h_rd_match` parameter.
- **V5.** Trust-base = 62 (or 63 with documented vmem axiom).
- **V6.** 51 MEM-family metaplan theorems decompose `h_bus_execute_matches_sail`.
- **V7.** 174 golden-trace fixtures.
- **V8.** Uniformity lint passes.
- **V9.** Signed MUL/DIV carry-chain lemmas `#print axioms` clean.
- **V10.** `REPORT.md` §3.1 caveat rewritten; §3.3 updated.
- **V11.** CLOSED section appended to this file.

## Out-of-scope (explicit — deferred to Phase 5)

- **Gap 1 — Sail input state derivation.** `h_input_r1`/`r2`/`pc`/`rd`
  remain parameters on all 41 metaplan theorems.
- **Gap 3 — Transpile axiom wiring.** 58 axioms stay declared-and-unused
  in current shape. Requires axiom-level refactor scoped in Phase 5.
- Arith table-lookup witnesses, Zicclsm, precompiles, ZisK custom ops —
  all scope-honest per CLAUDE.md.
