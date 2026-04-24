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

**Size (remaining):** ~550 lines.

### Track B — Signed MUL/DIV carry-chain closure

Extend unsigned carry-chain identity to `(na, nb) ∈ {0,1}²` via
per-quadrant sign-adjustment through `np`/`nr` witnesses. Author
`arith_mul_signed_packed_correct` and `arith_div_signed_packed_correct`
in `Airs/Arith/{Mul,Div}.lean`.

Closes signed-mode carry-chain polynomial identity. Does **not** close
the `arith_table` permutation dependency (that stays scope-honest).

**Size:** ~400 lines. Blocks: none (Bridge 1 already shipped).

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

**Size:** ~700 lines. Parallelizable with A, B.

### Track D — Golden-trace matrix expansion

Target 58 × 3 = 174 fixtures. Current: 6 × 3 + 52 × 1 = 70. Need ~104
new fixtures via harness extension + generation.

Parallel with proof tracks.

### Track E — `just verify-phase4` target

Bundle V1–V11 gates into a justfile target. Runs at end.

### Track F — Memory + CLOSED + REPORT deltas

- Append **Phase 4.5 CLOSED** section to this file.
- Update `project_phase_status.md`.
- `REPORT.md` §3.1: strike Arith-carry-chain caveat (Package C closed).
- `REPORT.md` §3.3: reflect full fixture matrix.
- `docs/fv/package-c-residuals.md`: mark closed or retire.
- `docs/fv/openvm-fv-parity.md`: mark Gap 2 closed; flag Gaps 1 and 3 as Phase 5 scope.
- `docs/fv/trusted-base.md`: Phase 4.5 history entry.

Runs at end.

## Execution order

Six-track Gantt. Critical path: A3 (Bridge 3) → A-rewire.

1. **A3 (Bridge 3)** serial in main session (hardest piece).
2. After A3: **A-rewire** (9 Arith files) + **B** (signed) + **C** (LD/SD) in parallel worktree subagents.
3. **D** (fixtures) runs any time, parallel.
4. **E** + **F** at the end.

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

## Phase 4.5 status — PARTIAL-CLOSED 2026-04-24

Session-2 shipped Track A3 (Bridge 3) and Track E
(`just verify-phase4`). Full phase closure remains a multi-session
effort; tracks A-rewire, B, C, D are outstanding.

### What shipped

- **A3 — Bridge 3** (`Fundamentals/PackedBitVec.lean`, 206 lines,
  commit `6cddb9b`). Provides six public lemmas:
  - `u64_toBV_toNat` — BV-concatenation to Nat byte-sum, via the
    openvm-fv `BitVec.toNat_append` + `Nat.shiftLeft_add_eq_or_of_lt`
    idiom (`OpenvmFv/Fundamentals/U32.lean:195`). Session-1 blocker
    (`bv_decide` vs `omega` tactic gap) avoided by using the Nat-form
    approach per the plan's fallback.
  - `fgl_byte_coe_toBV8_toNat` — FGL→BitVec 8 coercion preserves
    `.toNat` under byte range.
  - `u64_toBV_of_bytes_toNat` — composed: `U64.toBV` of coerced FGL
    bytes reduces to the Nat byte-sum.
  - `fgl_packed_bytes_nat_cast` — field-packed expression equals
    Nat cast (algebraic identity over `ZMod GL_prime`).
  - `fgl_packed_bytes_val_of_lt_prime` — `.val` equals Nat sum under
    the no-wraparound bound `sum < GL_prime`.
  - `u64_toBV_eq_ofNat_fgl_val` — final bridge consumed by A-rewire.
- **E — `just verify-phase4`** (commit `7ebb55b`). Bundles V1 (lake
  build green), V3 (zero sorry outside `Extraction/`), V8 (uniformity
  lint: 58 opcodes). Runs `verify-phase2` as a regression gate.

### What was learned

- **Scope of A-rewire is larger than the plan estimated.** "Drop
  `h_rd_match`" for the 9 Arith opcodes requires either (a) adding 5+
  decomposed hypotheses per theorem (byte ranges, Main-AIR c-lane ↔
  byte-pack match, Arith field identity, operand-packing identities,
  no-wraparound bound) or (b) deriving all of those from existing
  circuit hypotheses — which in turn requires authoring a Main-AIR
  `register_write_lanes_match` analogue (currently only exists for
  MEM-family in `Airs/MemoryBus.lean:139-143`). Both paths are
  substantive lifts, not the "~200 lines mechanical" the plan
  estimated. Bridge 3 is load-bearing infrastructure, but it is not
  sufficient on its own to close Gap 2 — it needs the bus-emission
  spec that ties Main `c_0`/`c_1` lanes to the register-write entry's
  byte lanes, which is currently only done for the MEM family.

### What remains — carry-over into Phase 4.5.1 (or fold into Phase 5)

- **A-rewire.** 9 Arith `equiv_<OP>_metaplan` theorems still take
  `h_rd_match` as a hypothesis. Gap 2 closure for Arith family still
  open.
- **Track B.** Signed MUL/DIV carry-chain closure. Independent of
  A-rewire; Bridge 1 (`Airs/Arith/Bridge1.lean`) already shipped in
  session 1 covers the unsigned specialization.
- **Track C.** Shape (d) LD / shape (e) SD bus-emission lemmas. 51
  MEM-family metaplan theorems still parameterize
  `h_bus_execute_matches_sail` monolithically. Closing these requires
  reducing an 8-element memory-bus fold, which
  `Airs/BusEmission.lean:309-323` already flags as multi-hour work.
- **Track D.** 58 × 3 = 174 golden-trace fixtures. Currently at 70
  (6 × 3 + 52 × 1). Requires harness extension + 104 new fixtures.
- **Track F (partial).** This CLOSED section appended; remaining docs
  (`REPORT.md` §3.1/§3.3, `docs/fv/{package-c-residuals,openvm-fv-parity,
  trusted-base}.md`) still carry the Phase-4 language. Roll them when
  A-rewire and C ship.

### Recommended next-session plan

1. Pick **one Arith opcode (MUL)** and do A-rewire as a pilot. This
   proves the Bridge 3 → `h_rd_match` discharge chain end-to-end and
   determines the per-opcode template for the remaining 8.
2. In parallel (worktree subagent), author the Main-AIR
   `register_write_lanes_match` analogue in `Airs/MemoryBus.lean`
   (or a sibling module) so the pilot has a named hypothesis to
   consume rather than inlining byte ↔ lane equations.
3. Track B and Track C are independent of A-rewire and can run in
   their own worktree subagents.
