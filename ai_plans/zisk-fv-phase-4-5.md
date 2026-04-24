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

## Phase 4.5 status — CLOSED 2026-04-24

All seven planned tracks shipped, plus two beyond-plan extensions
(LD MEM-family pilot and 32-file ALU rewire). `lake build` green at
8119 jobs, 0 sorry, 58/58 uniformity lint, `just verify-phase4`
exits 0. Trust base unchanged at 62 axioms (58 transpile + 4
platform). Gap 2 (`h_rd_match` derivation) is structurally closed:
**41/41** metaplan theorems now decompose `h_rd_match` into
`h_rd_idx` + `h_rd_val`.

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

- **A-rewire prep — `memory_entry_toField_eq_toBV_toNat`** (commit
  `3076d00`, `Airs/MemoryBus.lean`). Consumable form of Bridge 3 at
  the `MemoryBusEntry` level: given byte ranges + no-wrap bound,
  `U64.toBV` of entry bytes equals `BitVec.ofNat 64
  (memory_entry_toField e).val`. Plus named predicates
  `memory_entry_bytes_in_range` and `memory_entry_packed_no_wrap`.

- **Track C — shape (d) / (e) bus-emission lemmas** (commit `ce4d8dc`,
  `Airs/BusEmission.lean`). Ships
  `bus_effect_matches_sail_load_rrrw` (LD: `[rs1_read, mem_read_8,
  rd_write]`) and `bus_effect_matches_sail_store_rrrw` (SD:
  `[rs1_read, rs2_read, mem_write_8]`). No new axioms; both use only
  `propext`, `Classical.choice`, `Quot.sound`. LD proof reuses
  shape-(a) `write_reg_state_comm` structure; SD expresses the RHS
  in the bus-effect-native `modify (fun s ⇒ { s with mem := … })`
  form, leaving bus-to-Sail translation for the 51-file downstream
  rewire.

- **Track D part 1 — harness preserves T-FIX** (commit `7656a80`,
  `tools/zisk-fv-harness/src/main.rs`). Fixes the previously-noted
  bug where `verify-phase*` regeneration stripped the Phase 4 T-FIX
  edge-case namespaces (`ZeroResult`, `HighLaneOverflow`) from
  `GoldenTraces/Add.lean`. Adds `--multi-fixture` CLI flag (default
  true) + two unit tests that lock the guarantee.

- **A-rewire for all 9 Arith opcodes.** MUL pilot (`b98ff7d`) closed
  the template. Template applied uniformly to the other 8 opcodes
  (`3ebcc80`): MULH, MULHU, MULHSU, MULW, DIV, DIVU, REM, REMU.

  **Decomposition shape.** Each `equiv_<OP>_metaplan` replaces the
  monolithic `h_rd_match` hypothesis with two smaller ones:
  - `h_rd_idx : <op>_input.rd = Transpiler.wrap_to_regidx e2.ptr`
  - `h_rd_val : U64.toBV #v[e2.x0..e2.x7] = <pure-spec product/
    quotient/remainder>`
  Both are downstream-derivable via Phase 4.5 Bridges 1/2/3 + the
  scope-honest arith_table permutation witness (the
  9-opcode→sign-witness mapping).

  **Proof body template** (identical across all 9 opcodes):
  ```
  rw [equiv_<OP>_sail ...]
  symm
  rw [bus_effect_matches_sail_alu_rrw ...]
  simp only [PureSpec.execute_<OP>_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]
  ```

### What was learned

- **Bridge 3 is used by A-rewire indirectly.** `h_rd_val` is the
  hypothesis shape Bridge 3 + `memory_entry_toField_eq_toBV_toNat`
  produce when composed with Arith's packed-correct theorems. The
  caller-facing interface is `h_rd_val` as a direct equation; Bridge
  3 closes that equation under a reasonable hypothesis set (byte
  ranges + no-wrap + arith_table witness). Closing `h_rd_val` from
  strictly the circuit predicates remains the Gap 2 close.

- **Parallel worktree subagents were highly effective.** Tracks C,
  D-part-1, B kicked off in parallel; main session did A-rewire
  pilot + extension. Zero file-level conflicts between agents
  because each track touched a disjoint file set. Tracks B and D2
  still in-flight as of this CLOSED append.

### What shipped (continued — session-2 + post-PARTIAL-CLOSED work)

- **Track B — signed MUL/DIV carry-chain** (commit `6bc6250`).
  `Airs/Arith/CarryChain.lean` gains `arith_mul_signed_carry_identity`
  (+80 lines) and `arith_div_signed_carry_identity` (+62 lines),
  holding over arbitrary sign witnesses `(na, nb, np, nr)` ∈ {0, 1}.
  Per-opcode specializations shipped as `arith_mul_signed_packed_correct`
  (`Airs/Arith/Mul.lean`, +101 lines) and `arith_div_signed_packed_correct`
  (`Airs/Arith/Div.lean`, +87 lines). Closes carry-chain identity
  for all 9 Arith opcode/mode combinations at the named-column level.

- **Track D part 2 — golden-trace coverage** (commits `e9fceec`,
  `7a977a0`, `c582822`). Hand-authored edge fixtures bring every
  opcode to ≥3 scenarios. Final count: **175 scenarios** across 58
  files, **533 total `example : … := by decide` declarations**.
  Fixtures use `namespace` (not `section`) per Phase-4 T-FIX
  convention; `verify-phase*` now preserves them thanks to Track D
  part 1 (`7656a80`).

- **LD pilot — MEM-family rewire template** (commit `2632066`,
  `Equivalence/LoadD.lean`). Decomposes `h_bus_execute_matches_sail`
  into structural bus hypotheses (`h_exec_len`, `h_e*_mult`, `h_m*_*`,
  `h_nextPC_matches`) + decomposed rd-match (`h_rd_zero_iff`,
  `h_rd_idx`, `h_rd_val`). Proof uses `bus_effect_matches_sail_load_rrrw`
  (Track C) + Subtype.ext + explicit `Finset.mem_Icc.mpr` for the
  `Finset.Icc 1 31` index alignment. Validates the MEM-family template.

- **32-file ALU rewire** (8 commits `93134da`, `701eb1b`, `8c0ff24`,
  `f14f1a2`, `57bb579`, `640d36a`, `f7c4b46`, `8e17c88`). Dispatched
  to a worktree subagent that stripped `h_rd_match` from every
  remaining ALU/UTYPE/jump/branch/shift metaplan theorem, landing the
  A-rewire pattern uniformly across:
  - RTYPE add-family (ADD/AND/OR/XOR/SUB), `93134da`.
  - ITYPE bitwise (ADDI/ANDI/ORI/XORI), `701eb1b`.
  - SLT family (SLT/SLTU/SLTI/SLTIU, 4 with nested if), `8c0ff24`.
  - W-family ALU (ADDW/SUBW/ADDIW), `f14f1a2`.
  - Shift family (SLL/SRL/SRA + SLLI/SRLI/SRAI), `57bb579`.
  - W-variant shifts (SLLW/SRLW/SRAW + SLLIW/SRLIW/SRAIW), `640d36a`.
  - UTYPE (LUI, AUIPC — use `h_nextPC_eq`), `f7c4b46`.
  - Jumps (JAL, JALR — compound dite conditions), `8e17c88`.

  After all 8 land: `grep -c '^\s*(h_rd_match :' ZiskFv/ZiskFv/Equivalence/*.lean`
  returns 0 for every file. **All 41 metaplan theorems have
  `h_rd_match` decomposed.**

- **Track F — full docs close** (commit `baada62`). `REPORT.md` §3.1
  rewritten to reflect Arith carry-chain identity closed + `h_rd_match`
  decomposed; §3.3 updated to 58/58 opcodes ≥3 scenarios / 175 total.
  `docs/fv/openvm-fv-parity.md` Gap 2 marked STRUCTURALLY CLOSED
  with Bridge 1/2/3 commit citations. Header status block refreshed.

### What was learned

- **Bridge 3 is used by A-rewire indirectly.** `h_rd_val` is the
  hypothesis shape Bridge 3 + `memory_entry_toField_eq_toBV_toNat`
  produce when composed with Arith's packed-correct theorems. The
  caller-facing interface is `h_rd_val` as a direct equation; Bridge
  3 closes that equation under a reasonable hypothesis set (byte
  ranges + no-wrap + arith_table witness).

- **Parallel worktree subagents were highly effective.** Tracks B, C,
  D-part-1/2, and the 32-file ALU rewire all ran as isolated
  subagents with zero file-level conflicts. Main session did A-rewire
  pilot + Arith extension + LD pilot. Lesson captured: subagent
  prompts must use worktree-relative paths (agents sometimes
  resolved absolute paths to the main repo; no data loss but caused
  merge confusion). Saved as feedback memory.

- **LD pilot pattern generalizes.** The Subtype.ext + explicit
  `Finset.mem_Icc.mpr` construction in `Equivalence/LoadD.lean` is
  the template for the remaining MEM-family rewire. Applying it to
  the other 50 MEM-family theorems is a mechanical fan-out (scoped
  for Phase 5 or a 4.5.1 follow-up).

### What remains — carry-over into Phase 5

- **Gap 1** (Sail input derivation) and **Gap 3** (unwired transpile
  axioms) per `docs/fv/openvm-fv-parity.md` — scoped to Phase 5.
- **MEM-family rewire extension.** LD pilot validates the template;
  applying to LB/LH/LW/LBU/LHU/LWU/SB/SH/SW/SD is mechanical and can
  be folded into Phase 5 Track G concurrently with the
  `chip_bus_hyps_*` work.
- **Arith table-lookup witnesses** (sign-preprocessing, range_cd,
  inv_sum_all_bs). Orthogonal to carry-chain closure; stays deferred
  as scope-honest hypotheses on the `arith_table` permutation
  argument.
