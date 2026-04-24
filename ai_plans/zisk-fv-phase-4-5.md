# Phase 4.5 — Residual closure + openvm-fv structural parity

## Context

Phase 4 closed 2026-04-23 at `a1595bf` on `main`: `lake build` green at
8118 jobs, zero-sorry, 62 axioms (58 transpile + 4 platform + 0
Sail-equivalence), uniformity lint passing, `REPORT.md` shipped. The
project is at a "defensible completion point" — but a parity audit
against our template project [openvm-fv](/home/cody/openvm-fv) surfaces
that zisk-fv's metaplan theorems are **structurally weaker** than
openvm-fv's on three axes:

- **Gap 1 — Sail input state derivation.** openvm-fv derives
  `read_xreg rs1/rs2 state = ok ...` and `Sail.readReg Register.PC state
  = ok ...` internally via `chip_bus_hypotheses`; we parameterize on
  `h_input_r1`/`h_input_r2`/`h_input_pc`/`h_input_rd`.
- **Gap 2 — `h_rd_match` derivation.** openvm-fv derives the
  bus-byte ↔ pure-spec rd-value alignment via transpile-axiom unfolding;
  we parameterize.
- **Gap 3 — Unwired transpile axioms.** Our 58 `transpile_<OP>` axioms
  sit declared-and-unused in `Fundamentals/Transpiler.lean`; openvm-fv's
  analogue (`transpile_of_bus_wellformedness`) is consumed in proofs.

See `docs/fv/openvm-fv-parity.md` for the full side-by-side. Phase 4.5
closes these three gaps plus the four items Phase 4 explicitly deferred
(Package C Steps 3+4, signed MUL/DIV, LD/SD bus shapes, golden-trace
matrix, `just verify-phase4` target).

**End state after Phase 4.5:** the 41 metaplan theorems carry the same
parameter surface as openvm-fv's RISC-V equivalence theorems
(AIR mirror + `h_circuit` + bus-wellformedness + bus-effect precondition,
**nothing else**). Trust-base count **62 axioms genuinely load-bearing**
(both the 58 transpile contracts and the 4 platform axioms get consumed
in proofs). 58/58 RV64IM opcodes × 3 golden-trace fixtures. `just
verify-phase4` reproducibility gate landed. `REPORT.md` §3.1 Arith
caveat retired; §3.3 fixture matrix updated.

## Scope — eight tracks

### Track A — Package C closure (Arith bridges, unsigned) — Gap 2 part 1

Drops `h_rd_match` from the 9 Arith `equiv_<OP>_metaplan` theorems
(MUL, MULH, MULHU, MULHSU, MULW, DIV, DIVU, REM, REMU) under unsigned
mode witnesses. Three bridges per `docs/fv/package-c-residuals.md`:

- **Bridge 1 — constraint-46 normalization.** Under MUL-unsigned mode
  (`sext = 0, m32 = 0, main_mul = 1, main_div = 0, div = 0`), constraint
  46 collapses `bus_res1` to `c[2] + c[3]*65536`, giving `arith_c_packed
  = c_chunks_packed`. Mirror for DIV (`main_div = 1`) yields
  `a_chunks_packed_div` (quotient); for REM (secondary) yields
  `d_chunks_packed_div`. **New file** `ZiskFv/ZiskFv/Airs/Arith/Bridge1.lean`,
  ~80 lines.

- **Bridge 2 — Main ↔ Arith operand composition.** The bus-match identity
  pins `m.a_0 = v.a_0 + v.a_1*65536`, `m.b_0 = v.b_0 + v.b_1*65536`, etc.
  Composed with Bridge 1 and `arith_mul_unsigned_packed_correct`, proves
  `main_a_packed * main_b_packed = main_c_packed + main_d_packed * 2^64`
  as a field equation. **New file** `ZiskFv/ZiskFv/Spec/MulField.lean`,
  ~120 lines.

- **Bridge 3 — field → `BitVec 64` lift.** The hardest piece. Three
  sub-lemmas in **new file** `ZiskFv/ZiskFv/Fundamentals/PackedBitVec.lean`:
  1. `u64_toBV_of_bytes`: `U64.toBV #v[x0..x7] = BitVec.ofNat 64 (Σ x_i * 2^(8i))`.
  2. `fgl_packed_to_bitvec`: with chunk bounds `< 2^16`, the packed FGL value has `.val < 2^64` and equals `BitVec.ofNat 64 (packed.val)` via the chunk concatenation.
  3. `arith_c_equals_product_bitvec`: composes the above to show Arith's `c_chunks_packed` equals `BitVec 64 (r1_val * r2_val)` (low 64 bits).
  ~350 lines. No in-repo precedent; openvm-fv has the RV32 analogue at
  `OpenvmFv/Fundamentals/` but read-only.

- **Rewiring.** 9 `equiv_<OP>_metaplan` theorems lose `h_rd_match` from
  their signatures; proof body discharges via bridge composition.

**Effort:** ~550 lines new + ~200 lines rewiring. 3–4 days.

### Track B — Signed MUL/DIV carry-chain closure

Extends the unsigned carry-chain identity to `(na, nb) ∈ {0,1}²` with
per-quadrant sign-adjustment through `np`/`nr` witnesses. Authors
`arith_mul_signed_packed_correct` and `arith_div_signed_packed_correct`
in `Airs/Arith/{Mul,Div}.lean`, reusing the constraint 6/7/8 skeleton
from Track A Bridge 1.

Closes signed-mode carry-chain polynomial identity (not the
`arith_table` permutation-argument dependency — that remains a
scope-honest narrow structural parameter per Phase 4 § out-of-scope).

**Effort:** ~400 lines. 2–3 days. Blocked on Track A Bridge 1.

### Track C — Shape (d) and (e) LD/SD bus-emission lemmas

Per `Airs/BusEmission.lean:309-323`, Shape (d) (LD) and Shape (e) (SD)
bus-emission reductions were deferred. 51 MEM-family metaplan theorems
(LD, SD, LB, LBU, LH, LHU, LW, LWU, SB, SH, SW, and their unsigned
variants) currently parameterize on the monolithic
`h_bus_execute_matches_sail` rather than the decomposed hypothesis set.

Two new lemmas paired with `bus_effect_matches_sail_alu_rrw` /
`bus_effect_matches_sail_jump_rrw`:

- `bus_effect_matches_sail_load_rrrw` — Shape (d): exec reg-read rs1,
  mem-read 8 bytes (little-endian), reg-write rd.
- `bus_effect_matches_sail_store_rrrw` — Shape (e): exec reg-read rs1,
  reg-read rs2, mem-write 8 bytes.

Mirrors shape-(a) closure pattern (`register_type_pc_equiv`, foldl
unfolding, commutation of `writeReg nextPC` past memory ops). Memory
helpers (`vmem_read_aligned_equiv` / `vmem_write_aligned_equiv`) need
authoring or sourcing from LeanRV64D — **risk: may require a narrow
structural axiom** if absent (scope-honest if taken, documented in
trusted-base.md).

Rewire 51 MEM-family Equivalence files.

**Effort:** ~700 lines (two shape lemmas ~300 each + rewiring). 2–3 days.
Parallelizable with A, B.

### Track D — Golden-trace matrix expansion

Achieve 58 × 3 = 174 fixtures. Current: 6 × 3 (ADD/SUB/AND/SLT/MUL/LW)
+ 52 × 1 = 70 fixtures. Need ~104 new fixtures.

- Extend `tools/zisk-fv-harness/src/main.rs` to emit 2–3 variants per
  opcode (edge cases: zero, max, overflow-boundary, sign-boundary,
  unaligned).
- Extend Lean fixture template per pattern at `GoldenTraces/{ADD,SUB,MUL}.lean`.
- Generate and commit per-family batches for reviewability.

**Effort:** ½ day harness + 1–2 days generation. Parallel with proof tracks.

### Track E — `just verify-phase4` target

Bundle V1–V14 gates into a justfile target. Mirror `verify-phase2`:
`lake build`, zero-sorry grep, uniformity lint, fixture count, `#print
axioms` on representative metaplan theorems, transpile-axiom
consumption sanity check.

**Effort:** ~1 hour at end.

### Track F — Memory + CLOSED + REPORT deltas

- Append **Phase 4.5 CLOSED** section to this file mirroring Phase 4 shape.
- Update `project_phase_status.md` in memory.
- `REPORT.md` §3.1: strike Arith-carry-chain caveat (Package C closed).
- `REPORT.md` §3.3: update fixture matrix to "full 174 populated".
- `REPORT.md` §2: state that all 58 transpile axioms are load-bearing.
- Retire or strikethrough `docs/fv/package-c-residuals.md`.
- Update `docs/fv/trusted-base.md` with Phase 4.5 history entry.
- Update `docs/fv/openvm-fv-parity.md` marking gaps closed.
- Strip Phase-4-deferred commentary in `Airs/BusEmission.lean`,
  `Airs/Arith/{Mul,Div}.lean`, individual Equivalence files.

**Effort:** ½ day at end.

### Track G — `chip_bus_hypotheses`-analogue lemmas — Gap 1

**NEW (openvm-fv parity).** For each bus-shape family, author a
lemma that derives the Sail input-state facts from the
bus-wellformedness predicate + the row's transpile-axiom application.

Five lemmas, one per shape family, in **new file**
`ZiskFv/ZiskFv/Airs/BusHypotheses.lean` (or add to `BusEmission.lean`):

- `chip_bus_hyps_alu_rrw` — ALU shape-(a): derives `read_xreg rs1 =
  ok (U64.toBV bytes₁)`, `read_xreg rs2 = ok (U64.toBV bytes₂)`,
  `Sail.readReg Register.PC = ok (BitVec.ofNat 64 pc)`. Consumed by
  all ALU/arith metaplan theorems.
- `chip_bus_hyps_branch_rrw` — branch shape-(b).
- `chip_bus_hyps_jump_rrw` — jump shape-(c).
- `chip_bus_hyps_load_rrrw` — LD shape-(d).
- `chip_bus_hyps_store_rrrw` — SD shape-(e).

Each ~150 lines. Proof structure mirrors openvm-fv's
`Equivalence/Mul.lean:492-537` `chip_bus_hypotheses`: unfolds
`bus_effect`, applies `transpile_<OP>` to discharge the
ptr/register-index alignment, closes the state-read equalities by
bus-match.

**Rewiring.** 41 metaplan theorems drop `h_input_r1`, `h_input_r2`,
`h_input_pc`, `h_input_rd` parameters; the proof body invokes the
appropriate `chip_bus_hyps_*` lemma.

**Depends on Track H** (transpile axioms must be wired before they
can be consumed).

**Effort:** ~750 lines lemmas + ~200 lines rewiring. 3–4 days.

### Track H — Transpile axiom wiring — Gap 3

**NEW (openvm-fv parity).** Make the 58 `transpile_<OP>` axioms
actually load-bearing.

Each axiom is an existential of the form

```
axiom transpile_<OP> : ∀ (RISC-V row fields), ∃ (Zisk row fields),
    <Main-AIR row has these columns set>
```

Phase 4.5 wires these into the per-opcode proof pipeline:

1. Each `<op>_circuit_holds` predicate (or a new
   `<op>_row_from_transpile` predicate) references the
   `transpile_<OP>`-witnessed row fields. Current structural
   parameters (`h_main_a`, `h_main_b`, Main lane values, rd_ptr
   alignment) get derived from the axiom's existential.

2. In each metaplan theorem proof, invoke `have h_transpile :=
   transpile_<OP> ...; obtain ⟨zisk_row, h_row⟩ := h_transpile`, and
   discharge the row-alignment hypotheses that are currently
   parameters.

Opcode-by-opcode rewiring: each proof has ~20 lines of discharge
work per transpile axiom; many opcodes share discharge skeletons
(RTYPE family, ITYPE family, RTYPEW, UTYPE, branches, loads, stores,
MUL family, DIV family). Templating via `Tactics/` macros reduces
total to ~30% of the naive count.

**Effort:** ~15 days naive × 0.3 templating factor = ~5 days, or
~2 days with subagent fan-out per family.

**Enables Track G** (Sail input derivation depends on
transpile-axiom row-witness consumption).

**Enables full Gap 2 closure** (Package C Bridge 3's BitVec lift uses
transpile-axiom bytes alignment).

## Execution order (eight-track Gantt)

**Critical path:** H → G → metaplan rewirings. Other tracks fan out.

### Week 1 — foundation tracks
- **Day 0 (pilot):** A1 (Bridge 1) serial in main session. Small,
  validates extraction navigation.
- **Days 1–2:** A2, A3 (Bridges 2+3) serial in main session (Bridge 3
  is deep work, main focus). H fan-out in parallel subagent batch 1
  (RTYPE family: ADD/SUB/AND/OR/XOR/SLT/SLTU — 7 axioms). C fan-out
  in parallel subagent.
- **Days 3–4:** A rewiring (drops `h_rd_match` from 9 Arith theorems).
  H fan-out batch 2 (RTYPEW, ITYPE, UTYPE, branch, jump: 16 axioms)
  in parallel subagent. B starts after A1 lands.
- **Day 5:** H fan-out batch 3 (MUL, DIV, Load, Store, MULW, DIVU:
  19 axioms) in parallel subagent. D starts (harness extension).

### Week 2 — structural parity + expansion
- **Days 6–7:** G starts (5 `chip_bus_hyps_*` lemmas) serial in main
  session after H batch-1 stabilizes. D continues (fixture generation).
- **Days 8–9:** G rewiring — 41 metaplan theorems drop `h_input_*`
  parameters. Parallel worktree subagent per shape family (ALU, branch,
  jump, load, store). B completes.
- **Day 10:** E (justfile), F (memory/REPORT/CLOSED), V1–V14 gate runs.

**Wall-clock estimate:** 10 working days (~2 weeks) with aggressive
subagent fan-out. Solo execution: 3 weeks.

### Dependency graph

```
A1 ─── A2 ─── A3 ─── A-rewire (drops h_rd_match)
                          │
                          └──── F (REPORT updates)
A1 ─── B
H-batch-1 ─── H-batch-2 ─── H-batch-3 ─── G ─── G-rewire (drops h_input_*)
                                          │
                                          └──── F (REPORT updates)
C (independent) ──────────────────────────┴──── F
D (independent, harness + fixtures) ──────┴──── F
                                              │
                                              E (justfile) ── V1–V14 gates
```

**Parallelism model** (Phase 3C pattern): A runs in main session (deep
proof); B, C, D, H fan out via parallel worktree subagents once A1
ships. G waits for H batch-1 + A3.

## Critical files

**Read-only (must not mutate):**
- `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean` — axioms themselves
  stay as-is (only their *consumption* changes).
- `ZiskFv/ZiskFv/Extraction/*.lean` — auto-generated.
- `ZiskFv/ZiskFv/Airs/Main.lean`, `OperationBus.lean`.
- `ZiskFv/ZiskFv/Fundamentals/Execution.lean`.

**New files:**
- `ZiskFv/ZiskFv/Airs/Arith/Bridge1.lean` — constraint-46 normalization.
- `ZiskFv/ZiskFv/Spec/MulField.lean` — Main ↔ Arith field composition.
- `ZiskFv/ZiskFv/Fundamentals/PackedBitVec.lean` — U64.toBV + field→BitVec.
- `ZiskFv/ZiskFv/Airs/BusHypotheses.lean` — the five `chip_bus_hyps_*` lemmas.
- Possibly `ZiskFv/ZiskFv/Tactics/TranspileWiring.lean` — templating
  macros for Track H discharge skeletons.
- `ai_plans/zisk-fv-phase-4-5.md` — this file, with CLOSED section on completion.

**Edited:**
- `ZiskFv/ZiskFv/Airs/Arith/{Mul,Div}.lean` — signed-mode specializations.
- `ZiskFv/ZiskFv/Airs/BusEmission.lean` — Shape (d/e) lemmas.
- `ZiskFv/ZiskFv/Equivalence/*.lean` — all 41 metaplan theorems get:
  (i) `h_rd_match` dropped (9 Arith); (ii) `h_input_*` dropped (41);
  (iii) optional: transpile-axiom consumption in `h_circuit` discharge.
- `ZiskFv/ZiskFv/GoldenTraces/*.lean` — +2 fixtures per under-covered opcode.
- `tools/zisk-fv-harness/src/main.rs` — multi-fixture generation.
- `REPORT.md` — §2 and §3 updates.
- `docs/fv/trusted-base.md` — Phase 4.5 history; no axiom additions (base
  unchanged unless Track C's vmem axiom proves necessary).
- `docs/fv/openvm-fv-parity.md` — mark gaps closed.
- `docs/fv/package-c-residuals.md` — retire or mark closed.
- `justfile` — `verify-phase4` target.

## Known fragility

1. **Bridge 3 no in-repo precedent.** `U64.toBV` lemmas must be authored
   fresh. openvm-fv has `U32.toBV` analogue; RV64/8-byte variant is
   ~60% larger. Mitigation: budget +40% on A3 estimate; pilot on MUL
   first before fan-out.

2. **Chunk-bound witnesses.** Bridge 3 needs `c_i.val < 2^16` from
   the 16-bit range-check tables. These are direct column properties
   exposed via `Valid_ArithMul` structure fields (not lookup-argument
   dependent). Confirm by inspection.

3. **Signed-mode `linear_combination` complexity (Track B).** 8-chunk
   × 4-quadrant case-split. Factor `fab`/`na_fb`/`nb_fa` substitution
   into per-quadrant lemma; each quadrant reuses skeleton.

4. **Shape (d/e) vmem axiom (Track C).** If `vmem_read_aligned_equiv`
   doesn't exist in LeanRV64D, narrow structural axiom acceptable.
   Audit LeanRV64D memory-model first.

5. **Ring-atom trap (Phase 1).** All new proofs must write `65536^k`
   in factored `65536 * 65536 * ...` form.

6. **Transpile-axiom existentials (Track H).** 58 axioms have
   per-opcode existential shape; some opcodes (e.g. RTYPE family) have
   nearly identical discharge skeletons while others (MUL with
   Arith-row-witness, JALR with PC-next-arithmetic) are bespoke.
   Mitigation: cluster opcodes by discharge shape, template shared
   discharge, apply templated version per opcode.

7. **G's rd-ptr derivation (openvm-fv parity).** `chip_bus_hypotheses`
   in openvm-fv derives `wrap_to_regidx rd_ptr ≠ 0` via `rd_neq_0`
   lemma using transpile-axiom rd-bound. Same pattern needed in
   `chip_bus_hyps_*`. Dependency on Track H's output is critical.

8. **Rewire-at-scale for Tracks G, H, C.** 41 + 41 + 51 edits across
   ~80 unique Equivalence files. Mitigation: per-family subagent
   dispatch; per-family commit batches; uniformity lint after each
   batch.

## Verification gates (V1–V14)

- **V1.** `lake build` green. Expected ~9000 jobs (8118 + ~500
  Package C + ~50 signed + ~150 shape + ~300 fixtures + ~750 G + Track H
  rewiring).
- **V2.** `just verify-phase4` exits 0.
- **V3.** Zero-sorry across `ZiskFv/ZiskFv/`.
- **V4.** 9 Arith `equiv_<OP>_metaplan` theorems have no `h_rd_match` in
  signature.
- **V5.** Trust-base count stays at **62 axioms** (63 if Track C needs
  vmem axiom — documented).
- **V6.** 51 MEM-family metaplan theorems use shape-(d/e)-decomposed
  hypotheses.
- **V7.** Golden-trace fixture count = 174.
- **V8.** Uniformity lint passes.
- **V9.** Signed MUL/DIV carry-chain lemmas exist; `#print axioms`
  shows only transpile + platform + optional vmem.
- **V10.** `REPORT.md` §3.1 rewritten; §3.3 reflects full matrix;
  §2 reflects load-bearing transpile axioms.
- **V11.** Phase 4.5 CLOSED section appended to this file.
- **V12.** All 41 metaplan theorems have no `h_input_r1`/`h_input_r2`/
  `h_input_pc`/`h_input_rd` parameters. Lint: `grep -c 'h_input_r1'
  Equivalence/` = 0 on metaplan theorems (circuit-level `equiv_<OP>`
  may retain input parameters — only the metaplan form drops them).
- **V13.** All 58 `transpile_<OP>` axioms have at least one
  proof-level consumer. Lint: script counts non-docstring references per
  axiom; all > 0.
- **V14.** Parity audit. Compare parameter list on
  `equiv_MUL_metaplan` (zisk-fv) to `mul_spec` (openvm-fv); modulo
  decomposition preference the surfaces should match. Manual sign-off.

## Out-of-scope (explicit)

1. **Arith table-lookup witnesses** (sign-preprocessing, range_cd,
   inv_sum_all_bs per REPORT §3.2). Orthogonal to carry-chain.
2. **Non-Arith `h_bus_execute_matches_sail` discharge** beyond shape
   (a/c/d/e). Any unrepresented shape stays parameterized.
3. **Sail spec trusted** — inherited.
4. **Zicclsm, precompiles, ZisK custom ops** — out of scope per CLAUDE.md.
5. **Rust-side transpile-axiom audit** — the Rust transpiler
   (`riscv2zisk_context.rs`) remains trusted. Lean-side closure of
   the axioms' *consumption* is Phase 4.5; *retirement* via Rust
   verification is a separate project.

## Kickoff

When the user prompts Phase 4.5 execution:

1. **Pre-flight read** (~45 min):
   - `docs/fv/package-c-residuals.md`, `docs/fv/openvm-fv-parity.md`.
   - `Airs/Arith/{CarryChain,Mul,Div}.lean` current state.
   - `Extraction/Arith.lean` constraint 46.
   - `Airs/BusEmission.lean` — especially `bus_effect_matches_sail_alu_rrw`
     shape-(a) closure as the template for shapes (d/e) and for the
     `chip_bus_hyps_*` lemmas.
   - `/home/cody/openvm-fv/OpenvmFv/Equivalence/Mul.lean:468-600`
     (`rd_neq_0`, `chip_bus_hypotheses`, RISC-V equivalence) — the
     template for Track G and Track H wiring.
   - `Fundamentals/Interaction.lean` — `U64.toBV` definition.
   - Sample of `Equivalence/Add.lean:188-222` to see the current
     metaplan theorem hypothesis surface.

2. **Write ≤200-word execution plan for the pilot track** — recommended
   pilot: **A1 (Bridge 1) + one H-rewiring opcode** (e.g., ADD). This
   validates both Package C's extraction navigation AND the transpile-
   axiom wiring pattern end-to-end before parallel fan-out.

3. **Execute A1 + pilot H-ADD serially** in main session.

4. **Fan-out:** [A2, A3, B, C, D, H-batch-2, H-batch-3] via parallel
   worktree subagents. H batches sized by opcode-family cluster.

5. **Track G** starts after H-batch-1 + A3 land.

6. **After all proof tracks green:** E (justfile), F (REPORT + CLOSED
   section + memory). V1–V14 gates.

7. **On pass:** append Phase 4.5 CLOSED section to this file mirroring
   Phase 4's CLOSED shape.

## Verification (end-to-end how-to)

```bash
cd /home/cody/zisk-fv
cd ZiskFv && lake build                              # V1: ~9000 jobs
cd .. && just verify-phase4                          # V2: bundled V1-V14
git grep -n 'sorry' ZiskFv/ZiskFv/                   # V3: empty
grep -c 'h_rd_match' ZiskFv/ZiskFv/Equivalence/{Mul,MulH,MulHU,MulHSU,MulW,Div,Divu,Rem,Remu}.lean  # V4: 0
# V5: count axioms in trusted-base.md (expect 62 or 63)
grep -c 'h_bus_execute_matches_sail' ZiskFv/ZiskFv/Equivalence/*.lean  # V6: ≤5
# V7: count 'example' in GoldenTraces/*.lean (expect ≥174)
bash tools/zisk-fv-lint/uniformity-lint.sh           # V8
# V9: `#print axioms` on signed theorems
# V10: diff REPORT.md §3 against expected updates
# V11: verify CLOSED section exists in this file
# V12: grep -c 'h_input_r1' for each metaplan theorem (expect 0)
# V13: transpile-axiom consumer count script (each > 0)
# V14: side-by-side with openvm-fv `mul_spec` parameter list
```

**End state.** Parameter surface of every `equiv_<OP>_metaplan` theorem
matches openvm-fv's RISC-V-equivalence theorem modulo bundling
preferences. Trust base **62 axioms, every one load-bearing**.
`REPORT.md` §3.1 Arith-carry-chain caveat retired.
`docs/fv/openvm-fv-parity.md` marked "all gaps closed." Project at full
structural parity with the openvm-fv template.
