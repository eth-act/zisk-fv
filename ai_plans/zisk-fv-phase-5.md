# Phase 5 — openvm-fv structural parity (transpile-axiom refactor + Sail-input derivation)

## Context

Phase 4.5 (`ai_plans/zisk-fv-phase-4-5.md`) closes Gap 2 (`h_rd_match`
derivation) for 9 Arith opcodes and ships the Phase 4 deferred
completeness items. It explicitly leaves **Gap 1** (Sail input state
derivation) and **Gap 3** (unwired transpile axioms) open — they
require a ~2500-4000-line transpile-axiom refactor that's too big for
Phase 4.5's scope.

Phase 5 closes both. End state: every `equiv_<OP>_metaplan` theorem's
parameter list matches openvm-fv's RISC-V equivalence theorems modulo
bundling preferences. The 58 `transpile_<OP>` axioms become genuinely
load-bearing (every one has at least one proof-level consumer).

Per the parity audit `docs/fv/openvm-fv-parity.md`:
- openvm-fv's `transpile_of_bus_wellformedness` is consumed in proofs
  to discharge per-row column equalities. Ours currently sit declared
  and unused.
- openvm-fv's `chip_bus_hypotheses` derives `read_xreg rs1/rs2 state = ok …`
  and `Sail.readReg Register.PC state = ok …` from bus-wellformedness +
  transpile-axiom consumption. We parameterize on them.

The root cause is axiom shape. Our `transpile_<OP>` axioms have shape

```
axiom transpile_<OP> : ∀ state, ∃ row : ZiskInstructionRow, <field values>
```

The abstract `ZiskInstructionRow` has no connection to the concrete
`Valid_Main` row at a specific index. Phase 5 restructures this so the
axiom directly pins the Main AIR row's columns given mode witnesses.

## Scope — two tracks

### Track H — Transpile-axiom refactor (the big mechanical refactor)

Restate all 58 `transpile_<OP>` axioms in direct `Valid_Main`-form:

```
axiom transpile_<OP> :
  ∀ {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (state : RV64State)
    (rs1 rs2 rd : Fin 32),
    m.is_external_op r_main = 1 →
    m.op r_main = OP_<OP> →
    <other mode witness premises> →
    m.a_0 r_main = lane_lo (state.xreg rs1) ∧
    m.a_1 r_main = lane_hi (state.xreg rs1) ∧
    m.b_0 r_main = lane_lo (state.xreg rs2) ∧
    m.b_1 r_main = lane_hi (state.xreg rs2) ∧
    <per-opcode column equalities>
```

The signature varies per opcode family:
- **RTYPE** (ADD/SUB/AND/OR/XOR/SLT/SLTU/SLL/SRL/SRA) — same 2-lane
  a/b from `xreg rs1`/`xreg rs2`.
- **ITYPE** (ADDI/ANDI/ORI/XORI/SLTI/SLTIU/SLLI/SRLI/SRAI) — `a` from
  `xreg rs1`, `b` from immediate.
- **RTYPEW** (ADDW/SUBW/SLLW/SRLW/SRAW) — 32-bit width, `m32 = 1`.
- **ITYPEW** (ADDIW/SLLIW/SRLIW/SRAIW) — 32-bit + immediate.
- **UTYPE** (LUI/AUIPC) — no source registers; `imm`/`pc`-derived.
- **Branch** (BEQ/BNE/BLT/BGE/BLTU/BGEU) — 2-lane a/b + `jmp_offset`
  immediate.
- **Jump** (JAL/JALR) — `set_pc`/`store_pc` semantics.
- **Load** (LB/LH/LW/LBU/LHU/LWU/LD) — `a` from `xreg rs1`, `b` from
  memory (post-load value).
- **Store** (SB/SH/SW/SD) — 2 source operands, memory-write.
- **MUL family** (MUL/MULH/MULHU/MULHSU/MULW) — Arith-bus-emission,
  Main's `c` tied to Arith's packed result.
- **DIV family** (DIV/DIVU/REM/REMU) — similar to MUL with Arith
  remainder/quotient routing.

**Per-axiom work.** For each opcode:

1. Draft the new axiom statement referring to `Valid_Main` columns
   (~30-50 lines). Verify fidelity against `riscv2zisk_context.rs`
   (the Rust transpiler source — each axiom represents one Rust arm).
2. Update the circuit-level `equiv_<OP>` and metaplan theorem
   consumers to invoke the new axiom, dropping `h_main_a` / `h_main_b` /
   similar structural parameters (~10-15 lines per consumer).

**Templating opportunity.** Opcodes within a family share an axiom
skeleton (same premise shape, same conclusion shape modulo opcode
literal). A Lean macro at `Tactics/TranspileAxiomMacro.lean` could
factor out per-family axiom generation — ~1 day of macro authoring
then ~1 axiom per ~10 lines. Reduces total ~3000 lines → ~1500 lines.

**Subagent fan-out.** Split by family: one subagent per family (10-11
subagents), each restating ~5-7 axioms + updating ~5-7 consumers.
Worktree-isolated per Phase 3C pattern. Wall-clock ~1 week with
parallelism vs ~2 weeks solo.

**Effort:** ~2500-4000 lines total (3000 naive, 1500 with macro templating).

**Verification:** `#print axioms equiv_<OP>_metaplan` for each opcode
must show the new-form `transpile_<OP>` as a dependency. Before Track H
no metaplan theorem depends on any `transpile_<OP>`; after Track H
every metaplan theorem depends on its transpile axiom.

### Track G — `chip_bus_hypotheses`-analogue lemmas (Gap 1 closure)

**Depends on Track H** (consumes the restated transpile axioms).

For each bus-shape family, author a lemma deriving the Sail input-state
facts from bus-wellformedness + the row's transpile-axiom application.

Five lemmas in new file `ZiskFv/ZiskFv/Airs/BusHypotheses.lean`:

- `chip_bus_hyps_alu_rrw` — ALU shape-(a): derives
  `read_xreg rs1 state = ok (U64.toBV bytes₁) state`,
  `read_xreg rs2 state = ok (U64.toBV bytes₂) state`,
  `Sail.readReg Register.PC state = ok (BitVec.ofNat 64 pc) state`.
  Consumed by all ALU/Arith metaplan theorems (~35 of 41 total).
- `chip_bus_hyps_branch_rrw` — branch shape-(b).
- `chip_bus_hyps_jump_rrw` — jump shape-(c).
- `chip_bus_hyps_load_rrrw` — LD shape-(d). Consumes Phase 4.5 Track C's
  `bus_effect_matches_sail_load_rrrw`.
- `chip_bus_hyps_store_rrrw` — SD shape-(e). Consumes Phase 4.5 Track C's
  `bus_effect_matches_sail_store_rrrw`.

Each ~150 lines. Proof structure mirrors openvm-fv's
`Equivalence/Mul.lean:492-537` `chip_bus_hypotheses`: unfolds
`bus_effect`, applies new-form `transpile_<OP>` to discharge
ptr/register-index alignment, closes state-read equalities via
bus-match.

**Rewiring.** All 41 metaplan theorems drop `h_input_r1`, `h_input_r2`,
`h_input_pc`, `h_input_rd` parameters. Each theorem's proof invokes the
appropriate `chip_bus_hyps_*` lemma.

**Effort:** ~750 lines lemmas + ~200 lines rewiring. 3-4 days serial,
or 1-2 days with subagent parallelism per shape family.

## Execution order

Two-track Gantt. H precedes G; within H, parallelism per opcode family.

### Week 1 — Track H (transpile-axiom refactor)
- **Day 0:** Author macro at `Tactics/TranspileAxiomMacro.lean` (optional optimization).
- **Day 1:** Pilot — restate `transpile_ADD` and update `equiv_ADD`/`equiv_ADD_metaplan`. Validates the per-axiom shape end-to-end.
- **Days 2-5:** Fan-out via parallel worktree subagents, one per opcode family:
  - RTYPE subagent: ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA (10 axioms)
  - ITYPE subagent: ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLLI, SRLI, SRAI (9 axioms)
  - RTYPEW subagent: ADDW, SUBW, SLLW, SRLW, SRAW (5 axioms)
  - ITYPEW subagent: ADDIW, SLLIW, SRLIW, SRAIW (4 axioms)
  - UTYPE subagent: LUI, AUIPC (2 axioms)
  - Branch subagent: BEQ, BNE, BLT, BGE, BLTU, BGEU (6 axioms)
  - Jump subagent: JAL, JALR (2 axioms)
  - Load subagent: LB, LH, LW, LBU, LHU, LWU, LD (7 axioms)
  - Store subagent: SB, SH, SW, SD (4 axioms)
  - MUL subagent: MUL, MULH, MULHU, MULHSU, MULW (5 axioms)
  - DIV subagent: DIV, DIVU, REM, REMU (4 axioms)

  Per subagent: draft axioms + update consumer signatures + local build green.
  Total: ~58 axioms / 11 subagents.

- **Day 6:** Merge subagent branches. Full build. V13 (every transpile axiom consumed).

### Week 2 — Track G (chip_bus_hypotheses) + rewiring
- **Days 1-3:** Author 5 `chip_bus_hyps_*` lemmas serial in main session. Uses Week-1-shipped transpile axioms.
- **Days 3-5:** Fan-out metaplan-theorem rewiring via worktree subagents per shape family: 41 theorems drop `h_input_*` parameters.
- **Day 6:** Final build. V12 (no `h_input_*` on metaplan theorems).

### Week 3 — Verification + CLOSED
- Full `lake build` + all gates V1–V14 (including parity V14: side-by-side with openvm-fv `mul_spec`).
- Append **Phase 5 CLOSED** section.
- Update `REPORT.md` §2 (transpile axioms load-bearing); §3 (structural hypotheses discharged).
- Mark `docs/fv/openvm-fv-parity.md` as "all gaps closed."
- Update memory `project_phase_status.md`.

**Wall-clock:** ~2-3 weeks with aggressive subagent parallelism; ~4-6 weeks solo.

## Critical files

**New:**
- `ZiskFv/ZiskFv/Tactics/TranspileAxiomMacro.lean` — optional templating macro for per-family axiom generation.
- `ZiskFv/ZiskFv/Airs/BusHypotheses.lean` — the 5 `chip_bus_hyps_*` lemmas.

**Heavily edited:**
- `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean` — all 58 axioms restated.
- `ZiskFv/ZiskFv/Equivalence/*.lean` — all 41 metaplan theorems drop `h_input_*`; consumer updates for restated axioms.
- `ZiskFv/ZiskFv/Spec/*.lean` — consumer signature updates where `h_main_a`/`h_main_b` patterns appear.

**Documentation updates:**
- `REPORT.md` — §2 (axiom load-bearing), §3 (parity).
- `docs/fv/openvm-fv-parity.md` — "all gaps closed."
- `docs/fv/trusted-base.md` — Phase 5 history entry (no axiom count change; just shape change).

## Known fragility

1. **Per-axiom fidelity audit.** Restating 58 axioms requires per-opcode
   verification against `riscv2zisk_context.rs`. A wrong axiom is a
   trust-base break. Mitigation: for each restatement, quote the Rust
   source arm in a comment; mechanical review sign-off per opcode family.

2. **Macro templating correctness.** If we use the macro at
   `Tactics/TranspileAxiomMacro.lean`, the macro itself becomes a trust
   surface — a bug in the macro could silently mis-generate 58 axioms.
   Mitigation: pilot the macro on a small family first (e.g. RTYPEW,
   5 axioms) and hand-audit the generated axioms before fanning out.

3. **Consumer signature churn.** Metaplan theorems span 41 files; each
   loses ~4 parameters and gains ~1 transpile-axiom consumer invocation.
   Mitigation: per-family subagent batches with local build gates; lint
   script post-merge asserting expected parameter drops.

4. **Ring-atom trap.** All new proofs respect factored-form radix powers
   per Phase 1 lesson.

5. **Depends on Phase 4.5 Track C.** Track G's `chip_bus_hyps_load_rrrw`
   and `_store_rrrw` lemmas consume `bus_effect_matches_sail_{load,store}_rrrw`
   from Phase 4.5 Track C. Phase 5 blocked on Phase 4.5 closure for LD/SD
   opcodes — but can proceed for non-LD/SD opcodes in parallel.

## Verification gates (V12–V14, extending Phase 4.5's V1–V11)

- **V12.** All 41 metaplan theorems have no `h_input_r1`/`h_input_r2`/
  `h_input_pc`/`h_input_rd` parameters. Lint: `grep -c 'h_input_r1'
  ZiskFv/ZiskFv/Equivalence/*.lean` finds zero on metaplan theorems
  (circuit-level `equiv_<OP>` may still take input parameters).
- **V13.** Every `transpile_<OP>` axiom has ≥1 proof-level consumer.
  Lint script: for each of 58 axioms, count non-docstring references.
  All counts > 0.
- **V14.** Parameter-list parity check. Manual sign-off that
  `equiv_MUL_metaplan` (and representative branch/jump/load metaplan
  theorems) carry the same parameter surface as openvm-fv's
  `mul_spec` / `jal_spec` / etc.

## Out-of-scope (explicit — stays deferred)

- **Arith table-lookup witnesses** (sign-preprocessing, range_cd,
  inv_sum_all_bs). Orthogonal to carry-chain correctness.
- **Zicclsm, precompiles, ZisK custom ops.**
- **Sail spec** (trusted input).
- **Rust-side transpile-axiom proof** (the Rust transpiler itself
  remains trusted; Phase 5 closes the Lean-side consumption, not the
  Rust-side derivation).

## Kickoff

When Phase 4.5 closes and the user prompts Phase 5:

1. **Pre-flight read** (~30 min):
   - `ai_plans/zisk-fv-phase-4-5.md` CLOSED section.
   - `docs/fv/openvm-fv-parity.md`.
   - `/home/cody/openvm-fv/OpenvmFv/Equivalence/Mul.lean:468-600` (chip_bus_hypotheses template).
   - `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean:41-300` (current axiom shape sample).
   - `ZiskFv/ZiskFv/Equivalence/Add.lean:40-220` (current consumer shape).

2. **Write ≤200-word execution plan for the Track H pilot** — recommended pilot: **`transpile_ADD` restatement + `equiv_ADD`/`equiv_ADD_metaplan` update**. Validates the per-axiom pattern before fan-out.

3. **Execute Track H pilot serially**, then fan-out via 11 worktree subagents.

4. **Merge subagents** → full build → Track G starts.

5. **Track G** serial (5 lemmas) then rewiring fan-out.

6. **V12–V14 gates** + CLOSED section + REPORT + memory.

## Verification (end-to-end how-to)

```bash
cd /home/cody/zisk-fv
cd ZiskFv && lake build                              # V1
cd .. && just verify-phase5                          # new bundled target
git grep -n 'sorry' ZiskFv/ZiskFv/                   # V3: empty
# V12: grep -c 'h_input_r1' for each metaplan theorem  (expect 0)
# V13: transpile-axiom consumer script (each > 0)
# V14: side-by-side with openvm-fv mul_spec
```

**End state.** Parameter surface of every `equiv_<OP>_metaplan` theorem
matches openvm-fv's RISC-V-equivalence theorem modulo bundling
preferences. 62 axioms all genuinely load-bearing. `REPORT.md` §3
caveats fully retired. Project at complete structural parity with the
openvm-fv template.
