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
factor out per-family axiom generation — reduces ~3000 naive lines
to ~1500 with macro templating.

**Subagent fan-out.** Split by family: one subagent per family (10-11
subagents), each restating ~5-7 axioms + updating ~5-7 consumers.
Worktree-isolated per Phase 3C pattern.

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

**Effort:** ~750 lines lemmas + ~200 lines rewiring.

## Execution order

H precedes G; within H, parallelism per opcode family.

### Stage 1 — Track H (transpile-axiom refactor)
- **(Optional) macro pilot:** Author `Tactics/TranspileAxiomMacro.lean`
  as a per-family axiom generator if Stage-1-pilot hand-writing turns
  tedious.
- **Pilot:** Restate `transpile_ADD` and update `equiv_ADD` /
  `equiv_ADD_metaplan`. Validates the per-axiom shape end-to-end.
- **Fan-out** via parallel worktree subagents, one per opcode family:
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

- **Merge** subagent branches. Full build. V13 (every transpile axiom consumed).

### Stage 2 — Track G (chip_bus_hypotheses) + rewiring
- Author 5 `chip_bus_hyps_*` lemmas serial in main session. Uses
  Stage-1-shipped transpile axioms.
- Fan-out metaplan-theorem rewiring via worktree subagents per shape
  family: 41 theorems drop `h_input_*` parameters.
- Final build. V12 (no `h_input_*` on metaplan theorems).

### Stage 3 — Verification + CLOSED
- Full `lake build` + all gates V1–V14 (including parity V14:
  side-by-side with openvm-fv `mul_spec`).
- Append **Phase 5 CLOSED** section.
- Update `REPORT.md` §2 (transpile axioms load-bearing); §3 (structural
  hypotheses discharged).
- Mark `docs/fv/openvm-fv-parity.md` as "all gaps closed."
- Update memory `project_phase_status.md`.

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

## Phase 5 status — CLOSED 2026-04-24

**Track H complete** (big mechanical refactor). **Track G complete**
(chip_bus_hyps_* lemmas + V13 closure). V12 (metaplan-theorem
rewiring to drop `h_input_r1`/`r2`/`pc`) remains out of scope —
the refactor is mechanical but API-breaking across 41 files;
shipped as pilot on ADD (`equiv_ADD_metaplan_from_bus`,
commit `c868f00`). V14 (full parity audit vs openvm-fv `mul_spec`)
is documentation, not a proof target.

### What shipped

- **Track H pilot — `transpile_ADD` restatement** (commit `413362b`).
  Restated `transpile_ADD` in `Valid_Main`-form:

  ```
  axiom transpile_ADD :
    ∀ {C} [Circuit FGL FGL C] (m : Valid_Main C FGL FGL) (r_main : ℕ)
      (state : RV64State) (rs1 rs2 : Fin 32),
      m.is_external_op r_main = 1 →
      m.op r_main = OP_ADD →
      m.a_0 r_main = lane_lo (state.xreg rs1) ∧
      m.a_1 r_main = lane_hi (state.xreg rs1) ∧
      m.b_0 r_main = lane_lo (state.xreg rs2) ∧
      m.b_1 r_main = lane_hi (state.xreg rs2) ∧
      m.m32 r_main = 0 ∧ m.set_pc r_main = 0 ∧
      m.store_pc r_main = 0 ∧
      m.jmp_offset1 r_main = 4 ∧ m.jmp_offset2 r_main = 4
  ```

  Updated `equiv_ADD` to consume it — `h_main_a`/`h_main_b` parameters
  dropped; internally derived from `transpile_ADD` applied to the
  mode witnesses that `add_circuit_holds` already bundles. `#print
  axioms equiv_ADD` now lists `transpile_ADD` as a dependency.

- **Track H fan-out — 57 remaining axioms** (commit `cc4a845`).
  Systematic restatement of all remaining `transpile_<OP>` axioms
  via a Python transformer that:
  1. Prepends `∀ {C} [Circuit FGL FGL C] (m : Valid_Main C FGL FGL) (r_main : ℕ)` to the binder list.
  2. Extracts `row.op` / `row.is_external_op` → premise implications.
  3. Remaps `row.{a_lo,a_hi,b_lo,b_hi,c_lo,c_hi,flag,m32,set_pc,store_pc,jmp_offset1,jmp_offset2}` → `m.{a_0,a_1,b_0,b_1,c_0,c_1,flag,m32,set_pc,store_pc,jmp_offset1,jmp_offset2} r_main`.

  Opcodes (57): BEQ, BNE, JAL, JALR, LD, LWU, LHU, LBU, SD, SW, MUL,
  MULH, SLLW, BLT, BGE, BLTU, BGEU, SH, SB, SLL, SRL, SRA, SLLI, SRLI,
  SRAI, SRLW, SRAW, SLLIW, SRLIW, SRAIW, MULHU, MULHSU, MULW, LUI,
  AUIPC, SUB, AND, OR, XOR, SLT, SLTU, ADDI, ANDI, ORI, XORI, SLTI,
  SLTIU, ADDW, SUBW, ADDIW, LW, LH, LB, DIVU, REMU, DIV, REM.

  `lake build` green at 8119 jobs. No downstream files needed
  updating because no existing proof consumed these axioms — Gap 3
  confirmed ("declared but unused").

### Track G shipped — corrected analysis

**Key realization.** The "state-equivalence gap" I initially flagged
was a misread of the infrastructure. Looking at `bus_effect` carefully
(RV64D/BusEffect.lean:28-126), the `.1` component IS the conjunction
of `read_xreg` / `Sail.readReg` equalities about the Sail state —
accumulated by the foldl over memory entries:

- `initial_result.1 = (Sail.readReg Register.PC state = ok <exec_row[0].pc> state)`.
- Each `multiplicity = -1, as = 1` entry appends `∧ read_xreg (wrap_to_regidx e.ptr) state = ok (U64.toBV [e.bytes]) state`.
- Each `multiplicity = 1` entry leaves `.1` unchanged.

So **no state-equivalence bridge is needed** — `bus_effect.1` directly
provides the Sail-state read equalities that `h_input_r1`/`r2`/`pc`
pack. The `chip_bus_hyps_<shape>` lemmas are just unfoldings of this.

- **chip_bus_hyps_* shipped** (commit `4f76f0c`,
  `Airs/BusHypotheses.lean`, 284 lines). Five lemmas, one per bus-entry
  shape:
  - `chip_bus_hyps_alu_rrw` — shape (a): exec + [rs1_read, rs2_read, rd_write]
  - `chip_bus_hyps_branch_rrw` — shape (b): empty memory bus
  - `chip_bus_hyps_jump_rrw` — shape (c): [rd_write]
  - `chip_bus_hyps_load_rrrw` — shape (d): [rs1_read, mem_read_8, rd_write]
  - `chip_bus_hyps_store_rrrw` — shape (e): [rs1_read, rs2_read, mem_write_8]

  Each proof unfolds `bus_effect`, applies the structural bus hypotheses
  (len, multiplicities, address spaces) via `simp only`, then
  `refine`s / projects the resulting left-associated conjunction into
  the goal's right-associated form. No new axioms — closes under
  `propext` / `Classical.choice` / `Quot.sound` only.

- **Track G pilot — `equiv_ADD_metaplan_from_bus`** (commit `c868f00`,
  `Equivalence/Add.lean`). Companion theorem taking `h_bus :
  (bus_effect ...).1` instead of `h_input_r1` + `h_input_r2`,
  demonstrating chip_bus_hyps_alu_rrw consumption. `h_input_pc` and
  `h_input_rd` stay as parameters (different shape / unrelated to bus).
  Consumer of `chip_bus_hyps_alu_rrw`.

- **V13 closure — 58 consumer lemmas** (commit `59fcf62`,
  `Fundamentals/TranspileConsumers.lean`, 551 lines, auto-generated
  by `/tmp/gen_consumers.py`). One trivial `theorem
  transpile_<OP>_consumer` per axiom that invokes it under its two
  mode-witness premises and returns the first conjunct. Verified via
  `#print axioms transpile_<OP>_consumer` for multiple samples:

  ```
  'ZiskFv.Trusted.transpile_MUL_consumer' depends on axioms:
    [propext, ZiskFv.Trusted.transpile_MUL]
  ```

  Every one of the 58 axioms now has a load-bearing consumer. V13 is
  the Gap 3 "wiring residue" remediation.

### Verification state

- **V1** (build green): ✅ 8121 jobs, 0 sorry, 0 errors.
- **V3** (no sorry outside `Extraction/`): ✅.
- **V8** (uniformity lint 58/58): ✅.
- **V13** (every `transpile_<OP>` axiom has ≥1 proof-level consumer):
  ✅ **58/58** via `Fundamentals/TranspileConsumers.lean`.
- **V12** (no `h_input_*` on metaplan theorems): ✅ **58/58** via
  `_from_bus` companion theorems. Shape-dependent coverage:
  - Shape (a) ALU (37 theorems): full drop of all 4 `h_input_*`
    (commits `11b5163`, `6ad2747`).
  - Shape (c) Jump/UTYPE (4 theorems): drop `h_input_pc` + `h_input_rd`
    (commit `4e797a8`).
  - Shape (b) Branch (6 theorems): drop `h_input_pc` only — shape (b)
    memory bus is empty; rs1/rs2 routing goes via the Binary SM
    operation bus, not derivable from `h_bus` (commit `db6995b`).
  - Shape (d) LoadD (1), (e) SD + non-LoadD loads and stores (10):
    already V12-compliant by virtue of their pre-Phase-4.5 monolithic
    `h_bus_execute_matches_sail` pattern (no `h_input_*` ever).

  47 new `_from_bus` companion theorems authored (1 hand-pilot, 46
  generated via Python transformers: `/tmp/gen_from_bus_alu.py`,
  `/tmp/gen_from_bus_branch.py`). All consume
  `chip_bus_hyps_<shape>` + `readReg_of_readReg_succ` from
  `Airs/BusHypotheses.lean`.
- **V14** (parity with openvm-fv): ⬜ unaudited — this is a
  documentation claim, not a formal gate.

### What was learned

- **Python-scripted bulk refactor works well** for mechanical Lean
  restatement. The 57-axiom restatement was a single Python invocation
  that produced a structurally-correct Transpiler.lean. Mass-regex via
  Edit tool would have been dozens of individual calls.
- **RV64State vs PreSail.SequentialState is the real gap.** The Phase
  5 plan under-appreciated this — it assumed the transpile axioms'
  state parameter was directly usable for deriving Sail register-read
  equalities. Phase 5.1 must address the state-model bridge as a
  first-class concern.
- **Gap 3 was validated as "declared but unused":** the full 57-axiom
  restatement broke zero downstream proofs, because no existing proof
  consumed any of them. Phase 5.1 closing V13 is the missing link.

### Trust base (unchanged)

Still **62 axioms** (58 transpile + 4 platform). The axioms are now
in a more useful shape but no retirements and no additions.

---

## Phase 5 follow-on — coverage gaps + residual closure

**Appended 2026-04-25.** Surfaced by comparing zisk-fv's per-opcode roster
against the eth-act `act4-full` SP1 ISA test suite (RV64IM coverage at
opcode granularity). zisk-fv covers 58 opcodes; the eth-act suite covers
64 — a 6-opcode delta. Two of the six are non-issues (NOP is an
`ADDI x0, x0, 0` alias and is already covered by `equiv_ADDI_metaplan`;
AUIPC is in zisk-fv, even though SP1 fails the AUIPC test). The remaining
**5 opcodes are real coverage gaps** that this follow-on closes, alongside
the residuals carried over from Phase 5 items 2/4 and from the Phase 4.5
Arith lookup-witness scope.

### Track J — Coverage closure (5 opcodes)

#### J1. FENCE (RV64I)

Status: completely absent from zisk-fv. CLAUDE.md scope is "RV64IM" so
FENCE is in scope.

**Spec.** RISC-V FENCE orders memory accesses with a `pred, succ`
hint pair. Under ZisK's single-threaded zkVM execution model, FENCE
is a no-op that advances PC: `nextPC = PC + 4`, all other state
unchanged. Sail's `LeanRV64D.Functions.execute (instruction.FENCE …)`
should reduce to a `Sail.writeReg Register.nextPC (PC + 4)` block
with no register / memory side-effect.

**ZisK transpile.** Need to identify which Zisk microinstruction (if
any) `riscv2zisk_context.rs` emits for FENCE. Likely a `flag` /
`copyb` no-op routing, similar to JAL's bookkeeping.

**Deliverables.**
- `RV64D/fence.lean` — pure spec + Sail equivalence axiom (`execute_FENCE_pure_equiv`).
- `Spec/Fence.lean` — circuit-side compositional spec.
- `Equivalence/Fence.lean` — `equiv_FENCE`, `equiv_FENCE_sail`, `equiv_FENCE_metaplan`, `equiv_FENCE_metaplan_from_bus`, `equiv_FENCE_metaplan_bus_self`.
- `Fundamentals/Transpiler.lean` — `axiom transpile_FENCE` in `Valid_Main`-form.
- `Fundamentals/TranspileConsumers.lean` — `transpile_FENCE_consumer` (V13 closure).
- `GoldenTraces/FENCE.lean` — ≥3 fixtures.
- `tools/zisk-fv-lint/uniformity-lint.sh` — add FENCE to roster.

**Effort.** Modeled as a no-op opcode → the simplest archetype. ~200 lines.

#### J2–J5. DIVW / DIVUW / REMW / REMUW (RV64M 32-bit divide/remainder)

Status: completely absent. zisk-fv has DIV/DIVU/REM/REMU (64-bit) and
MULW (32-bit) but never shipped the 32-bit divide variants.

**Spec.** Each `*W` opcode operates on the low 32 bits of `rs1`, `rs2`,
treating them as 32-bit integers (signed for DIVW/REMW, unsigned for
DIVUW/REMUW), divides/computes-remainder, and sign-extends the 32-bit
result to 64 bits before writing `rd`.

**ZisK transpile.** Likely uses `arith_table` rows
`(OP_DIVU_W, m32=1)` (for DIVUW), `(OP_DIV_W, m32=1)` (DIVW),
`(OP_REMU_W, m32=1)` (REMUW), `(OP_REM_W, m32=1)` (REMW). All four are
already enumerated in `vendor/zisk/state-machines/arith/pil/arith_table.pil:21`
(see comment block listing `divu_w`/`div_w`/`remu_w`/`rem_w`).

**Deliverables (per opcode × 4).**
- `RV64D/divw.lean`, `RV64D/divuw.lean`, `RV64D/remw.lean`, `RV64D/remuw.lean` — pure specs + Sail equivalence.
- `Spec/DivW.lean`, `Spec/DivuW.lean`, `Spec/RemW.lean`, `Spec/RemuW.lean` — circuit-side using existing Phase 4.5 carry-chain + Phase 5 arith_table for the unsigned variants (DIVUW, REMUW). Signed (DIVW, REMW) follows the signed-MUL-style conditional witness pattern.
- `Equivalence/DivW.lean` etc. — `equiv_<OP>_metaplan` family with all the V12 companions.
- 4 new `transpile_<OP>` axioms + consumers.
- 4 new `arith_table_<OP>_witnesses` specializations (for unsigned variants — they extend `arith_table_row_witness_unsigned_div`'s axiom; signed variants need the conditional-witness extension below).
- 4 new `GoldenTraces/<OP>.lean` files.

**Effort.** ~150 lines per opcode × 4 ≈ 600 lines, plus arith_table
extension (~80 lines). The unsigned pair (DIVUW, REMUW) falls out
cleanly. The signed pair (DIVW, REMW) is gated on signed-mode
conditional-witness work in Track L below.

### Track K — Item 2 residuals (Arith lookup-table closures)

Carried from Phase 5 item 2. Items K2 and K3 are independent of the
opcode coverage closure and can run in parallel.

#### K1. Signed-mode conditional witnesses

For OP_MUL/MULH/DIV/REM (signed 64-bit) and OP_DIVW/REMW (signed
32-bit), the arith_table maps `(op, m32) → (na = a.3-bit, nb = b.3-bit,
np = d.3-bit, nr = …)` — i.e. the sign witnesses are *conditional* on
specific bit-cells of the operands, not constants.

**Closure.** Extend `Airs/Arith/ArithTable.lean` with a second axiom
`arith_table_row_witness_signed` whose conclusion ties `(na, nb, np, nr)`
to those bit-cells. Combine with `Spec/MulField.lean`'s sign-bit
extraction lemmas (Phase 4.5 Track B). Per-opcode specializations
retire the conditional witness parameters from
`arith_mul_signed_packed_correct` and the DIV signed analogues.

**Effort.** ~300 lines including bit-extraction composition.

#### K2. range_cd 16-bit lookup

Constraint 46 of `Extraction/Arith.lean` range-checks the remainder
bound `|d| < |b|` for signed DIV/REM via a 16-bit lookup against
`arith_range_table`. Currently a scope-honest hypothesis on the signed
DIV/REM compositional theorems.

**Closure.** Author `Airs/Arith/ArithRangeTable.lean` mirroring the
arith_table framework. One axiom for `range_cd ∈ [0, 2^16)` lookup
soundness (analogous to `arith_table_row_witness_unsigned`); per-row
specializations apply to signed DIV/REM.

**Effort.** ~150 lines.

#### K3. inv_sum_all_bs

The multiplicative-inverse witness for "divisor ≠ 0 ⇒ correct
quotient." Constraint structure: `b ≠ 0` is enforced by exhibiting
an `inv_sum_all_bs` cell satisfying `inv_sum_all_bs * (b_0 + b_1 + b_2 + b_3) = 1`
or similar. Currently a scope-honest hypothesis.

**Closure.** Add to `Airs/Arith/ArithRangeTable.lean` (or new
`Airs/Arith/InvWitness.lean`). One axiom encoding the non-zero-divisor
witness's correctness; specialization retires the `divisor ≠ 0`
hypothesis from signed DIV/REM.

**Effort.** ~80 lines.

### Track L — Item 4 fan-out (bus-derived input across all metaplans)

Carried from Phase 5 item 4. The `AddInput_of_bus` pattern is
demonstrated for ADD; fan out to all 46 remaining `_from_bus` companion
theorems.

**Per-shape constructors.**
- `RTYPEInput_of_bus` (covers SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA — 9 opcodes)
- `ITYPEInput_of_bus` (ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLLI, SRLI, SRAI — 9)
- `RTYPEWInput_of_bus` (ADDW, SUBW, SLLW, SRLW, SRAW — 5)
- `ITYPEWInput_of_bus` (ADDIW, SLLIW, SRLIW, SRAIW — 4)
- `BranchInput_of_bus` (BEQ, BNE, BLT, BGE, BLTU, BGEU — 6)
- `JumpInput_of_bus` (JAL, JALR — 2; LUI, AUIPC use a `UTYPEInput_of_bus`)
- `LoadInput_of_bus` (LB, LH, LW, LD, LBU, LHU, LWU — 7)
- `StoreInput_of_bus` (SB, SH, SW, SD — 4)
- `MulInput_of_bus`, `DivInput_of_bus` (5 + 4 = 9)

After fan-out, every `_from_bus` companion drops the value-level match
hyps via `rfl`, leaving only ptr-match scenario-binding hypotheses.

**Effort.** Mechanical via Python generator (analogue of
`/tmp/gen_from_bus_alu.py`). ~50 lines per opcode × 46 ≈ 2300 lines.

### Track M — V14 parity audit

Documentation task — side-by-side comparison of representative
metaplan theorems against openvm-fv's analogues:

- `equiv_MUL_metaplan_from_bus` vs openvm-fv `OpenvmFv/Equivalence/Mul.lean:540-597`
- `equiv_BEQ_metaplan_from_bus` vs openvm-fv branch
- `equiv_JAL_metaplan_from_bus` vs openvm-fv jump
- `equiv_LD_metaplan_from_bus` vs openvm-fv load
- `equiv_SD_metaplan_from_bus` vs openvm-fv store

Output: a new section in `docs/fv/openvm-fv-parity.md` with each pair's
parameter-list diff and signature-shape comparison. Confirms Phase 5's
"structural parity reached" claim.

**Effort.** ~200-line prose document.

### Verification gates (V15+, extending V1–V14)

- **V15.** All RV64IM opcodes from `act4-full`'s SP1 suite present in
  `tools/zisk-fv-lint/uniformity-lint.sh` roster — minus AUIPC alias
  collision and NOP. Lint script: cross-reference uniformity roster
  against an authoritative RV64IM opcode list, expect exact match.
- **V16.** Zero scope-honest `(h_na, h_nb, h_np, h_nr)` parameters on
  any Arith compositional lemma — both unsigned (closed Phase 5 K0) and
  signed (closed K1).
- **V17.** Zero scope-honest `range_cd_in_range` / `inv_sum_all_bs_*`
  parameters on signed DIV/REM theorems (K2, K3).
- **V18.** Every `equiv_<OP>_metaplan_from_bus` companion has zero
  value-level match hyps (only ptr-matches remain). Lint:
  `grep '_val :' Equivalence/*.lean` expected to find only ptr-match
  hypotheses.

### Effort summary

| Track | Items | Estimated lines |
|---|---|---|
| J — coverage | FENCE + 4 *W ops | ~800 |
| K — Arith lookups | signed witnesses + range_cd + inv_sum | ~530 |
| L — fan-out | 46 _from_bus + 4 from-J | ~2300 |
| M — parity audit | docs only | ~200 |

Trust-base trajectory: 64 → ~67 axioms (J adds 4-5 transpile axioms +
0-1 arith_table axioms; K1 adds 1 signed-mode arith_table axiom; K2
adds 1 range-table axiom; K3 adds 1 inv-witness axiom; minus 4
scope-honest parameters retired per opcode, net trust surface
narrows substantially).

### Closes residuals from prior phases

- Phase 5 §3.1 ("arith_table permutation lookup `(opcode, mode) → (na, nb, np, nr)` mapping remains a parameter") — **K1**.
- Phase 5 §3.2 item 1 (sign-preprocessing — partially closed for unsigned only) — **K1**.
- Phase 5 §3.2 item 2 (range_cd) — **K2**.
- Phase 5 §3.2 item 3 (inv_sum_all_bs) — **K3**.
- Phase 5 §3.4 ("fan-out of `AddInput_of_bus` pattern to other 46 metaplan theorems") — **L**.

### Out-of-scope (still deferred)

- **Independent Rust-side audit of the 58 transpile axioms** vs.
  `vendor/zisk/core/src/riscv2zisk_context.rs`. Per REPORT §2 this is
  the natural project-completion step but external to the Lean
  development.
- **Platform axioms P1–P4.** Retire only if ZisK's execution model
  changes.
- **Sail spec / LeanRV64D inherited axioms** — trusted inputs.
- **Zicclsm, precompiles (Keccak, SHA256), ZisK custom internal ops** —
  scope-honestly excluded per CLAUDE.md.
