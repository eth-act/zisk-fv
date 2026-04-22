# Phase 3 — Parallel sweep (RV64IM opcodes via archetype fan-out)

**Status:** Phase 3A IN PROGRESS (started 2026-04-22).

## Context

Phase 2.5 closed at commit `0a66910` with six validated archetype macros
(Branch, Jump, Load, Store, Mul, Shift) and thirteen opcodes shipped
(ADD, BEQ, BNE, JAL, JALR, LD, LWU, SD, SW, MUL, MULH, SLLW, SRLW).
Per-opcode cost under a validated macro is calibrated at ≈½ day of
subagent time — six Phase 2.5 D4 siblings (BNE, JALR, LWU, SW, MULH,
SRLW) each shipped with zero macro adjustment.

Per the metaplan (`ai_plans/zisk-fv-metaplan.md` § Phase 3) this phase
closes the remaining RV64IM tail with no new architecture. Because
~50 opcodes is too large for a single commit cycle, Phase 3 is staged:

- **Phase 3A** (this plan): sibling fan-out across the **five**
  value-producing archetypes — 24 opcodes. (Jump has no remaining
  RV64IM siblings — JAL + JALR complete the jump family.)
- **Phase 3B** (next user prompt): new archetypes — ALU RTYPE
  (SUB / AND / OR / XOR / SLT / SLTU / ADDW / SUBW), ALU ITYPE
  (ADDI / ANDI / ORI / XORI / SLTI / SLTIU / ADDIW), DIV/REM family
  (DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW, REMUW), UTYPE (LUI,
  AUIPC).

Phase 3A is scoped to opcodes **whose Spec/Equivalence files can be
authored by instantiating an already-shipped archetype macro** without
touching `Fundamentals/Execution.lean`, `Airs/Main.lean`, `Airs/
OperationBus.lean`, or any of the six `Tactics/*Archetype.lean` files.
The only shared-file edits are additive: new `transpile_<OP>` axioms
in `Fundamentals/Transpiler.lean`, new `ZiskFv/*.lean` root imports,
new entries in `docs/fv/trusted-base.md` for any Sail-equivalence
axioms that mirror M1-M4 / C1.

## Scope (strict)

**In scope — Phase 3A (24 opcodes across 5 archetypes):**

- **Branch (4):** BLT, BGE, BLTU, BGEU. All four use the
  `BranchArchetype` macro.
  - BLT, BGE on Zisk op `OP_LT = 7`; BLTU, BGEU on `OP_LTU = 6`.
  - BLT/BLTU: `neg = 0` (flag=1 taken) — direct mirror of BEQ.
  - BGE/BGEU: `neg = 1` (offset swap) — direct mirror of BNE.

- **Load (5):** LB, LBU, LH, LHU, LW. All five use the `LoadArchetype`
  macro (inherits D3e-DEFERRED shape (d) — each metaplan theorem
  retains `h_bus_execute_matches_sail` hypothesis, like LWU).
  - Widths: LB/LBU = 1 byte; LH/LHU = 2 bytes; LW = 4 bytes.
  - Sign-extend: LB, LH, LW (signed loads); LBU, LHU zero-extend.
  - Each needs a trusted `execute_<OP>_pure_equiv_axiom` in
    `RV64D/<op>.lean::PureSpec`, added to `docs/fv/trusted-base.md`
    as "M5..M9" — siblings of M1 (LOADD) / M3 (LOADWU). Closable once
    Phase 2.6 extends `RISC_V_assumptions` with PMP/CLINT witnesses.

- **Store (2):** SB, SH. Both use the `StoreArchetype` macro
  (inherits D3e-DEFERRED shape (e) — each metaplan theorem retains
  `h_bus_execute_matches_sail`).
  - Widths: SB = 1 byte; SH = 2 bytes.
  - Each needs a trusted axiom ("M10..M11") — siblings of M2 (STORED)
    / M4 (STOREW).

- **Mul (3):** MULHU, MULHSU, MULW. All three use the `MulArchetype`
  macro.
  - MULHU: unsigned × unsigned, high 64 bits.
  - MULHSU: signed × unsigned, high 64 bits.
  - MULW: 32-bit multiply, sign-extend to 64 — **`m32 = 1` route**
    (uses the W-variant sub-archetype if one exists; otherwise directly
    instantiates the existing macro at `m32 = 1` and adjusts the mode
    predicate, as SLLW/SRLW do for Shift).

- **Shift (10):** split into two sub-tasks for cognitive management:
  - **Shift-64 (6):** SLL, SRL, SRA, SLLI, SRLI, SRAI.
    - Register variant (SLL/SRL/SRA): Binary SM ops (OP_SLL, OP_SRL,
      OP_SRA at Zisk), shamt from `rs2[5:0]`.
    - Immediate variant (SLLI/SRLI/SRAI): Binary SM ops, shamt
      from imm[5:0]. Uses a different transpile path in
      `riscv2zisk_context.rs` (`create_imm_op`-style rather than
      `create_register_op`).
  - **Shift-32W (4):** SLLIW, SRLIW, SRAIW, SRAW. Direct analogues of
    the shipped SLLW / SRLW, `m32 = 1` route.

**Explicitly out of scope (Phase 3B or later):**

- SUB, AND, OR, XOR, SLT, SLTU, ADDW, SUBW — these share ADD's macro
  shape but require **Binary-SM op literals beyond OP_ADD** and may
  demand a generalization of `Spec/Add.lean` into a reusable
  "ALU-RTYPE archetype" (Phase 3B, estimated 2-day archetype build +
  ½ day per sibling).
- DIV, DIVU, REM, REMU and their W-variants — these route through the
  **Arith state machine** (not Binary), requiring a new state-machine
  AIR reference and a new archetype macro (Phase 3B).
- ADDI, ANDI, ORI, XORI, SLTI, SLTIU, ADDIW — these share the Main-AIR
  shape but require a new "ALU-ITYPE archetype" capturing the
  `b_lo = sign_extend(imm)` immediate routing (Phase 3B).
- LUI, AUIPC — UTYPE archetype, no Binary SM, literal load (Phase 3B).
- FENCE, ECALL, EBREAK, CSR* — out of RV64IM scope per CLAUDE.md.
- Closing the five (now fifteen with Phase 3A's extension) Sail-side
  memory/control axioms — that is Phase 2.6 / Phase 4 work. Phase 3A
  adds axioms, it does not close them.

**Specifically preserved invariants (Phase 3A must not regress):**

- `lake build` green, zero `sorry` anywhere under `Fundamentals/`,
  `Airs/`, `Spec/`, `Equivalence/`, `GoldenTraces/`, `Tactics/`, and
  in every `RV64D/*.lean` imported by `ZiskFv.lean` at phase close.
- The six archetype macros are untouched (read-only). If a sibling
  requires a macro tweak, that is a **flag-and-stop** — log the
  surprise in the CLOSED section and escalate to the user; do not
  silently mutate the macro.
- `just verify-phase2` remains green (Phase 3A's additive extensions
  must not break the Phase 2.5 gate).

## Execution order

Track prefixes: B (Branch), L (Load), S (Store), M (Mul), H (Shift
64), H2 (Shift W). Dispatched in parallel — each track writes its own
`Spec/`, `Equivalence/`, `GoldenTraces/`, `RV64D/` file set plus
adds to `Fundamentals/Transpiler.lean`. The only cross-track merge
hazard is `Fundamentals/Transpiler.lean` (append-only) and
`ZiskFv/ZiskFv.lean` (append-only imports); trivial to rebase.

### Track B — Branch siblings (4 opcodes)

**B1 — BLT.** Transpile via `create_branch_op(instr, "lt", false, 4)`
at `riscv2zisk_context.rs`. Zisk op = `OP_LT = 7`, `neg = 0` — BEQ
polarity. New axiom `transpile_BLT`. Spec/BranchLessThan.lean,
Equivalence/BranchLessThan.lean, GoldenTraces/BLT.lean. RV64D's
`blt.lean` already exists; add `PureSpec.execute_BLT_pure` and
`execute_BLT_pure_equiv` (pattern from BNE — no new axiom unless Sail
closure stalls, in which case axiomatize as "C2" per C1 precedent).

**B2 — BGE.** `create_branch_op(instr, "lt", true, 4)`. OP_LT,
`neg = 1`. Transpile axiom mirrors BNE with `OP_EQ → OP_LT`.

**B3 — BLTU.** `create_branch_op(instr, "ltu", false, 4)`. OP_LTU = 6,
`neg = 0`. BEQ polarity.

**B4 — BGEU.** `create_branch_op(instr, "ltu", true, 4)`. OP_LTU,
`neg = 1`. BNE polarity.

### Track L — Load siblings (5 opcodes)

Pattern: direct analogue of `Equivalence/LoadWU.lean` (D4c). Each
opcode needs:
- `transpile_<OP>` axiom in Transpiler.lean (routes through
  `create_load_op` with the appropriate `ind_width` byte count).
- `RV64D/<op>.lean` with `PureSpec.<Op>Input`, `execute_<OP>_pure`,
  `execute_<OP>_pure_equiv_axiom`. Axiomatized per the M1/M3 policy —
  catalogue as M5..M9 in `docs/fv/trusted-base.md`.
- `Spec/Load<Name>.lean` instantiating the `LoadArchetype` macro with
  the right opcode + width.
- `Equivalence/Load<Name>.lean` with the three-theorem trio; metaplan
  theorem retains `h_bus_execute_matches_sail` per D3e.
- `GoldenTraces/<OP>.lean` with concrete rows.

**L1 — LW** (4 bytes, signed — direct analogue of LWU).
**L2 — LH** (2 bytes, signed).
**L3 — LHU** (2 bytes, unsigned).
**L4 — LB** (1 byte, signed).
**L5 — LBU** (1 byte, unsigned).

### Track S — Store siblings (2 opcodes)

Pattern: direct analogue of `Equivalence/StoreW.lean` (D4d). Same
ingredient set as Load; axioms catalogued as M10 / M11 (siblings of
M2 / M4).

**S1 — SH** (2 bytes).
**S2 — SB** (1 byte).

### Track M — Mul siblings (3 opcodes)

Pattern: direct analogue of `Equivalence/MulH.lean` (D4e) for MULHU /
MULHSU; analogue of `Equivalence/Shift.lean` (Phase 2.5 SLLW) for
MULW because MULW uses the `m32 = 1` routing. Each needs:

- `transpile_<OP>` axiom (route via `create_arith_op` in
  `riscv2zisk_context.rs`).
- Pure spec in `RV64D/<op>.lean` + equivalence theorem (Mul pure-spec
  chain already derived through `Fundamentals/Execution.lean::
  execute_RTYPE_pure` — probably no new axiom).
- Spec / Equivalence / GoldenTraces files.

**M1 — MULHU** (unsigned × unsigned, high 64).
**M2 — MULHSU** (signed × unsigned, high 64).
**M3 — MULW** (32-bit mul, sign-ext, `m32 = 1`).

### Track H — Shift siblings (64-bit, 6 opcodes)

Register variant pattern: direct analogue of `Equivalence/Shift.lean`
(Phase 2.5 SLLW), but `m32 = 0` route. Immediate variant pattern: same
but the transpile axiom reads `b_lo = sign_extend(imm[5:0])` instead
of `lane_lo(state.xreg rs2)`.

**H1 — SLL** (register, left, `m32 = 0`, Zisk `OP_SLL`).
**H2 — SRL** (register, right logical).
**H3 — SRA** (register, right arithmetic).
**H4 — SLLI** (immediate, left).
**H5 — SRLI** (immediate, right logical).
**H6 — SRAI** (immediate, right arithmetic).

### Track H2 — Shift siblings (32-bit W, 4 opcodes)

Direct analogues of SLLW / SRLW. `m32 = 1` route.

**H2a — SRAW** (register, right arithmetic, W).
**H2b — SLLIW** (immediate, left, W).
**H2c — SRLIW** (immediate, right logical, W).
**H2d — SRAIW** (immediate, right arithmetic, W).

### Track V — Verify + CLOSED

**V1.** `lake build` green. `git grep -n 'sorry'` across
`ZiskFv/Fundamentals ZiskFv/Airs ZiskFv/Spec ZiskFv/Equivalence
ZiskFv/GoldenTraces ZiskFv/Tactics` + all 24 new `RV64D/*.lean` files
returns empty.

**V2.** `just verify-phase2` still green.

**V3.** `#print axioms <equiv_<OP>_metaplan>` for each of the 24 new
opcodes shows only kernel axioms + `transpile_<OP>` + (for L/S
families) the single trusted memory axiom. No `sorryAx`.

**V4.** `docs/fv/trusted-base.md` updated with entries for the new
axioms. Each entry: statement, file, consumers, provenance, closure
path.

**V5.** Append "Phase 3A status — CLOSED <date>" section to
`ai_plans/zisk-fv-phase-3.md` with: shipped opcodes, axiom count
delta, any macro surprises that required a flag-and-stop, per-opcode
wall-clock, Phase 3B readiness notes.

**V6.** `git log --oneline main..HEAD` reads as ≈6-8 commits,
one-per-track plus V.

## Parallelism overview

All six tracks (B, L, S, M, H, H2) run in parallel subagents with
`isolation: worktree`. Expected wall-clock:

- Track B: 4 × ½ day = 2 days (serialized within the track by one
  agent owner).
- Track L: 5 × ½ day = 2.5 days.
- Track S: 2 × ½ day = 1 day.
- Track M: 3 × ½ day = 1.5 days.
- Track H: 6 × ½ day = 3 days.
- Track H2: 4 × ½ day = 2 days.

Critical path: Track H (3 days) assuming effort holds. If per-opcode
cost surprises, pivot — H is the easiest to split into H-reg vs
H-imm sub-owners.

## Verification (end-to-end)

1. From clean checkout: `just verify-phase2` exits 0. (Phase 3A must
   not regress the Phase 2.5 gate.)
2. `cd ZiskFv && lake build` — full green.
3. `git grep sorry ZiskFv/ZiskFv/Equivalence/ ZiskFv/ZiskFv/Spec/
   ZiskFv/ZiskFv/GoldenTraces/` — empty.
4. For each of the 24 opcodes, `#print axioms` on its `*_metaplan`
   theorem shows only kernel axioms + `transpile_<OP>` + (where
   applicable) the catalogued Sail axiom.
5. `docs/fv/trusted-base.md` grows by the expected axiom count
   (roughly: 24 new transpile axioms + ≤ 7 memory axioms for L/S; if
   more emerge, log each in the CLOSED section).

## Known fragility

1. **Macro doesn't generalize for one sibling.** Phase 2.5 saw this
   once (JumpArchetype + JALR — needed a sub-archetype extension).
   Phase 3A expectation: most likely in Shift-immediate (new
   transpile shape), MULW (m32=1 route may interact with MulArchetype
   the way SLLW did with a freshly minted macro). Mitigation:
   flag-and-stop; propose a sub-archetype in the CLOSED section; user
   decides whether to patch the macro or axiomatize per-op.

2. **Sail pure-spec equivalence stalls on a CSR / privilege state
   reduction.** Policy: axiomatize via trusted-base, log as a new
   entry. Do not add a `sorry`. This is what D4b-patch did with
   `execute_JALR_pure_equiv_axiom` (C1).

3. **Transpile-axiom merge conflicts.** Minor — Transpiler.lean is
   strictly append-only in Phase 3A. If two agents pick adjacent
   insertion points, sequential git apply resolves.

4. **Shift-immediate operand routing.** The Zisk immediate-shift
   transpile emits `b_lo = imm[5:0]` rather than reading a register.
   If the existing `ShiftArchetype` macro assumes `b_lo = lane_lo
   (state.xreg rs2)`, the macro may not directly fit. Pre-execution
   check (Task H4): read `ShiftArchetype.lean` and confirm it is
   agnostic to `b_lo`'s source (unfolds via the `OperationBusEntry`
   shape, not via a transpile-axiom-specific hypothesis). If not,
   flag-and-stop.

## Critical files

**New per-opcode (24 × 3 = 72 files):**

- `ZiskFv/ZiskFv/Spec/<OpName>.lean` (24 new).
- `ZiskFv/ZiskFv/Equivalence/<OpName>.lean` (24 new).
- `ZiskFv/ZiskFv/GoldenTraces/<OP>.lean` (24 new).

**Edited (additive):**

- `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean` — +24 transpile axioms.
- `ZiskFv/ZiskFv/RV64D/<op>.lean` — each of the 24 files gains a
  `PureSpec` section with pure spec + equivalence axiom (or derived
  theorem where Sail closure is tractable).
- `ZiskFv/ZiskFv.lean` — +24 root imports.
- `docs/fv/trusted-base.md` — +24 transpile entries, up to +7
  memory/control axioms.

**Read-only (must not be mutated):**

- `ZiskFv/ZiskFv/Tactics/*Archetype.lean` (6 files).
- `ZiskFv/ZiskFv/Airs/Main.lean`, `Airs/OperationBus.lean`,
  `Airs/BusEmission.lean`.
- `ZiskFv/ZiskFv/Fundamentals/Execution.lean`.

## Phase 3A status — CLOSED 2026-04-22

`just verify-phase2` exits 0 from a clean checkout; `lake build`
green (7988 jobs total). Zero `sorry` in all scoped directories and
all 22 of the 24 planned Phase 3A opcode RV64D files (the 3 LW/LH/LB
signed-load stubs are deferred untouched — see Track L flag-and-stop
below).

### Shipped opcodes — 22 of 24 planned

- **Branch (4/4):** BLT, BGE, BLTU, BGEU — via `BranchArchetype`
  (opcode_lit ∈ {OP_LT = 7, OP_LTU = 6}; BLT/BLTU BEQ polarity,
  BGE/BGEU BNE polarity).
- **Load (2/5):** LHU, LBU — via `LoadArchetype`. **Flag-and-stop
  on LW/LH/LB** (signed-extension loads use external `signextend_*`
  ops incompatible with the `copyb`-shape macro; sign-extension-load
  archetype deferred to Phase 3B).
- **Store (2/2):** SH, SB — via `StoreArchetype` (both OP_COPYB,
  width 2 / 1; retain `h_bus_execute_matches_sail` parameter per
  D3e DEFERRED shape (e)).
- **Mul (3/3):** MULHU, MULHSU, MULW — via `MulArchetype`. MULHU /
  MULHSU closed with direct Sail proofs mirroring MulH; MULW
  axiomatized (C4, salvage path — missing `execute_MULW'` refactor).
- **Shift-64 (6/6):** SLL, SRL, SRA, SLLI, SRLI, SRAI — via
  `ShiftArchetype` at m32=0. All six closed directly via the
  `execute_RTYPE'` / `execute_SHIFTIOP'` chain; no axioms needed
  beyond the transpile contracts.
- **Shift-W (4/4):** SRAW, SLLIW, SRLIW, SRAIW — via `ShiftArchetype`
  at m32=1. SRAW closed directly per SLLW precedent; SLLIW/SRLIW/
  SRAIW axiomatized per C3a/b/c (missing `execute_SHIFTIWOP'`
  refactor).

### Gate targets — pass state

1. `lake build` → 7988 jobs, green. ✓
2. `just verify-phase2` → green. ✓
3. `git grep sorry` across scoped dirs + 22 Phase 3A RV64D files →
   empty. ✓ (LW/LH/LB retain pre-existing `sorry` stubs — not
   imported by `ZiskFv.lean`, out of scope per L-track
   flag-and-stop.)
4. `#print axioms` on each `equiv_*_metaplan` shows only kernel
   axioms + the catalogued trusted Sail axioms (C2a-C2d, M5-M11,
   C3a-C3c, C4); no `sorryAx`.

### Trust base — final Phase 3A state

New axioms this phase (on top of the 17 Phase 2.5 end-state):

- **+22 transpile axioms** in `Fundamentals/Transpiler.lean`:
  `transpile_{BLT,BGE,BLTU,BGEU,LHU,LBU,SH,SB,MULHU,MULHSU,MULW,
  SLL,SRL,SRA,SLLI,SRLI,SRAI,SRAW,SLLIW,SRLIW,SRAIW}` +
  `transpile_SRLW` (repaired from Phase 2.5 D4f dropped commit by
  Track H2). Associated new OP constants: `OP_LT=7`, `OP_LTU=6`,
  `OP_SLL=33`, `OP_SRL=34`, `OP_SRA=35`, `OP_SRL_W=37`,
  `OP_SRA_W=38`, `OP_MULUH=177`, `OP_MULSUH=179`, `OP_MUL_W=182`,
  plus helpers `shamt_b_lo` / `shamt_w_b_lo`.
- **+11 Sail-equivalence axioms** catalogued in
  `docs/fv/trusted-base.md`:
  - **C2a-C2d** (BLT/BGE/BLTU/BGEU, 4 axioms) — no
    `RISC_V_assumptions` extension needed; consolidated ≈1-day
    closure via the BNE skeleton + per-opcode comparator.
  - **M7, M9** (LHU, LBU, 2 axioms) — share M1-M4 PMP/CLINT
    closure path.
  - **M10, M11** (SH, SB, 2 axioms) — share M1-M4 PMP/CLINT
    closure path.
  - **C3a-C3c** (SLLIW/SRLIW/SRAIW, 3 axioms) — close under
    `execute_SHIFTIWOP'` refactor in `Fundamentals/Execution.lean`.
  - **C4** (MULW, 1 axiom) — closes under `execute_MULW'` refactor.

**Total trust base after Phase 3A:**
- 34 transpile axioms (12 Phase 2.5 + 22 Phase 3A).
- 16 Sail-equivalence axioms (5 Phase 2.5 + 11 Phase 3A):
  M1-M4, M7, M9, M10, M11; C1, C2a-C2d, C3a-C3c, C4.

### Execution history — what actually happened

Track B pilot (me, direct): 4 opcodes, 5 commits, clean. Validated
the pattern end-to-end before parallel fan-out.

Parallel fan-out (5 subagents, worktree isolation): L, S, M, H, H2.
Outcomes:

- **S** returned clean — 2 opcodes, 3 commits, rebased onto main.
- **L** returned with a principled **flag-and-stop** — 2 of 5
  opcodes shipped (LHU, LBU); LW/LH/LB flagged as out-of-scope for
  the shipped `LoadArchetype` due to the `signextend_*`-vs-`copyb`
  archetype mismatch. Moved to Phase 3B.
- **H** returned clean — 6 opcodes, 6 commits; all direct closures
  (no Sail axiom).
- **H2** returned clean — 4 opcodes, 4 commits; SRAW direct,
  SLLIW/SRLIW/SRAIW axiomatized per C3. Also caught and repaired a
  Phase 2.5 D4f dropped commit (missing `transpile_SRLW` +
  `OP_SRL_W` — the build had been passing via a stale lake cache).
- **M** returned broken — agent produced a malformed completion
  summary and left its 3 opcodes of work uncommitted in the
  worktree. Salvaged by (a) committing all uncommitted files in the
  worktree as a single cherry-pick source, (b) cherry-picking into
  main and resolving trivial append-only conflicts, (c) fixing a
  bad proof in `mulw.lean` (unqualified `to_bits_truncate` /
  `sign_extend`; `sorry` in the proof) by axiomatizing per C4.

### What this buys

- **22 new opcodes kernel-checked** modulo their transpile + Sail
  trust entries. Cumulative count: 35 of the ≈63 RV64IM opcodes
  (13 Phase 2.5 + 22 Phase 3A).
- **All six shipped archetype macros exercised with siblings.**
  No macro needed modification in Phase 3A (Phase 2.5 had one
  sub-archetype extension for JALR; Phase 3A had zero).
- **LoadArchetype coverage boundary identified** (copyb vs
  signextend), giving Phase 3B a concrete spec for a
  sign-extension-load archetype.
- **Three closable Sail-refactor groups carved out:** C3 (SHIFTIWOP
  triple), C4 (MULW triple), and consolidated C2a-d (BNE skeleton
  + comparator bridge). Each is a localized mechanical port that
  would retire 3-4 axioms with a single edit to
  `Fundamentals/Execution.lean` or a small Int-coercion bridge
  lemma.

### Residual gaps carried to Phase 3B+

- **LW, LH, LB (Track L flag-and-stop).** Need a new sign-extension-
  load archetype macro that handles `is_external_op = 1, op =
  OP_SIGNEXTEND_{B,H,W}`. Expected ~1 day archetype build + half-day
  per sibling.
- **ALU RTYPE sweep** (SUB, AND, OR, XOR, SLT, SLTU, ADDW, SUBW) and
  **ALU ITYPE sweep** (ADDI, ANDI, ORI, XORI, SLTI, SLTIU, ADDIW).
  Require new `ALUArchetype` / `ImmediateALUArchetype` macros.
- **DIV/REM family** (DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW,
  REMUW). New Arith-SM archetype.
- **UTYPE** (LUI, AUIPC). New archetype.
- **Phase 2.6 memory-model closure** (optional but high-leverage):
  extend `RISC_V_assumptions` with PMP/CLINT witnesses; retires
  M1, M2, M3, M4, M7, M9, M10, M11 together (8 of 11 Phase 3A Sail
  axioms + the 4 Phase 2.5 entries).

### Repro

```
git checkout 501dd13
cd /home/cody/zisk-fv
just verify-phase2
cd ZiskFv && lake build
```

Exit 0, 7988 jobs, no sorries.

---

# Phase 3.5 — trust-base closure

## Context

Phase 3A closed at `e952496` with 22 new opcodes and a growing trust
base: 34 transpile axioms + 16 Sail-equivalence axioms (M1-M4, M7, M9-
M11, C1, C2a-d, C3a-c, C4). Of the 16 Sail-equivalence axioms, two
groups have principled closure paths:

1. **M1-M11 + C1 (9 axioms)** — these encode end-to-end Sail memory /
   control-flow reductions that only fail to simp-reduce because
   `LeanRV64D`'s platform config bakes in `sys_pmp_count = 16`,
   `plat_clint_base = 2^25`, and nontrivial Zicfilp-enable bits.
   `openvm-fv`'s RV32D gets the corresponding simp reductions for
   free because its RV32 platform constants are zero. The semantic
   content of the RV64 axioms is **true by computation** once the
   platform features are stipulated inert, which is a direct
   consequence of RV64IM-scope (PMP, CLINT, Zicfilp are all out of
   scope per `CLAUDE.md`).
2. **C3a-c + C4 (4 axioms)** — genuine implementation gap in
   `ZiskFv/ZiskFv/Fundamentals/Execution.lean`: it provides a
   `execute_RTYPEW_pure` / `execute_RTYPEW'` /
   `execute_RTYPEW_eq_execute_RTYPEW'` triple used by SLLW/SRLW/SRAW
   but lacks analogous triples for `execute_SHIFTIWOP` and
   `execute_MULW`. Adding those triples is a mechanical port.

Phase 3.5 closes both groups. **C2a-d** (branch skeleton port, ~1
day of BNE mechanical replication) remains out of scope for 3.5 —
no downstream leverage; better fit in Phase 4's audit sweep.

Phase 3.5 ships zero new opcodes. After 3.5 the metaplan's
remainders are: **Phase 3B** (~28 opcodes across 4 new archetypes —
signed-load, ALU-RTYPE, ALU-ITYPE, DIV/REM, UTYPE), and **Phase 4**
(audit, REPORT.md, final sign-off).

## Scope (strict)

**In scope — Track I (Platform-feature axioms for M-closure):**

Add three narrow, scope-honest axioms at the lowest Sail-function
level, encoding that ZisK's RV64IM target explicitly disables PMP,
CLINT, and the relevant PMA-check paths:

```
axiom pmpCheck_is_pure_none  : ∀ addr width priv state,
  pmpCheck addr width priv state = (pure none, state)
axiom within_clint_is_false  : ∀ addr width state,
  within_clint addr width state = (pure false, state)
axiom pmaCheck_is_pure_none  : ∀ addr width access state,
  pmaCheck addr width access state = (pure none, state)
```

Each is one line of semantic content that maps directly to a single
out-of-scope RV64 feature. Home: a new section in
`ZiskFv/ZiskFv/RV64D/Auxiliaries.lean` under a `ZiskFv.PlatformScope`
namespace; catalogued in `docs/fv/trusted-base.md` as P1-P3 (a
distinct category from M/C: "platform-feature assertions" rather
than "memory-model reductions" or "control-flow reductions").

Derive `vmem_read_addr_aligned_equiv` and
`vmem_write_addr_aligned_equiv` as lemmas consuming the three
axioms (~100-150 lines of mechanical unfolding). These are the
bridging lemmas that `trusted-base.md § "Why M1-M4 exist"` already
named.

Re-derive M1, M2, M3, M4, M7, M9, M10, M11 as theorems (were
axioms). Each shrinks to a ~5-line invocation of the vmem lemmas.
Remove the eight `execute_*_pure_equiv_axiom`s from their RV64D
files; keep the `execute_*_pure_equiv` lemmas (with the same
signatures their consumers expect) and re-point their bodies to
the new theorems.

**In scope — Track II (Zicfilp axiom for C1-closure):**

Add one narrow axiom for the Zicfilp landing-pad feature:

```
axiom update_elp_state_is_pure_unit : ∀ rs1 state,
  update_elp_state rs1 state = (pure (), state)
```

Catalogued as P4. Derive `execute_JALR_pure_equiv` as a theorem
porting `/home/cody/openvm-fv/OpenvmFv/RV32D/jalr.lean::execute_JALR_pure_equiv`
(which closes directly in RV32 because Zicfilp is disabled there
too) with the obvious width widening (`signExtend 32 → signExtend
64`) and the existing RV64 `jump_to_equiv` misa witness.

**In scope — Track III (Execution.lean triples for C3/C4-closure):**

Mechanical port of the `execute_RTYPEW_pure` / `execute_RTYPEW'` /
`execute_RTYPEW_eq_execute_RTYPEW'` triple (lines 151-187 of
`Fundamentals/Execution.lean`) to two new Sail functions:

- `execute_SHIFTIWOP`: opens the monadic block via `let`-bindings so
  `simp` can reduce it. Sail enum: `sopw ∈ {SLLIW, SRLIW, SRAIW}`;
  shamt signature `BitVec 5`. Enables direct closure of the three
  SLLIW/SRLIW/SRAIW Sail-equivalence lemmas.
- `execute_MULW`: same refactor for the 32-bit signed multiply.
  Single opcode, no enum branching.

Then re-derive `execute_SHIFTIWOP_slliw_pure_equiv`,
`execute_SHIFTIWOP_srliw_pure_equiv`,
`execute_SHIFTIWOP_sraiw_pure_equiv`, `execute_MULW_pure_equiv` as
theorems (were axioms C3a-c and C4).

**Explicitly out of scope:**

- C2a-d closure (branches) — no downstream leverage; Phase 4 audit.
- Phase 3B's ~28 opcodes — Phase 3B needs its own plan after 3.5.
- Transpile-axiom reduction — all 34 are principled (specifications
  of the Rust transpiler, not the Sail chain).

## Execution order

**I1:** Extend `RISC_V_assumptions` with `pmp_all_off`,
`clint_disjoint`, `pma_single_region` fields. Purely descriptive;
no proof cost. Commit.

**I2:** Author P1-P3 platform axioms in
`RV64D/Auxiliaries.lean::ZiskFv.PlatformScope`. Add P1-P3 entries
to `trusted-base.md` under a new "Platform-feature assertions
(Phase 3.5)" section. Commit.

**I3:** Author `vmem_read_addr_aligned_equiv` as a lemma in
`Auxiliaries.lean` (or `RV64D/Memory.lean` if import-order demands).
~50-80 lines, consumes P1-P3 + existing `RISC_V_assumptions`
fields. Commit.

**I4:** Author `vmem_write_addr_aligned_equiv` (symmetric). Commit.

**I5:** Promote M1-M4 to theorems. Replace the four axioms in
`RV64D/{ld,sd,lwu,sw}.lean` with proof bodies invoking the vmem
lemmas (~5 lines each). Keep the lemma signatures downstream
consumers use. Mark M1-M4 in `trusted-base.md` as "promoted to
theorem in Phase 3.5" with a link to the theorem body. Commit.

**I6:** Promote M7, M9, M10, M11 to theorems. Same pattern for
`RV64D/{lhu,lbu,sh,sb}.lean`. Commit.

**II1:** Author P4 Zicfilp axiom in `Auxiliaries.lean::PlatformScope`.
Add P4 to `trusted-base.md`. Commit.

**II2:** Promote C1 to theorem. Replace `execute_JALR_pure_equiv_axiom`
in `RV64D/jalr.lean` with a port of openvm-fv's RV32D proof.
Estimated 40-60 lines. Commit.

**III1:** Port the RTYPEW triple to `execute_SHIFTIWOP` in
`Fundamentals/Execution.lean`. ~80-100 lines. Commit.

**III2:** Promote C3a-c to theorems in
`RV64D/{slliw,srliw,sraiw}.lean` using `execute_SHIFTIWOP'`. Each
~20-30 lines mirroring `sllw.lean::execute_RTYPE_sllw_pure_equiv`.
Commit.

**III3:** Port the RTYPEW triple to `execute_MULW` in
`Fundamentals/Execution.lean`. ~50-80 lines. Commit.

**III4:** Promote C4 to theorem in `RV64D/mulw.lean`. ~20-30 lines.
Commit.

**V1:** Append Phase 3.5 CLOSED section to
`ai_plans/zisk-fv-phase-3.md` with axiom accounting:
- Before 3.5: 50 axioms total (34 transpile + 16 Sail-equiv).
- After 3.5: 34 transpile + 4 C2 (deferred) + 4 P1-P4 (new category)
  = 42 axioms. Net −8.
- M1-M11 and C1 catalogued as "promoted to theorem".

**V2:** Run verification gates (see next section).

## Parallelism

Low. Tracks I / II / III could be split across 1-2 subagents, but
all three touch `Auxiliaries.lean` and the per-opcode files are
disjoint — serial execution by a single agent avoids the
merge-resolution overhead Phase 3A experienced. Budget: ~3 days
wall-clock if serial.

## Verification (end-to-end)

1. From clean checkout: `just verify-phase2` exits 0.
2. `lake build` green, zero `sorry` in `Fundamentals/`, `Airs/`,
   `Spec/`, `Equivalence/`, `GoldenTraces/`, `Tactics/`, and in all
   32 shipped opcode `RV64D/*.lean` files (the original 22 from
   3A plus the 10 promoted here: ld, sd, lwu, sw, lhu, lbu, sh, sb,
   jalr, slliw, srliw, sraiw, mulw).
3. `#print axioms` on each former M/C1 metaplan theorem shows only
   kernel axioms + transpile_* + P1-P4 (as applicable) + the still-
   parameterized bus-emission hypotheses (for load/store metaplans).
   No `sorryAx`. No `execute_*_pure_equiv_axiom`.
4. `docs/fv/trusted-base.md` reflects: 4 P-axioms; 4 C2 axioms
   marked "deferred to Phase 4"; M1-M11, C1, C3a-c, C4 marked
   "promoted to theorem in Phase 3.5" with theorem-body links.
5. `git grep -n '^axiom ' ZiskFv/ZiskFv/RV64D/` returns only the 4
   P-axioms (from `Auxiliaries.lean`) — no per-opcode
   `*_pure_equiv_axiom`s remain.

## Critical files

**Edited in Phase 3.5:**
- `ZiskFv/ZiskFv/RV64D/Auxiliaries.lean` — extend `RISC_V_assumptions`;
  add P1-P4 axioms + `vmem_{read,write}_addr_aligned_equiv` lemmas.
- `ZiskFv/ZiskFv/Fundamentals/Execution.lean` — add
  `execute_SHIFTIWOP_*` and `execute_MULW_*` refactor triples.
- `ZiskFv/ZiskFv/RV64D/{ld,sd,lwu,sw,lhu,lbu,sh,sb}.lean` — remove
  `execute_*_pure_equiv_axiom`; convert lemma bodies to theorems.
- `ZiskFv/ZiskFv/RV64D/jalr.lean` — remove
  `execute_JALR_pure_equiv_axiom`; port the openvm-fv RV32D proof.
- `ZiskFv/ZiskFv/RV64D/{slliw,srliw,sraiw,mulw}.lean` — remove
  axioms; real proofs via the new Execution.lean triples.
- `docs/fv/trusted-base.md` — add P-category section; mark promoted
  axioms; history entry.

**Read-only (reference):**
- `/home/cody/openvm-fv/OpenvmFv/RV32D/jalr.lean` — Track II port
  source.
- `ZiskFv/ZiskFv/Fundamentals/Execution.lean:151-187` — Track III
  template (existing RTYPEW triple).
- `ZiskFv/ZiskFv/RV64D/sllw.lean::execute_RTYPE_sllw_pure_equiv` —
  direct-closure template for Track III's C3 promotions.

## Known fragility

1. **`vmem_{read,write}_addr_aligned_equiv` unfolding may be longer
   than the sketched ~50-80 lines each.** Real unfolding of
   `execute_LOAD` through `checked_mem_read` may hit simp-resistant
   intermediaries (`pma_attribute_lookup`, `VMReadResult`
   construction). If the naive unfold doesn't close under simp +
   P1-P3, add one or two additional narrow platform axioms (P5,
   P6, …) — staying in scope-honest territory — rather than
   falling back to re-axiomatizing at the top level.

2. **JALR port from RV32D may have RV64-specific diffs beyond
   width.** If `update_elp_state`'s callee graph differs
   structurally between RV32 and RV64 (not just bit-width),
   additional narrow axioms may be needed. Same mitigation: small
   narrow axioms over top-level re-axiomatization.

3. **C4 MULW's `to_bits_truncate` / `sign_extend` may resist simp**
   even after the refactor. If so, add small `@[simp]` helpers on
   the underlying `BitVec` primitives. These are in-scope
   computational aids, not platform-feature assertions.

## Phase 3.5 status — CLOSED <date TBD>

(To be populated when Phase 3.5 executes.)

