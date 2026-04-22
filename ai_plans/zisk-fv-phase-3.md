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

## Phase 3A status — CLOSED <date TBD>

(To be populated when Phase 3A executes.)
