# Phase 2 detailed plan — archetype coverage

**Parent metaplan.** `ai_plans/zisk-fv-metaplan.md` (Phase 2 section,
under the 2026-04-22 post-Phase-1.5 revision).

## Context

Phase 1 + 1.5 shipped the complete ADD vertical slice (`equiv_ADD`
circuit-level, `equiv_ADD_sail` Sail-level, `equiv_ADD_metaplan` in the
metaplan target shape) and all the reusable infrastructure the
metaplan anticipated:

- `Fundamentals/{Goldilocks,PrattCertificate,Transpiler,Execution,
  U64,Interaction,GoldilocksBridge}.lean` — field + Sail + bus +
  bridge machinery.
- `Airs/{Main,Binary/BinaryAdd,OperationBus}.lean` — named-column
  `Valid_<AIR>` structures with the ADD-subset constraints.
- `RV64D/{add,BusEffect,Auxiliaries}.lean` — Sail-side entry points.
- `codygunton/sail-riscv-lean@ext-zca-simp-lemmas` fork consumed for
  `currentlyEnabled Ext_Zca` reductions.
- Harness + fixture + `verify-phase1` gate.

Phase 2 spends that infrastructure: one representative opcode per
**proof archetype**, each yielding a zero-`sorry` theorem, a
golden-trace fixture, a reusable proof macro, and an archetype
doc. Phase 3 fans out over the long tail using those macros.

The metaplan chose six archetypes. Two pre-execution observations
shape the task order:

1. **ZisK's microinstruction IR may reshape some archetypes.** RV64
   `BEQ` doesn't have a direct Zisk opcode; the RV→Zisk transpiler
   (`vendor/zisk/core/src/riscv2zisk_context.rs`) emits Zisk
   microinstruction sequences for branches, not 1:1 ops. This was
   not audited in Phase 1 (ADD maps cleanly to `OP_ADD = 0x0A`).
   The first branch-archetype task is therefore investigation:
   *which* Zisk microinstruction(s) does BEQ transpile to, and
   which Main AIR constraints + bus entries cover the branch
   semantics? openvm-fv's direct `BranchEqual` spec is the proof
   template, but the Zisk-side mapping is unknown territory.
2. **Deriving `h_bus_execute_matches_sail` is net-new Phase 2
   scope.** `equiv_ADD_metaplan` parameterizes over this hypothesis
   today; every Phase 2 archetype needs to either (a) derive it
   from a more elementary PIL-level bus-emission spec, or (b)
   continue parameterizing and push the derivation to Phase 4
   audit. Decision belongs to the BEQ task (since BEQ is the first
   opcode whose bus-effect shape differs from ADD's).

Secondary cleanup:

3. **Simp-race redundancy.** `Auxiliaries.lean` has a local
   `@[simp high] currentlyEnabled_Zca_of_misa_val` that wins the
   simp race against the imported `LeanRV64D.Lemmas` version. Either
   retire the local helper (canonicalize on the upstream path) or
   demote the upstream import to an `anchor` — decide during the
   branch archetype which delivers a cleaner proof.

## Scope (strict)

**In scope (six archetypes, in task order):**

- **A1 (Branch): BEQ.** Purpose: prove the first PC-mutating
  archetype end-to-end + establish a branch-proof macro. Delivers:
  `Spec/BranchEqual.lean`, `Equivalence/BranchEqual.lean`,
  `Airs/Binary/<TBD>.lean` or `Airs/Main.lean` extensions for
  branch-specific Main constraints, `GoldenTraces/BEQ.lean`,
  a branch archetype macro, `docs/fv/archetype-branch.md`.
- **A2 (Jump+link): JAL.** Purpose: PC-mutating + register write,
  no memory, no bus call to a secondary SM.
- **A3 (Load): LD.** Purpose: RV64 8-byte memory read via the
  memory bus, register write, sign/zero extension. Exercises
  `Fundamentals/Interaction.lean`'s `MemoryBusEntry` end-to-end.
- **A4 (Store): SD.** Purpose: RV64 8-byte memory write, no
  register write.
- **A5 (Arith SM): MUL.** Purpose: distinct secondary state
  machine (Arith, not Binary). Requires `Airs/Arith/Mul.lean`
  counterpart to `Airs/Binary/BinaryAdd.lean`.
- **A6 (-W family): SLLW.** Purpose: validate RV64 sign-extension-
  of-32-bit-result + the `m32 = 1` operation-bus path that
  Phase 1.5 Track M enabled but which no opcode has exercised yet.

**In scope (cross-cutting):**

- **Bus-emission correctness (B1).** Decide whether to derive
  `h_bus_execute_matches_sail` from PIL-level bus-emission during
  BEQ archetype work, or keep it parameterized through Phase 2 and
  address in Phase 4. If derived: build it as a reusable lemma
  set in `Airs/OperationBus.lean` or a new `Airs/BusEmission.lean`.
- **Simp-race cleanup (C1).** Decide during BEQ archetype; act on
  decision before the archetype lands.
- **Non-ADD RV64IM opcode equivalences (the 43 `sorry`s from
  Phase 1's Track A).** Partially opportunistic: where an archetype
  naturally closes a family (e.g. A1 should close the other 5
  branches via macro fan-out), do so. This is **not** the Phase 3
  long-tail sweep — that stays separate.
- **Archetype macros.** Each archetype produces a macro parametric
  over opcode name, opcode value, and operand signature (mirroring
  openvm-fv's `alu_non_imm_proof` pattern).
- **Golden-trace matrix extension.** Each archetype gets one
  fixture in `GoldenTraces/`; per-opcode fixtures from fan-out
  move to Phase 3.
- **`justfile::verify-phase2` target.** Runs verify-phase1 + per-
  archetype `lake build` + `#eval` fixture checks.

**Explicitly out of scope:**

- Phase 3 long-tail (the ~60 remaining opcodes after archetype
  macros land).
- Phase 4 audit (lint script, trusted-base review, report).
- Any compressed / floating-point / CSR / vector opcodes.
- Zicclsm (per metaplan locked decision).
- Filing the U1 upstream issue on `sail-riscv-lean` (user-gated;
  see CLOSED section of Phase 1).
- Fixing the upstream C++ `#include <cstdint>` blocker for the
  harness `--features live` path (outside our code).
- Proving additional metaplan theorems for archetypes beyond what
  the macro produces (they're derivable; proving them is Phase 3
  fan-out).

## Pre-execution reconnaissance

Populated during BEQ task (A1-R below). The key unknowns:

1. **ZisK transpiles BEQ to which microinstruction(s)?** Expected
   from `vendor/zisk/core/src/riscv2zisk_context.rs`
   (`create_branch_op` or similar). Output: the Zisk `op` value(s)
   BEQ produces, the flag/offset fields, PC next-value handling.
2. **Which Main AIR constraints gate branching?** The ADD work
   touched 8 constraints (`main.pil` subset indices
   8,9,15,16,17,18,19,24,30). Branch path indices: unknown;
   extract with `zisk-pil-extract --list-constraints Main`.
3. **Does BEQ hop the operation bus?** If yes, to what secondary
   state machine, and what opcode ID? (If no, BEQ closes without
   the `opBus_row_Main` / `matches_entry` machinery.)
4. **Does BEQ's transpilation depend on `is_external_op` /
   `is_precompiled`?** If no bus hop, `is_external_op = 0` and the
   Main-row proof closes without involving BinaryAdd/Arith.
5. **Are there any Main AIR constraints that gate PC differently
   from `STEP` increment?** `main.pil:393-404` is the row-to-row
   PC handshake; need to verify it handles branch-taken/not-taken
   consistently.

openvm-fv analogue read: `/home/cody/openvm-fv/OpenvmFv/Spec/
BranchEqual.lean`, `/home/cody/openvm-fv/OpenvmFv/Equivalence/
BranchEqual.lean`, `/home/cody/openvm-fv/OpenvmFv/RV32D/beq.lean`,
`/home/cody/openvm-fv/OpenvmFv/Equivalence/Equivalence.lean`
(archetype macro site).

## Execution order

### Archetype A1 — BEQ (serial, first)

**A1-R: Reconnaissance.** Read the openvm-fv analogues (3 files
above). Trace `core/src/riscv2zisk_context.rs` for the RV64 BEQ →
Zisk microinstruction mapping. Run `zisk-pil-extract --air Main
--list-constraints` to enumerate branch-relevant Main constraints.
Write a <300-word section at the end of this file under
"Reconnaissance A1" recording the findings before proceeding.

**A1-E: Extend `Airs/Main.lean` for branch constraints.** Add
named-predicate analogues of the branch-gated Main constraints to
the existing `Valid_Main` structure (or a thin extension). Write
`constraint_N_of_extraction` bridges.

**A1-B: Bus-emission decision (B1).** If BEQ does *not* hop the
bus (expected for branches), keep `h_bus_execute_matches_sail`
parameterized. If BEQ *does* hop (contrary to expectation), prove
it and the decision about PIL-level derivation begins here. Log
the decision in this plan.

**A1-T: Axiomatize `transpile_BEQ`.** Add a case to
`ZiskFv/Fundamentals/Transpiler.lean` mirroring `transpile_ADD`'s
shape, citing `core/src/riscv2zisk_context.rs`.

**A1-S: `Spec/BranchEqual.lean`.** Compositional theorem:
given the branch-gated Main constraints + PC handshake + register
reads, either PC advances by 4 or branches to `pc + imm`.

**A1-RV64D: Close `RV64D/beq.lean` equivalence.** The file has
the pure spec and a `sorry` on the Sail equivalence. Close it
using `jump_to_equiv` (now unblocked) + Sail branch semantics.

**A1-E2E: `Equivalence/BranchEqual.lean`.** Final theorem
`equiv_BEQ` in the metaplan shape. If B1 chose derivation, the
theorem has no `h_bus_execute_matches_sail`-style parameterization;
otherwise carries it parallel to `equiv_ADD_metaplan`.

**A1-M: Branch archetype macro.** Extract common proof structure
from BEQ so BNE/BGE/BGEU/BLT/BLTU fan out via macro instantiation.
Write to a new `Tactics/BranchArchetype.lean` (or similar). Document
at `docs/fv/archetype-branch.md` (≤300 lines): macro call shape,
archetype assumptions, per-opcode parameters.

**A1-F: Golden-trace fixture for BEQ** in `GoldenTraces/BEQ.lean`.

**A1-V: Checkpoint.** `just verify-phase2` passes with BEQ. Commit.

**A1-CLEAN: Simp-race cleanup (C1).** Act on the decision from
earlier — either remove the local `currentlyEnabled_Zca_of_misa_val`
helper or restructure the import path.

### Archetypes A2-A6 (parallel fan-out, one subagent per archetype)

Each follows A1's task shape (R / E / T / S / RV64D / E2E / M /
F / V), adapted to the archetype. Expected tasks per archetype:

- **A2 (JAL):** no bus hop (like BEQ); exercises register-write +
  PC-mutation. Likely ~1 day post-A1-M.
- **A3 (LD):** memory-bus hop. **New infrastructure needed:**
  proof machinery for `MemoryBusEntry` matching against Main's
  memory-op constraints. Budget: ~3 days; this is the Phase 2
  "memory archetype" equivalent of Phase 1's "compositional Main+
  Binary proof" risk point.
- **A4 (SD):** symmetric to A3; closes fast after A3 lands.
- **A5 (MUL):** requires `Airs/Arith/Mul.lean` mirroring
  `Airs/Binary/BinaryAdd.lean`. Extract the Arith AIR subset with
  `zisk-pil-extract --air Arith --only <mul-subset>`. Budget:
  ~2 days.
- **A6 (SLLW):** `m32 = 1` operation-bus path. Exercises Track M
  code untouched since Phase 1.5. Budget: ~1.5 days (includes
  auditing the `(1 - 1) * x = 0` simp path).

### Cross-cutting (after A1, parallel with A2-A6)

**B1-derive:** If A1-B chose "derive PIL-level bus emission", land
it as a `Airs/BusEmission.lean` module. All prior-existing metaplan
theorems (`equiv_ADD_metaplan`, plus what A1-A6 produce) lose their
`h_bus_execute_matches_sail` parameter and become self-contained.

**Phase 2 status — CLOSED** section to be appended here on close.

## Verification (end-to-end)

Phase 2 is complete iff `just verify-phase2` exits 0. Specifically:

1. `verify-phase1` continues to pass (regression gate).
2. Each of A1-A6 has `equiv_<OPCODE>` exported, zero `sorry` in the
   archetype's own Spec/Equivalence/RV64D files (other RV64D files
   may still carry per-opcode `sorry`s pending Phase 3).
3. Each archetype has a golden-trace fixture with `#eval` check.
4. Six `docs/fv/archetype-*.md` files exist.
5. `git grep -n 'sorry' ZiskFv/Fundamentals ZiskFv/Airs ZiskFv/Spec
   ZiskFv/Equivalence ZiskFv/GoldenTraces ZiskFv/Tactics` — zero
   matches.
6. `lake build` green across full package.

## Known fragility

- **A1-B decision (derive `h_bus_execute_matches_sail` now, or
  defer).** Deriving is substantial proof work. Deferring leaves
  every Phase 2 archetype parameterized, pushing a uniform audit to
  Phase 4. Budget 1 day on A1-R to inform the choice.
- **A3 memory-bus proof is the likeliest deep risk.** The
  `MemoryBusEntry` shape is exercised end-to-end for the first time;
  expect to discover missing lemmas in
  `Fundamentals/Interaction.lean` or `BusEffect.lean`. Budget
  +2 days if friction hits early.
- **Archetype macros may leak across archetypes.** If `beq_proof`'s
  macro needs information only derivable after JAL is proven, the
  archetype partition is wrong. Re-partition rather than shoehorn.
- **A5 needs Arith AIR extraction.** `zisk-pil-extract` supports
  Main + BinaryAdd today; Arith AIR is likely similar shape but
  extractor may need another operand-kind pass. Budget +1 day if
  extraction surfaces new kinds.
- **Track A's 43 remaining `sorry`s.** Phase 2 is **not** a long-
  tail sweep. Close a `sorry` only when an archetype naturally
  does. Explicitly skip the rest — they are Phase 3's scope.
- **Upstream C++ starks-lib-c blocker.** Harness `--features live`
  stays unusable end-to-end throughout Phase 2. Not a blocker for
  the proof work itself. If harness live-mode becomes load-bearing
  for any archetype's fixture, downgrade to `--mode golden`.

## Decisions captured (reversible but preferred)

- **BEQ first, other archetypes via subagent fan-out.** Same
  serial-BEQ-then-parallel pattern as Phase 2's metaplan section
  prescribes. Validates macro discipline before fanning out.
- **Proof macros are the archetype deliverable, not just the
  theorem.** A theorem without a reusable macro isn't a closed
  archetype — Phase 3 depends on the macros.
- **`h_bus_execute_matches_sail` decision deferred to A1-B.** Don't
  pre-commit.
- **Simp-race cleanup folded into A1-CLEAN.** Avoid a separate
  housekeeping task when it's naturally decided by the branch
  archetype's proof structure.
- **No new operand kinds in `zisk-pil-extract` unless A5 forces
  it.** Extractor stays feature-frozen through most of Phase 2.

## Parallelism overview

Rough. Archetype work dominates; other items fit in around it.

- **Serial prereq:** A1 (BEQ) end-to-end — 1–2 weeks.
- **Fan-out (after A1-M lands):** A2, A3, A4, A5, A6 in parallel,
  one subagent per archetype. A4 depends on A3's memory-bus
  machinery.
- **Cross-cutting:** B1 (if elected) runs parallel with A2-A6.

## Critical files to read / reference

- **Phase 1 closure context:** `ai_plans/zisk-fv-phase-1.md` Round 2
  addendum.
- **Metaplan:** `ai_plans/zisk-fv-metaplan.md` (Phase 2 section + 2026-04-22 revision).
- **Transpiler source:** `vendor/zisk/core/src/riscv2zisk_context.rs`
  (branch + jump + load + store + mul cases).
- **Main PIL:** `vendor/zisk/state-machines/main/pil/main.pil`
  (branch/jump gating, PC handshake).
- **Opcode ID table:** `vendor/zisk/pil/operations.pil`.
- **openvm-fv archetype templates:** `/home/cody/openvm-fv/OpenvmFv/
  Spec/{BranchEqual,JalR,JalLui,LoadW,StoreW,Mul,Shift}.lean` and
  corresponding `Equivalence/` entries.
- **openvm-fv macro site:** `/home/cody/openvm-fv/OpenvmFv/
  Equivalence/Equivalence.lean` (contains `alu_non_imm_proof` and
  similar — archetype macro reference shapes).
- **zisk-fv present RV64D starters:** `ZiskFv/RV64D/{beq,jal,ld,sd,
  mul,sllw}.lean` — pure specs in place, equivalences at `sorry`.

---

## Phase 2 status — CLOSED <date TBD>

(To be populated when Phase 2 executes.)
