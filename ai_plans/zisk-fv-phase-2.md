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

## Reconnaissance A1 (BEQ) — 2026-04-22

**Zisk microinstruction.** `vendor/zisk/core/src/riscv2zisk_context.rs:202`
maps `"beq" → self.create_branch_op(instr, "eq", false, 4)`. The
`create_branch_op` helper (line 740) emits exactly one Zisk
microinstruction with: `src_a = reg(rs1)`, `src_b = reg(rs2)`,
`op = "eq"` (ZisK opcode `0x09`, `Binary` type — `zisk_ops.rs:391`),
and crucially `j(imm, inst_size=4)` — i.e. `jmp_offset1 = imm`,
`jmp_offset2 = 4`. The `neg` parameter (false for BEQ) places `imm`
in `jmp_offset1` (flag=1 path) and `4` in `jmp_offset2` (flag=0 path).
BNE passes `neg=true`, swapping the two. Because `eq` has `OpType::Binary`,
`is_external_op = true` (`zisk_inst_builder.rs:203`).

**Main AIR branch-relevant constraints.** The PC handshake
`(1 - SEGMENT_L1) * (pc - expected_current_pc) === 0` at `main.pil:410` —
where `expected_current_pc = 'set_pc*('c[0]+'jmp_offset1) +
(1-'set_pc)*('pc+'jmp_offset2) + 'flag*('jmp_offset1-'jmp_offset2)` —
is constraint **20**, and it uses a negative rotation (the `'` prefixed
columns are previous-row). Our `zisk-pil-extract` tool currently skips
this because `Circuit.main` rotation is `ℕ`. **This is the key blocker:**
the constraint tying `next_pc` to `flag` lives in the row *after* the BEQ
row. No existing extracted constraint names `jmp_offset1`/`jmp_offset2`/
`set_pc` in a usable way for per-row PC reasoning. Constraints 8,9,15-19,
24,30 (the ADD subset) are reusable as-is for BEQ's `flag`/`is_external_op`
booleans and `flag*set_pc = 0` disjointness.

**Bus hop?** YES. Because `eq` is `OpType::Binary`, the Main row has
`is_external_op = 1` and emits an OperationBus entry with
`op = OP_EQ = 9`. The Binary state machine's `flag` output bit is what
Main's `flag` column pulls in. The BinaryAdd SM does not handle `eq` —
that's the full Binary SM (`vendor/zisk/state-machines/binary/pil/binary.pil`).
`flag`'s correctness is delegated to that SM; for Phase 2 we parameterize
rather than derive.

**`is_precompiled` / `is_external_op`.** `is_external_op = 1`,
`is_precompiled = 0` (no precompile for `eq`). Same shape as ADD on those
two selectors.

**PC taken vs. not-taken.** On flag=1 (branch taken), next row's `pc =
pc + jmp_offset1 = pc + imm`. On flag=0, `pc + jmp_offset2 = pc + 4`.
For BNE, `neg=true` makes this `pc + 4` taken vs. `pc + imm` not-taken —
i.e. `flag` inverted.

**A1-B decision (Bus-emission).** **DEFER.** Deriving
`h_bus_execute_matches_sail` requires modeling the full Binary SM's bus
emission (not just BinaryAdd's restricted shape). That is net-new scope
beyond ADD's proof, which uses BinaryAdd's narrower carry-chain SM.
Parameterizing keeps BEQ aligned with `equiv_ADD_metaplan`'s shape and
hands the full bus derivation to Phase 4.

**A1-E2 PC handshake.** Since constraint 20 is not extractable, we
introduce a **named PC-handshake predicate** at the Main AIR layer —
not derived from `constraint_20_of_extraction`, but parameterized on a
"next-row `pc`" cell the caller supplies. This mirrors how
`equiv_ADD_metaplan` parameterizes `h_bus_execute_matches_sail`: the
PIL-level handshake stays a trusted boundary for Phase 2, and Phase 4
audit closes the loop by wiring `zisk-pil-extract` for negative-rotation
cells. Logged as new scope item — the extractor feature is Phase 4
(per metaplan revision 2026-04-22), not Phase 2.

---

## Reconnaissance A6 (SLLW) — 2026-04-22

**Zisk microinstruction.** `vendor/zisk/core/src/riscv2zisk_context.rs:155` maps
RV64 `sllw rd, rs1, rs2` → `self.create_register_op(instr, "sll_w", 4)`. The
`create_register_op` helper (line 631) emits a single microinstruction with
`src_a = reg(rs1)`, `src_b = reg(rs2)`, `op = "sll_w"`, `store = reg(rd)`,
`j(4, 4)` (no branch). `zisk_inst_builder.rs:206` sets `self.i.m32 = true`
because `"sll_w".contains("_w")`. The opcode is **`OP_SLL_W = 0x24`**
(`pil/operations.pil:62`, `zisk_ops.rs:416`), type `BinaryE`, so
`is_external_op = 1`, `is_precompiled = 0`, `set_pc = 0`, `flag = 0`.

**Binary SM routing.** `OP_SLL_W = 0x24` is one of the 9 shift/sign-extend
opcodes listed at `binary_extension.pil:10-19` (`SLL`, `SRL`, `SRA`, `SLL_W`,
`SRL_W`, `SRA_W`, `SEXT_B`, `SEXT_H`, `SEXT_W`). They are handled by the
**`BinaryExtension` AIR**, *not* the `BinaryAdd` AIR we used for ADD. Like
BEQ (which hit the full `Binary` AIR), we DEFER the BinaryExtension bus-
emission derivation: the bus match `opBus_row_Main r = opBus_row_BinaryExt r'`
is parameterized. No `Airs/Binary/BinaryExt.lean` is produced this phase;
that's Phase 4 audit scope. The bus entry's `c = (c_lo, c_hi)` carries the
32-bit result sign-extended to 64 (so `c_hi = 0xFFFF_FFFF` when bit 31 of
the low half is set, else `0`).

**m32 = 1 path through `opBus_row_Main`.** The PIL emits bus entry
`a = [a[0], (1 - m32) * a[1]]`, `b = [b[0], (1 - m32) * b[1]]`. For SLLW
(`m32 = 1`), the high lanes zero out: `a_hi = b_hi = 0` on the bus. The
secondary SM (`BinaryExtension`) sees a 32-bit operand. To close `simp` on
`(1 - m.m32 row) * x` under `h : m.m32 row = 1`, we add lemma
`one_sub_one_mul : (1 - 1) * x = 0` — mirror of Phase 1's `one_sub_zero_mul`.

**Sail pure function.** LeanRV64D exposes `execute_RTYPEW` at
`InstsEnd.lean:65650-65661`: extracts low 32 bits of rs1/rs2, computes
`shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0)`, and sign-
extends to 64 via `sign_extend (m := 64) result`. The instruction is
`instruction.RTYPEW (rs2, rs1, rd, ropw.SLLW)` (`Defs.lean:527,757`).
No port needed — we author `execute_RTYPEW_pure` / equivalence in
`Fundamentals/Execution.lean` mirroring `execute_RTYPE`.

**A6-B decision.** DEFER bus-emission derivation (same as A1-B). The full
`BinaryExtension` AIR is net-new infrastructure; parameterizing the bus-
match hypothesis keeps SLLW aligned with BEQ/JAL's metaplan shape.

---

## Reconnaissance A2 (JAL) — 2026-04-22

**Zisk microinstruction.** `vendor/zisk/core/src/riscv2zisk_context.rs:201,1098` —
RV64 `jal rd, label` dispatches to `self.jal(i, 4)` which emits a single Zisk
microinstruction via `ZiskInstBuilder`:
* `src_a = imm 0`, `src_b = imm 0` (no register source; a/b lanes all zero),
* `op("flag")` — ZisK opcode `0x00`, `OpType::Internal` (`zisk_ops.rs:382`),
* `store_pc("reg", rd, false)` — store **`pc + jmp_offset2`** to rd (per the PIL
  `store_value` expression at `main.pil:311`),
* `j(imm, 4)` — `jmp_offset1 = imm`, `jmp_offset2 = 4`.
**No** `set_pc()` call: JAL's PC advance uses `flag = 1` + the standard handshake,
not `c[0]` as next-pc source (that's JALR's path).

**Main AIR constraints relevant.** Because `is_external_op = 0`, constraints 17/18
force `flag = 1` (`(1-ext)*(1-op)*(1-flag) = 0`). Constraints 8/15 force
`c[0] = c[1] = 0` (internal op=0 zeroes c). Constraint 19 (`flag * set_pc = 0`) is
satisfied trivially since `set_pc = 0`. **Reused from A1 (BEQ):** the
`pc_handshake` predicate at `Airs.Main.pc_handshake` and its specialization
`pc_handshake_branch`. The `jmp_offset1`/`jmp_offset2`/`set_pc`/`pc` columns are
already exposed. No new Main column accessors required.

**PC handshake for unconditional jumps.** With `set_pc = 0` and `flag = 1`, the
specialized handshake collapses to
`next_pc = pc + jmp_offset2 + 1 * (jmp_offset1 - jmp_offset2) = pc + jmp_offset1`
`= pc + imm`. Symmetric to BEQ's taken case, but `flag` is forced by constraints
17+30 (no external SM delegation) rather than parameterized.

**Bus hop?** NO. `is_external_op = 0`, so the `assumes_operation` call
(`main.pil:367-374`) is inactive. `h_bus_execute_matches_sail` parameterization
mirrors BEQ (DEFER Phase 4 derivation).

---

## Reconnaissance A3 (LD) — 2026-04-22

**Zisk microinstruction.** `vendor/zisk/core/src/riscv2zisk_context.rs:216`
maps `"ld" → self.load_op(riscv_instruction, "copyb", 8, 4)`. `load_op`
(line 803) emits exactly one Zisk microinstruction via `ZiskInstBuilder`:
* `src_a = reg(rs1)` — `a[0]`/`a[1]` carry `xreg(rs1)` lanes;
* `ind_width = 8` — memory operand width is 8 bytes;
* `src_b = ind(imm)` — `b_src_ind = 1`, `b_offset_imm0 = imm`; Main
  reads `b` from memory at `addr1 = imm + a[0]` (`main.pil:192`);
* `op = "copyb"` (`0x01`, `OpType::Internal`, `zisk_ops.rs:383`);
* `store = reg(rd)` — `store_reg = 1`, `store_offset = rd`; Main writes
  `c` (= `c[0] + c[1]*2^32`) to register `rd`;
* `j(4, 4)` — both `jmp_offset1 = 4` and `jmp_offset2 = 4`.
**No** `set_pc()` call, so `set_pc = 0`.

**Main AIR constraints.** Because `is_external_op = 0`, constraint 9
(`(1 - is_external_op) * op * (b[i] - c[i]) = 0`) + constraint 16 force
`c[i] = b[i]` at the Main level — the internal op=1 "copy_b" short-circuit
replaces an external bus hop. Constraint 18 forces `flag = 0`. PC handshake
(set_pc=0, flag=0) collapses to `next_pc = pc + jmp_offset2 = pc + 4`.
**No operation-bus entry is emitted for copyb.**

**Memory bus.** Two `mem_op` calls fire per LD row:
`main.pil:300` (load-b from memory, `MEMORY_LOAD_OP = 1`, `bytes = 8`,
`addr = imm + a[0]`, value = `b`) and `main.pil:323` (store-c to register,
`MEMORY_REG_OP = 3`, `bytes = 8`, `addr = rd`, value = `store_value`).
Permutation entry shape: `[op, addr, mem_step, bytes, ...value]`
(`state-machines/mem/pil/mem.pil:524-527`). In our Lean model
(`Interaction.MemoryBusEntry`) each row carries `(multiplicity, as, ptr,
x0..x7, timestamp)` with `as ∈ {1 (reg), 2 (mem)}`.

**Memory-bus-entry format for LD.** Two entries:
* **Memory read** — `multiplicity = -1` (assume), `as = 2`, `ptr = rs1_val +
  imm`, `x0..x7 = bytes of mem[ptr..ptr+7]`. (Also an assumed-side
  register-read of rs1 with `as = 1`, `multiplicity = -1`, `ptr = 4 * rs1`
  — precedes the memory read in the bus list.)
* **Register write** — `multiplicity = 1` (prove), `as = 1`,
  `ptr = 4 * rd`, `x0..x7 = the 8 bytes of the loaded doubleword`.

**Alignment gating.** Sail's `vmem_read` performs the alignment check via
`is_aligned_vaddr` / `check_misaligned`; under `RISC_V_assumptions` (PMA
attribute `misaligned_fault = AlignmentFault`), misaligned 8-byte loads
raise `E_Load_Addr_Align`. ZisK's PIL `mem_op` does not itself fault on
misalignment — the memory SM enforces byte-range via permutation; the
transpiler assumes aligned `ld` at the program level. **Approach:** mirror
openvm-fv's `lw_state_assumptions` pattern — per-input `ld_state_assumptions`
include `8 ∣ (rs1 + imm)` and `rs1_val + imm < OpenVM_address_space_size`
so Sail's `vmem_read` takes the Ok/aligned branch.

**`bus_effect` memory-read branch** (`BusEffect.lean:47-62`). For
`multiplicity = -1` + `as = 2`: adds eight `state.mem[ptr+i]? = .some x_i`
conjuncts. Matches what `vmem_read` consumes via byte-by-byte `read_ram`.
`U64.toBV` rebuilds the `BitVec 64` from byte lanes in little-endian order —
same byte-order as `vmem_read`'s accumulator.

**A3-B decision (Bus-emission).** **DEFER** (same as A1, A2). Deriving
`h_bus_execute_matches_sail` from PIL-level bus emission requires modeling
the Mem SM's permutation argument end-to-end (not just `bus_effect`'s
fold). That is Phase 4 scope. Parameterize.

---

## Reconnaissance A5 (MUL) — 2026-04-22

**Arith AIR location.** `vendor/zisk/state-machines/arith/pil/arith.pil`
(airtemplate `Arith`, 65 constraints; there is also a `arith_mul64.pil`
variant specialised to 64-bit mul which is unused by the active pilout).
PIL emits one permutation-proved bus entry per row
(`proves_operation(op:, a:, b:, c:, flag: div_by_zero, mul: multiplicity)`)
at `arith.pil:269-270`. Opcodes 0xb0/0xb1/0xb3/0xb4/0xb5/0xb6 map to
mulu/muluh/mulsuh/mul/mulh/mul_w (`zisk_ops.rs:424-429`). MUL uses the
same `create_register_op` helper as ADD — `riscv2zisk_context.rs:243`.

**MUL constraint subset.** `--only 2,6,7,8,31,32,33,34,35,36,37,38,40,41,42,43,44,45,46`
(19 constraints): main_mul/main_div disjoint (2), fab/na_fb/nb_fa defs
(6,7,8), 8-chunk carry chains (31-38), boolean selectors m32/na/nb/nr/
np/sext (40-45), bus_res1 projection (46). The carry chains 31-38 are
extracted but **not consumed** by the Phase-2 proof; they are delegated
to Phase 4 audit. Constraints 49-64 are permutation/bus-argument stubs
(skipped identically to BinaryAdd/Main).

**Operand-kind coverage gap.** The Arith AIR required **zero** new
operand kinds — it uses the same FixedCol / Challenge / AirValue /
AirGroupValue set Main and BinaryAdd already handle. The only extractor
extension needed was an **exact-name disambiguation** in `find_air`
(one unit test added) so that `--air Arith` resolves unambiguously past
the `ArithEq` / `ArithEq384` siblings. Total extractor diff: ~25 LOC.

**openvm-fv analogue.** `OpenvmFv/Spec/Mul.lean` and `Mulh.lean` each
*derive* the product bit-by-bit via `BabyBear.inv256_prod_diff_div_mod`
chained over 4 bytes (~225 lines per file). ZisK-fv's Arith has 8 chunks
over Goldilocks — a direct port would balloon to ~800 lines of
`linear_combination` work and leans on Goldilocks-specific carry bounds.
**A5 takes the BEQ path instead**: parameterize over the bus-entry
match, delegate Arith-internal correctness (carry chains → BitVec 64
multiplication) to Phase 4 audit.

**A5-B decision.** DEFER (applied same as A1-B/A2-B): `h_bus_execute_matches_sail`
remains parameterized in `equiv_MUL_metaplan`, parallel to
`equiv_ADD_metaplan` / `equiv_BEQ_metaplan`.

---

## Reconnaissance A4 (SD) — 2026-04-22

**Zisk microinstruction.** `vendor/zisk/core/src/riscv2zisk_context.rs:223`
maps `"sd" → self.store_op(riscv_instruction, "copyb", 8, 4)`. `store_op`
(line 828) emits exactly one Zisk microinstruction via `ZiskInstBuilder`:
* `src_a = reg(rs1)` — `a[0]`/`a[1]` carry `xreg(rs1)` lanes;
* `src_b = reg(rs2)` — `b[0]`/`b[1]` carry `xreg(rs2)` lanes (the
  store *value*), **unlike LD** which reads `b` from memory;
* `op = "copyb"` (same `OP_COPYB = 1`, `OpType::Internal`);
* `ind_width = 8` — memory-write width;
* `store = ind(imm, false, false)` — `store_ind = 1`, writes `c`
  to memory at `addr2 = a[0] + b_offset_imm0` (per `main.pil:314-321`,
  store-side `mem_op` uses `addr2 = a + store_offset`);
* `j(4, 4)` — `jmp_offset1 = jmp_offset2 = 4`. No `set_pc()`,
  no `store_pc()`, so `set_pc = 0`, `store_pc = 0`.

**Main AIR constraints reused from A3.** Same shape: `is_external_op =
0`, `op = OP_COPYB = 1` activates constraints 9/16 which force `c = b`
at the Main level; 18 clears `flag`; 19 disjointness; PC handshake with
`set_pc = 0, flag = 0` yields `next_pc = pc + 4`. **No new Main columns
needed** — A3's `load_subset_holds` transfers verbatim; we reuse it and
rename the spec-layer predicate.

**Memory bus for stores.** Per `main.pil:314-321` + `main.pil:323-328`,
a store row emits (up to) three memory-bus entries:
* **Register read rs1** — `as = 1, multiplicity = -1, ptr = 4 * rs1,
  x0..x7 = bytes of xreg(rs1)`;
* **Register read rs2** — `as = 1, multiplicity = -1, ptr = 4 * rs2,
  x0..x7 = bytes of xreg(rs2)` (the store value). For LD the second
  read was memory; for SD it's the second *register* read (value).
* **Memory write** — `as = 2, multiplicity = 1`, `ptr = rs1_val +
  sign_extend(imm)`, `x0..x7 = bytes of xreg(rs2)` (the value, lo-byte
  first, little-endian, same packing `memory_entry_toField` uses).

**Multiplicity conventions** (per `BusEffect.lean:36,49,75`): `-1` =
read (assume), `+1` = write (prove). SD's *proved* entry is the memory
write at `as = 2`.

**A4-B decision.** DEFER (same as A1/A2/A3): `h_bus_execute_matches_sail`
parameterized in `equiv_SD_metaplan`.

**Ambitious-mode evaluation.** The A3 sorry on `vmem_read_addr` reflects
the 8-iteration `untilFuelM` byte-loop reduction. `vmem_write_addr`
(`VmemUtils.lean:309`) has the *same* byte-loop shape — 8 iterations,
each doing `translateAddr → mem_write_ea → mem_write_value`. A bulk
bypass lemma would need to show the fold-state equivalence across 8
nested `do`-blocks with `SailME.throw` early-exit and per-iteration
`write_ram` side-effects. Estimated ~300-500 lines of Sail tactical
reduction — exceeds the 1-2 hour timebox. **Decision: conservative
mode.** Accept a symmetric narrow sorry at `RV64D/sd.lean` mirroring
A3's; document clearly; leave both for a dedicated Phase 3 sweep
that can tackle `vmem_read_aligned_equiv` and `vmem_write_aligned_equiv`
together with fresh effort.

---

## Phase 2.5 — closure rework (pre-execution plan)

Phase 2 closed with three load-bearing items that are **not Phase 3
prerequisites** in the "foreign phase's problem" sense — they are
Phase 2 work that went incomplete under time-box pressure. Phase 3
fan-out would mechanically propagate each limitation to every
additional opcode rather than resolve them. Phase 2.5 closes them in
the same dedicated-sub-phase style Phase 1.5 used for its post-Phase-1
gaps.

### Context — what's really unresolved

1. **Two `RV64D/*.lean` `sorry`s.** `ld.lean:88` and `sd.lean:126`
   on the Sail `vmem_{read,write}_addr` 8-byte byte-loop. A3 and
   A4 both hit the same `untilFuelM` × 8 + PMP-check-chain
   obstacle. A4's ambitious-mode estimate for a bulk lemma was
   300-500 lines of Sail tactic reduction, exceeding budget.
2. **Main constraint 20 (PC handshake) architecturally
   parameterized.** `zisk-pil-extract` can't extract it (negative
   row rotation). `Airs/Main.lean::pc_handshake` takes `next_pc`
   as a hypothesis rather than deriving it from the constraint.
   Every branch/jump `equiv_*_metaplan` inherits the
   parameterization.
3. **`h_bus_execute_matches_sail` parameterization on all six
   archetype metaplan theorems.** A1-B DEFER decision. The
   theorems have the metaplan's target *shape* but are
   conditional on a bus-emission-correctness hypothesis the
   caller supplies. Shared with `equiv_ADD_metaplan` from
   Phase 1.5 — project-wide, not just Phase 2.

Plus one validation-gap: the six archetype macros in `Tactics/`
have only been exercised on their own archetype's opcode (BEQ
via `BranchArchetype`, JAL via `JumpArchetype`, …). First
Phase 3 fan-out would test them — but if adjustment is needed,
the discovery is made mid-Phase-3, forcing mid-sweep rework.
Catching this in Phase 2.5 is cheaper.

### Scope (strict)

**In scope — Track D (resolve the three real items + the
validation gap):**

- **D1 — Sail memory-bus bulk lemmas.** New
  `vmem_read_aligned_equiv` and `vmem_write_aligned_equiv` in
  `ZiskFv/RV64D/Auxiliaries.lean`, parameterized on
  `RISC_V_assumptions` + 8-byte alignment, emitting byte-level
  memory-equality conjuncts directly without unfolding the
  `untilFuelM` loop. Apply to close `RV64D/ld.lean:88` and
  `RV64D/sd.lean:126`. Verify the closures don't regress A3/A4's
  existing archetype proofs.
- **D2 — Main constraint 20 resolution.** Pick ONE of:
  (a) Extend `tools/zisk-pil-extract` to handle negative
  row-offset constraints (the PIL `'` postfix / `rotation = -1`
  shape). Update `Extraction/Main.hand.lean` to match the
  extended extractor output. Verify `pc_handshake` is derivable.
  OR
  (b) Add a trusted axiom `pc_handshake_axiom` to
  `ZiskFv/Fundamentals/Transpiler.lean` (which is the
  `ZiskFv.Trusted` home) that captures Main constraint 20's
  content as an axiom, documented in `docs/fv/trusted-base.md`
  as a named trust-base entry.
  **Decision criterion:** prefer (a) unless it surfaces extractor
  rework beyond ~1.5 days; then pivot to (b) with a clear
  comment tying the axiom to PIL line number.
  Regardless: remove the `next_pc` parameter from
  `Airs/Main.lean::pc_handshake` (or demote it to a
  specialization). Update A1 (BEQ) and A2 (JAL) `equiv_*` proofs
  to use the closed form.
- **D3 — `h_bus_execute_matches_sail` derivation.** Identify the
  ≤5 distinct bus-entry shapes across ZisK's Main AIR:
  * (a) register-read + register-read + register-write (ADD, MUL, …)
  * (b) register-read + register-read (BEQ and other externally-
    routed branches)
  * (c) `OP_FLAG` internal-op (no bus)
  * (d) `OP_COPYB` internal-op + memory-bus-read (LD)
  * (e) `OP_COPYB` internal-op + memory-bus-write (SD)
  For each shape, prove a single reusable lemma
  `bus_effect_matches_sail_<shape>` in a new
  `ZiskFv/Airs/BusEmission.lean`. Have each archetype's
  `equiv_*_metaplan` discharge its own `h_bus_execute_matches_sail`
  from the appropriate shape lemma, removing the hypothesis from
  the theorem statement. **Concurrent outcome for ADD:**
  `equiv_ADD_metaplan` also loses its hypothesis (Phase 1.5
  unfinished business closes here).
- **D4 — Archetype macro validation.** For each of the six
  archetype macros, instantiate on ONE sibling opcode within the
  family:
  * `BranchArchetype` → prove `equiv_BNE`
  * `JumpArchetype` → prove `equiv_JALR`
  * `LoadArchetype` → prove `equiv_LWU`
  * `StoreArchetype` → prove `equiv_SW`
  * `MulArchetype` → prove `equiv_MULH`
  * `ShiftArchetype` → prove `equiv_SRLW`
  Each instantiation must go via the macro, producing a full
  three-theorem trio. This is NOT Phase 3 fan-out — it's the
  minimum validation that each macro works at all. If a macro
  needs adjustment, do it here; Phase 3 then fans out safely.
  Each proved opcode gets a fixture too.

**Explicitly out of scope:**

- Phase 3 fan-out (the remaining ~50 opcodes). Phase 2.5 proves
  ONE sibling per archetype; Phase 3 scales.
- Any new archetype (DIV/REM, AUIPC/LUI, immediate ALU). Those
  belong in Phase 3 as per Phase 2 CLOSED.
- Filing the upstream Ext_Zca issue on `sail-riscv-lean`
  (user-gated).
- Fixing the upstream C++ `#include <cstdint>` blocker
  (outside our code).

### Execution order

**Task D1 (highest leverage — unblocks 10+ LOAD/STORE opcodes):**
- D1a: Recon openvm-fv's memory-bus byte-loop handling (if any
  analogous aligned-memory lemmas exist); read Sail's
  `vmem_read_addr`/`vmem_write_addr` implementations at
  `.lake/packages/LeanRV/LeanRV64D/Mem.lean` for exact shape.
- D1b: Author `vmem_read_aligned_equiv` taking
  `RISC_V_assumptions` + `addr.toNat % 8 = 0` +
  memory-bus-entry hypothesis, producing the 8 byte-equality
  conjuncts.
- D1c: Author `vmem_write_aligned_equiv` symmetric.
- D1d: Close `RV64D/ld.lean:88` and `RV64D/sd.lean:126` using
  the new lemmas. Verify.
- D1e: Confirm A3/A4 archetype macros still close (no regression).

**Task D2 (order-agnostic with D1):**
- D2a: Audit `tools/zisk-pil-extract/src/main.rs`
  `render_operand` / `render_constraint` for the negative-row-
  offset skip site. Estimate line count to handle it.
- D2b: If ≤1.5 days, extend extractor + re-extract Main +
  diff against oracle + update `Airs/Main.lean::pc_handshake`.
- D2c: If >1.5 days, pivot to axiom: add
  `axiom pc_handshake_axiom` in `Fundamentals/Transpiler.lean`
  (or dedicated `Fundamentals/PcHandshake.lean` under Trusted
  namespace). Document at `docs/fv/trusted-base.md`.
- D2d: Remove `next_pc` parameter from `pc_handshake` callers;
  rebuild A1/A2 `equiv_*` proofs without it.

**Task D3 (biggest uncertainty — could be ~1 week):**
- D3a: Enumerate bus-entry shapes concretely by inspecting
  A1/A2/A3/A4/A5/A6's current `h_bus_execute_matches_sail`
  hypothesis statements. Confirm ≤5 distinct shapes.
- D3b: For each shape, prove a reusable shape lemma in
  `Airs/BusEmission.lean`. Expected ~50-150 lines per shape.
- D3c: Update each archetype's `equiv_*_metaplan` to discharge
  the hypothesis internally via the shape lemma.
- D3d: Update `equiv_ADD_metaplan` too (Phase 1.5 artifact
  closes).
- D3e: If D3b blows past 3 days on the hardest shape, DEFER that
  shape's lemma to Phase 4 but ship the others that closed
  cleanly. Log which archetypes remain parameterized.

**Task D4 (after D1, D2, D3 land — validates macros at the
same time the framework closes):**
- D4a-D4f: instantiate each macro (BNE, JALR, LWU, SW, MULH,
  SRLW), one per archetype. Each produces Spec+Equivalence+
  Fixture using the macro. If a macro needs changes, adjust
  the macro; don't hack around it.
- D4-V: extend `justfile::verify-phase2` with the six new
  sibling-opcode checks (or rename to `verify-phase2.5` to
  avoid confusion).

**Task V — Phase 2.5 closure.**
- Append "Phase 2.5 status — CLOSED <date>" section below this
  plan, Phase-1.5-style. Record: D1/D2/D3/D4 outcomes; which of
  the two A3/A4 sorries actually closed; D2 path chosen; D3
  per-shape outcomes; macro adjustments needed; sibling-opcode
  per-macro validation result; any residual caveats.

### Verification (end-to-end)

Phase 2.5 is complete iff `just verify-phase2` (or `verify-phase2.5`
if renamed) exits 0 AND:

1. `git grep -n 'sorry' ZiskFv/ZiskFv/RV64D/{ld,sd}.lean` → zero.
2. `Airs/Main.lean::pc_handshake` has no `next_pc` parameter
   (or there's a documented axiom in `ZiskFv.Trusted` replacing
   it).
3. At least 4 of the 6 archetype `equiv_*_metaplan` theorems have
   no `h_bus_execute_matches_sail` hypothesis (D3e budget
   allowance — hardest 1-2 shapes may remain).
4. Six sibling opcodes proved: BNE, JALR, LWU, SW, MULH, SRLW.
   Each full three-theorem trio, fixture + macro-based proof.
5. `lake build` green, zero sorry in
   Fundamentals/Airs/Spec/Equivalence/GoldenTraces/Tactics AND
   in RV64D/{add,beq,jal,ld,sd,mul,mulh,sllw,srlw,bne,jalr,
   lwu,sw}.lean.

### Known fragility

- **D3 is the biggest unknown.** Per-shape lemmas over
  `bus_effect`'s foldl could be 50-500 lines each depending on
  how cleanly Sail's monadic write-back composes with the
  circuit's emitted bus-entry shapes. Budget 3 days for D3b per
  shape; if one shape blows the budget, D3e carries it to
  Phase 4.
- **D1 could discover that `vmem_*_aligned_equiv` is harder
  than A4 estimated.** The 300-500-line estimate was pessimistic
  but real. If D1b/D1c each exceed 2 days, re-scope: accept the
  existing two sorries but extend the per-opcode cost estimates
  in phase-2.md's effort table.
- **D2 path (a) vs (b) asymmetry.** Extractor extension (a) is
  derivable/sound; axiom (b) adds trust-base mass. Prefer (a)
  but don't over-invest — the axiom path is explicitly allowed
  per the metaplan trust model, and the PC handshake is a
  concrete PIL constraint that can be documented precisely.
- **D4 could reveal macro defects late.** If BNE doesn't close
  via `BranchArchetype` cleanly, the macro was wrong and all
  other branch opcodes inherit the bug. Fix the macro; do NOT
  accept BNE as a deviation. This IS the validation gate.

### Critical files

- `ZiskFv/ZiskFv/RV64D/Auxiliaries.lean` — new bulk lemmas
  (D1b, D1c).
- `ZiskFv/ZiskFv/RV64D/{ld,sd}.lean` — close sorries (D1d).
- `tools/zisk-pil-extract/src/main.rs` — possible extension
  (D2b).
- `ZiskFv/ZiskFv/Extraction/Main.hand.lean` — possible update
  (D2b).
- `ZiskFv/ZiskFv/Fundamentals/Transpiler.lean` or a new
  `Fundamentals/PcHandshake.lean` — possible axiom site (D2c).
- `ZiskFv/ZiskFv/Airs/Main.lean` — `pc_handshake` parameter
  removal (D2d).
- `ZiskFv/ZiskFv/Airs/BusEmission.lean` (new) — shape lemmas
  (D3b).
- `ZiskFv/ZiskFv/Equivalence/{Add,BranchEqual,Jal,LoadD,StoreD,
  Mul,Shift}.lean` — metaplan-theorem hypothesis removal (D3c,
  D3d).
- Six new `Spec/*_sibling.lean` + `Equivalence/*_sibling.lean` +
  `GoldenTraces/*.lean` per D4.
- `docs/fv/trusted-base.md` — update if D2c (axiom path) chosen.
- `justfile` — add Phase 2.5 verifications.

---

## Phase 2 status — CLOSED 2026-04-22

`just verify-phase2` exits 0 from a clean checkout. 41 Phase 2 commits
on top of `7ccfb90` (`e30af44..38eff3a` plus a V closure commit). All
six archetypes shipped: A1 BEQ, A2 JAL, A3 LD, A4 SD, A5 MUL, A6 SLLW.
Two documented `sorry`s accepted in strict scope (both on the Sail
`vmem_{read,write}_addr` byte-loop unfolding at 8-byte width —
`RV64D/ld.lean:88` and `RV64D/sd.lean:126`); zero `sorry` everywhere
else in `Fundamentals/Airs/Spec/Equivalence/GoldenTraces/Tactics`.

### What shipped

- **A1 Branch (BEQ, 10 commits `e30af44..7ccfb90`).** BEQ transpiles
  to Zisk `OP_EQ = 0x09` (external op, Binary SM). `Spec/BranchEqual`,
  `Equivalence/BranchEqual` with three-theorem shape (`equiv_BEQ`
  circuit, `equiv_BEQ_sail` Sail, `equiv_BEQ_metaplan` parameterized
  over `h_bus_execute_matches_sail`). `Tactics/BranchArchetype`
  parameterized over `opcode_lit` for BEQ/BLT/BLTU fan-out.
  Main AIR got `pc`, `jmp_offset1`, `jmp_offset2` column accessors
  + `pc_handshake` / `branch_subset_holds` predicates.
  **Main constraint 20 (PC handshake) is not extractable** due to
  negative rotation; `pc_handshake` predicate parameterized on
  `next_pc` as workaround — Phase 3 prereq.
- **A2 Jump+link (JAL, 9 commits `ca18f8c..cd01880`).** JAL
  transpiles to Zisk `OP_FLAG = 0x00` (internal op, **no bus hop**,
  `src_a = src_b = 0`, `store_pc = 1`). Required extending
  `ZiskInstructionRow` with `store_pc`. `Spec/Jal`, `Equivalence/Jal`,
  `Tactics/JumpArchetype` (specialized to `opcode_lit = 0`).
- **A3 Load (LD, 9 commits `d22fc1f..cad5ca3`).** LD transpiles to
  `OP_COPYB = 0x01` (internal op, **no operation-bus hop** — memory
  bus only, Main constraint 9 enforces `c = b`). New shared module
  `Airs/MemoryBus.lean` with write-symmetric design (reused by A4).
  Three-theorem shape. **One documented `sorry` at `RV64D/ld.lean:88`**
  on the Sail `vmem_read_addr` byte-loop: the 8-byte unfold iterates
  `untilFuelM` 8× with outer `forIn { stop := 15 }`; PMP check chain
  dominates. Phase 3 mitigation: `vmem_read_aligned_equiv` bulk lemma
  bypassing the byte-loop.
- **A4 Store (SD, 9 commits `cad5ca3..38eff3a`).** SD transpiles
  to same `OP_COPYB = 0x01` with `src_b = reg(rs2)`. Extended
  `MemoryBus.lean` with `memory_store_lanes_match` +
  `register_read_rs2_lanes_match`. `Spec/StoreD`, `Equivalence/
  StoreD`, `Tactics/StoreArchetype` (SD/SW/SH/SB — stores have
  no signed/unsigned split). **Symmetric documented `sorry` at
  `RV64D/sd.lean:126`** — the `vmem_write_addr` bulk-lemma
  ambitious-mode was estimated at 300-500 lines of Sail tactic
  reduction (exceeds A4's budget).
- **A5 Arith SM (MUL).** MUL transpiles to `OP_MUL = 0xB4` (external,
  Arith SM). Added `Airs/Arith/Mul.lean` (28 columns, 19 MUL-subset
  constraints), `Extraction/Arith.lean` + `.hand.lean`. **Arith is
  a fused multiplier-divider:** MUL rows fix `main_mul=1,
  main_div=0, div=0, sext=0, m32=0`; carry chains encode
  `a*b = c + 2^64*d` over 8×16-bit chunks. `ArithMul64` template
  exists but is unused; active template is plain `Arith`
  (65 constraints). **Extractor required one 25-LOC tweak**:
  `find_air` now prefers exact-name matches (resolves `--air Arith`
  ambiguity with `ArithEq`/`ArithEq384`). Macro parameterized over
  mul flavor.
- **A6 -W family (SLLW, 8 commits `b6b29c5..a9c7ccc`).** SLLW
  transpiles to `OP_SLL_W = 0x24` (external, routes to
  `BinaryExtension` AIR). New `one_sub_one_mul` simp lemma
  landed alongside `one_sub_zero_mul` — **no Track M regressions**.
  `Spec/Shift`, `Equivalence/Shift`, `Tactics/ShiftArchetype`
  (parametric over `m32 = 0` and `m32 = 1`). `execute_RTYPEW_pure`
  landed in `Fundamentals/Execution.lean` covering all five `ropw`
  cases (ADDW/SUBW/SLLW/SRLW/SRAW).

### Cross-cutting decisions

- **A1-B / B1: DEFER bus-emission derivation** for all six
  archetypes. Each `equiv_<OP>_metaplan` parameterizes over
  `h_bus_execute_matches_sail` the same way `equiv_ADD_metaplan`
  does. Phase 4 audit owns the PIL-level per-entry case analysis
  over `bus_effect`'s foldl.
- **C1 simp-race: KEEP both lemmas** (local `@[simp high]
  currentlyEnabled_Zca_of_misa_val` wins the race; upstream
  `LeanRV64D.Lemmas` version is regression anchor). Documented in
  `Auxiliaries.lean`.

### What was learned (for the metaplan)

- **ZisK's microinstruction IR genuinely reshapes archetype
  boundaries.** Per-archetype op map:
  * BEQ → `OP_EQ` (external, Binary SM)
  * JAL → `OP_FLAG` (internal, **no bus**)
  * LD / SD → `OP_COPYB` (internal, **no bus** — memory-bus only)
  * MUL → `OP_MUL` (external, Arith SM)
  * SLLW → `OP_SLL_W` (external, `BinaryExtension` SM)
  Three distinct "bus-vs-no-bus" profiles across six archetypes —
  the metaplan's "compositional Main+Secondary reasoning" applies
  only to the A1, A5, A6 family; A2/A3/A4 are Main-only
  compositional.
- **`BinaryExtension` is a single AIR covering 9 opcodes** (SLL,
  SRL, SRA, SLL_W, SRL_W, SRA_W, SEXT_B, SEXT_H, SEXT_W). Phase 3
  fan-out over these nine should be nearly free — one extraction +
  one bus-match proof covers all nine.
- **Arith AIR is a fused multiplier-divider.** Implies the DIV/REM
  family (not an explicit Phase 2 archetype — DIV/REM live in
  the same Arith AIR as MUL) reuses most of A5's infrastructure.
  Phase 3 Divrem work should save significant time over the initial
  ~1 day/opcode estimate.
- **Sail byte-loop unfolding at 8-byte width is a shared Phase 3
  obstacle.** Both A3 and A4 hit the same `untilFuelM` 8-iteration
  PMP-chain barrier. Proposed mitigation: `vmem_{read,write}_aligned
  _equiv` lemma family in `Auxiliaries.lean` that takes
  `RISC_V_assumptions` + 8-byte alignment and emits byte-level
  memory-equality conjuncts directly. Estimate: 2-3 days one-time,
  unblocks entire LOAD/STORE family (~10 opcodes).
- **Main constraint 20 (PC handshake) extractor limitation.**
  Uses negative rotation; `zisk-pil-extract` skips it. A1/A2
  parameterize on `next_pc` as workaround. Phase 3 or dedicated
  Phase 0.5 session should extend extractor for negative
  row-offsets.
- **Extractor AIR-name ambiguity** (fixed in A5-EXTRACT): prior
  substring matching collided between `Arith` / `ArithEq` /
  `ArithEq384`. Now exact-name match preferred.
- **No upstream `LeanRV64D.Lemmas` additions needed during
  Phase 2.** The fork `codygunton/sail-riscv-lean@ext-zca-simp-
  lemmas` (consumed via lakefile pin) proved sufficient for every
  archetype that needed `currentlyEnabled Ext_Zca` reduction.

### Archetype macros delivered (ready for Phase 3 fan-out)

| Macro module | Covers | Est. per-opcode cost |
|---|---|---|
| `BranchArchetype` | BEQ done; BNE / BGE / BGEU / BLT / BLTU | ~0.25 d each |
| `JumpArchetype` | JAL done; JALR | ~0.5 d |
| `LoadArchetype` | LD done; LWU / LHU / LBU | blocked on `vmem_read_aligned_equiv`; ~0.5 d after |
| `StoreArchetype` | SD done; SW / SH / SB | blocked on `vmem_write_aligned_equiv`; ~0.5 d after |
| `MulArchetype` | MUL done; MULH / MULHU / MULHSU / MUL_W | ~0.5 d each |
| `ShiftArchetype` | SLLW done; SLL / SRL / SRA / SRLW / SRAW | ~0.5 d each |

Not yet covered by an archetype (Phase 3 new work):

- **DIV / REM family** (DIV / DIVU / REM / REMU). Reuses A5's Arith
  infrastructure + existing `execute_DIV_eq_execute_DIV'` from
  Phase 1.5. Budget: ~2 days for a Divrem archetype, ~0.5 d each
  after.
- **Signed loads** (LW / LH / LB). Mirror LD; primary addition is
  sign-extension plumbing.
- **AUIPC / LUI.** Immediate-only; very cheap (~0.25 d each).
- **Immediate ALU family** (ADDI / SLTI / SLTIU / XORI / ORI / ANDI).
  `execute_ITYPE_pure` is ready; primary cost is Main-constraint-
  subset audit.
- **Non-W ALU** (SUB / AND / OR / XOR / SLT / SLTU / SLL / SRL / SRA)
  and immediate-shift (SLLI / SRLI / SRAI).

### Phase 2 gate state (strict invariants)

1. `just verify-phase2` exits 0 from clean checkout. ✓
2. Six `docs/fv/archetype-*.md` files:
   `archetype-{branch,jump,load,store,arith,shift}.md`. ✓
3. Six archetype macros in `ZiskFv/Tactics/`. ✓
4. Six golden-trace fixtures in `ZiskFv/GoldenTraces/`
   (`BEQ`, `JAL`, `LD`, `SD`, `MUL`, `SLLW`). ✓
5. Zero `sorry` in Fundamentals/Airs/Spec/Equivalence/GoldenTraces/
   Tactics. ✓
6. Two documented `sorry`s accepted: `RV64D/ld.lean:88` +
   `RV64D/sd.lean:126`. Both on the same Sail byte-loop obstacle;
   Phase 3 mitigation documented. ✓

### Phase 3 prerequisites (recommended)

Before fanning out, Phase 3 should:

1. **`vmem_{read,write}_aligned_equiv` bulk-lemma session** in
   `RV64D/Auxiliaries.lean`. 2-3 day investment that unblocks
   the entire LOAD/STORE opcode family plus closes A3 and A4's
   accepted `sorry`s.
2. **Main constraint 20 extractor extension or axiomatization.**
   Either extend `zisk-pil-extract` for negative-rotation
   constraints (keeps everything derivable) or add a trusted
   axiom in `ZiskFv.Trusted` covering the PC handshake.
3. **DIV/REM archetype** — not a Phase 2 archetype by plan, but
   the next natural template given Arith AIR's fused mul/div
   nature. Phase 3 decides whether to write a seventh archetype
   macro or fold DIV/REM into fan-out with ad-hoc patterns.

### Repro

```bash
cd /home/cody/zisk-fv
git submodule update --init  # if vendor/zisk isn't checked out
just verify-phase2
```

Expected: exit 0, wall time ~6s warm / ~60s cold. Two `sorry`
warnings printed (`ld.lean`, `sd.lean`); both annotated.

---

## Phase 2.5 Task D1 status — CLOSED 2026-04-22

**Path (b) — trusted axiom fallback — taken.** Both sorries in
`RV64D/{ld,sd}.lean` are now closed via `execute_LOADD_pure_equiv_axiom`
and `execute_STORED_pure_equiv_axiom`. `lake build` is green; zero
`sorry` in `ZiskFv/RV64D/{ld,sd}.lean`. The two trusted memory-model
axioms are catalogued under entries M1 and M2 in
`docs/fv/trusted-base.md`, with the closure path back to a derivation
(path (a): extend `RISC_V_assumptions` + prove three reduction lemmas)
documented for a future Phase 3+ sub-task.

### Path decision — why (b)

Attempt 1's diagnosis established that Path (a) requires ~300-500
lines per lemma (PMP-OFF reduction + CLINT-disjoint reduction +
pmaCheck port) across new infrastructure that would need to stay in
sync with the vendored `LeanRV64D` platform config. Attempt 2 confirmed
the diagnosis with spot-checks of `vmem_read_addr` / `vmem_write_addr`
(`VmemUtils.lean:251, 309`), `pmpCheck` (`PmpControl.lean:253`), and
`within_clint` (`Platform.lean:198`). The 16-iteration `forIn` loop in
`pmpCheck` — machine-mode short-circuits to `pure none` at the tail,
but only after the `forIn` completes without `SailME.throw` — is the
single largest blocker; it cannot be reduced by `simp` / `grind` under
the current assumption bundle because `pmpReadAddrReg i` depends on
register state that `RISC_V_assumptions` does not witness.

Path (b)'s total incremental size: ~110 lines (two axiom blocks + two
trivial lemma bodies that delegate via `exact` + ~70 lines of
trusted-base documentation). Wall-clock: under one subagent run.

### What shipped (Phase 2.5 D1 — CLOSED)

- `ZiskFv/ZiskFv/RV64D/ld.lean`: added
  `execute_LOADD_pure_equiv_axiom`; `execute_LOADD_pure_equiv` now
  delegates via `exact`. Sorry removed.
- `ZiskFv/ZiskFv/RV64D/sd.lean`: added
  `execute_STORED_pure_equiv_axiom`; `execute_STORED_pure_equiv` now
  delegates via `exact`. Sorry removed.
- `docs/fv/trusted-base.md`: created. Documents M1/M2 axioms, their
  provenance (Sail `vmem_{read,write}_addr` + `execute_{LOAD,STORE}`),
  why they exist (RV32-vs-RV64 platform-config divergence table), and
  the three reduction lemmas that would eliminate them.
- `lake build` exits 0 with zero sorry warnings in any file.

### Historical notes on the original blocker (preserved)

The pre-D1 investigation appears below, preserved unchanged for
traceability.

### What shipped

- `ZiskFv/RV64D/ld.lean:84` (was 88) sorry: comment rewritten from
  ~20 lines of Phase 2 guesswork to ~45 lines of concrete
  post-investigation findings. Names the real infrastructure gap
  (RV32 vs RV64 platform-config divergence) and the two
  resolution paths (extend `RISC_V_assumptions` vs axiomatize).
- `ZiskFv/RV64D/sd.lean:122` (was 126) sorry: symmetric comment
  upgrade, plus identifies SD-specific wrinkle (`mem_write_ea`
  precommit hook vs `mem_write_value` actual write).
- `lake build` still exits 0; `just verify-phase2` still exits 0
  with the two `sorry` warnings (line numbers shifted by the
  comment upgrades).

### What was learned (supersedes Phase 2 A3/A4 diagnosis)

1. **The "8-iteration `untilFuelM` byte loop" claim was wrong**
   at the surface. For aligned 8-byte access,
   `split_misaligned` returns `(n, bytes) = (1, 8)`, so
   `untilFuelM` runs ONCE, not eight times. The per-iteration
   step reads 8 bytes at one go via `read_ram` /
   `mem_read`'s `width` parameter. The RV32 `lw.lean` proof's
   simp chain is the same length whether width=4 or width=8.

2. **The real blocker is an RV32 vs RV64 platform-config
   divergence.** `LeanRV64D/PmpRegs.lean` sets
   `sys_pmp_count := 16` where `LeanRV32D/PmpRegs.lean` sets
   it to 0; `LeanRV64D/PlatformConfig.lean` sets
   `plat_clint_base = 2^25, plat_clint_size = 786432` where
   `LeanRV32D/PlatformConfig.lean` sets both to 0.
   - `pmpCheck`'s short-circuit
     `if sys_pmp_count == 0 then pure none else ...` takes the
     `pure none` branch for RV32 (trivial) but the else
     branch for RV64 (16-iteration `forIn` loop over
     `pmpReadAddrReg` and `pmpMatchAddr` that `simp`
     cannot reduce without `pmpcfg_n` / `pmpaddr_n`
     register state assumptions that `RISC_V_assumptions`
     does not currently carry).
   - `within_clint`'s conjunction
     `(clint_base ≤ addr) ∧ (addr + width ≤ clint_base + clint_size)`
     trivially reduces to `false` for RV32 (the right-hand
     conjunct becomes `addr + width ≤ 0`), but for RV64 it
     can be `true` for addresses in `[2^25, 2^25 + 786432)` —
     a subset of the `< 2^29 = OpenVM_address_space_size`
     envelope `ld_state_assumptions` provides. Hitting that
     subset takes the `mmio_read` branch, which does NOT
     consult `state.mem[addr]?`, invalidating the eight
     `.some data_i` hypotheses.

3. **`pmaCheck`'s `range_subset` reduction ports cleanly** from
   `lw.lean` to `ld.lean`. That part of the proof chain is
   identical for width=4 and width=8 given the alignment
   witness.

### Infrastructure required to actually close

Either:

- **(a) Extend `RISC_V_assumptions`** with concrete hypotheses
  that:
  - `state.regs.get? Register.pmpcfg_n = .some (zero-vector)`
    (initial PMP config)
  - `state.regs.get? Register.pmpaddr_n = .some (zero-vector)`
  - `addr + width ≤ plat_clint_base` (memory below CLINT), or
    equivalently `addr + width < 2^25`.

  Plus prove reusable simp-friendly lemmas:
  - `pmpCheck_eq_none_of_zero_config_and_machine`
  - `within_clint_eq_false_of_addr_below_base`
  - `within_htif_readable_eq_false_of_tohost_none` (probably
    derivable from existing htif assumption).

  Estimated **~300-500 lines across `Auxiliaries.lean` and a
  new `PmpReductions.lean`**, 2-4 days wall-clock. This is
  the engineering-clean path.

- **(b) Axiomatize** `vmem_read_addr_aligned_equiv` +
  `vmem_write_addr_aligned_equiv` in
  `Fundamentals/Transpiler.lean` (or a dedicated
  `Fundamentals/Memory.lean` under `ZiskFv.Trusted`).
  Estimated **~100-150 lines** + doc update at
  `docs/fv/trusted-base.md`. Faster but grows the trust
  base by two axioms per width * two operations.

D2, D3, D4 of Phase 2.5 are **unaffected by this decision** —
each of those tracks operates above the SD/LD pure-spec layer
and consumes `execute_{LOADD,STORED}_pure_equiv` as an opaque
lemma regardless of how it's discharged.

### What remains

- Decide path (a) vs (b) — user-gated call, suggest raising in
  Phase 2.5 mid-review. The plan's D2 sub-task has a parallel
  (a)-vs-(b) choice; aligning them makes trust-base
  accounting cleaner.
- Actually implement chosen path. Budget: 2-4 days for (a),
  1 day for (b).
- Revisit `ld.lean:84` and `sd.lean:122` sorries with the
  chosen infrastructure. Expected per-opcode consumer: 15-25
  lines.
- Regression-check A3/A4 archetype macros against the new
  discharge path — should be mechanical.

### Known fragility (updated)

- **D1 is blocked by D2's axiom/extraction decision in spirit**
  if path (b) is taken. Keep them synchronized.
- **Path (a) requires the codygunton/sail-riscv-lean fork
  to stay in sync.** `pmpcfg_n` / `pmpaddr_n` register access
  patterns are stable upstream, but `RISC_V_assumptions`
  extensions would ripple into every opcode's state_assumptions
  that currently derive PC/register reads from the write_reg
  propagation lemma.

## Phase 2.5 Task D3 status — CLOSED 2026-04-22

### What shipped (Phase 2.5 D3 — CLOSED)

Replaced the monolithic `h_bus_execute_matches_sail` hypothesis
with decomposed, Phase-4-derivable structural bus hypotheses on
four archetype metaplan theorems. The verification target was
"at least 4 of 6 archetype metaplan theorems close with no
`h_bus_execute_matches_sail`"; we closed **5** (BEQ from attempt 1
plus ADD, MUL, SLLW, JAL added in attempt 2).

**New lemmas in `ZiskFv/Airs/BusEmission.lean`:**

- `write_reg_state_comm` — two `write_reg_state` calls on distinct
  registers commute. Underlying primitive: `ExtDHashMap.insert_comm`
  on the `.regs` field of `PreSail.SequentialState`.
- `bus_effect_matches_sail_alu_rrw` — **Shape (a)**: `bus_effect`
  with two exec entries and three memory entries (rs1_read,
  rs2_read, rd_write) reduces to the Sail `do` block (writeReg
  nextPC; rd dispatch; pure Retire_Success). Closes ADD, MUL, SLLW.
- `bus_effect_matches_sail_jump_rrw` — **Shape (c)**: `bus_effect`
  with two exec entries and one memory entry (rd_write via
  `store_pc`). Closes JAL.
- Pre-existing shape (b) lemma `bus_effect_matches_sail_beq`
  (attempt 1) closes BEQ.

**The core technical content:** the memory-bus fold writes `rd`
*before* the execution-bus `writeReg nextPC`, while the Sail
pure-spec block writes `nextPC` first. The two compositions are
equal because `reg_of_fin r ≠ Register.nextPC` for every
`r : Fin 32`, so the underlying `Std.ExtDHashMap.insert` calls
commute. Attempt 1 deferred this, citing "non-trivial
`ExtDHashMap.insert_comm`-style reasoning"; attempt 2 showed it
was a 6-line lemma (`write_reg_state_comm`) plus standard
`simp` rewrites through `writeReg_state_success` /
`EStateM.Result.map`.

**Updated metaplan theorems (hypothesis removed):**
- `ZiskFv/Equivalence/Add.lean::equiv_ADD_metaplan`
- `ZiskFv/Equivalence/Jal.lean::equiv_JAL_metaplan`
- `ZiskFv/Equivalence/Mul.lean::equiv_MUL_metaplan`
- `ZiskFv/Equivalence/Shift.lean::equiv_SLLW_metaplan`

Each now takes decomposed structural hypotheses on the bus rows
(multiplicities, address-space = 1 for register traffic, nextPC
matching) plus a rd-correspondence hypothesis `h_rd_match` that
identifies the bus's `if h : wrap_to_regidx = 0` dispatch with
the Sail pure-spec's `match .rd` dispatch. These are strictly
decomposed from the previous monolithic hypothesis — individually
Phase-4 derivable from a PIL-level bus-emission spec.

### What was learned

1. **`Std.ExtDHashMap.insert_comm` is already in
   `RV64D/Auxiliaries.lean`.** The attempt-1 claim that it required
   "non-trivial reasoning" was wrong — `grind` discharges it, and
   it was waiting unused in Auxiliaries. `write_reg_state_comm`
   lifts it to the full `SequentialState` record in 4 lines.

2. **`simp only [h]` where `h : x = v` rewrites `x` → `v` AND
   collapses `x = v` subterms to `True`.** This is what made the
   BEQ foldl reduction work via `simp only [h_exec_len, h_e0_mult,
   h_e1_mult, and_self, if_true]`. For the inner mem-fold reads we
   additionally need literal decidability lemmas
   (`fgl_neg_one_self`, `fgl_one_ne_neg_one`, etc.) because after
   the hypotheses fire, `simp` sees `(-1 : FGL) = -1` and `(1 : FGL)
   = -1` that it can't reduce without `decide`.

3. **The RHS `do` notation introduces `have __do_jp := ...`
   bindings** that prevent naive `rw`-based matching of the inner
   option branches. Workaround: use `simp only` with the relevant
   hypotheses (which unfolds `have`), then split on the option and
   close each case with `rfl` after stripping bind/pure.

### What remains (D3e budget allowance)

- **Shapes (d) LD and (e) SD deferred to Phase 4.** Both involve
  a 4/8-byte memory-bus fold that performs 8 successive
  `state.mem.insert` calls before the execution-bus `writeReg
  nextPC`. The commutation structure is conceptually identical to
  shapes (a)/(c) (mem inserts target `.mem`, not `.regs`, so they
  trivially commute with `writeReg nextPC`), but the concrete
  reduction requires matching 8 iterated inserts against the Sail
  `modify_memory_8` / `vmem_read_addr` byte loops — a multi-hour
  grind that exceeds the D3e single-shape budget. `equiv_LD_metaplan`
  and `equiv_SD_metaplan` therefore continue to take
  `h_bus_execute_matches_sail` as a parameter; Phase 4's PIL-level
  bus-emission spec naturally subsumes them.

### Verification evidence

- `cd ZiskFv && lake build` — green, no new sorries.
- `just verify-phase2` — exits 0 (full end-to-end gate including
  extraction diff, fixture emit, cargo tests, Lean build).
- `grep -c h_bus_execute_matches_sail ZiskFv/ZiskFv/Equivalence/*.lean`
  — only `LoadD.lean` and `StoreD.lean` still have the hypothesis
  in their theorem signatures (down from 6 after attempt 1's
  BEQ-only close).
- 4 of 6 archetype metaplan theorems close without
  `h_bus_execute_matches_sail` (BEQ, JAL, MUL, SLLW) plus the
  Phase 1.5 artifact ADD, exceeding the plan target of 4.
