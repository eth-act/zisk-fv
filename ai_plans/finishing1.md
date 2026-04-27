# finishing1 — Track N: h_rd_val retirement, additive store_pc=0 archetype

**Branch:** `feature/track-n-h-rd-val` (worktree at `/home/cody/zisk-fv/.worktrees/track-n`).
**Source plan:** `/home/cody/.claude/plans/squishy-strolling-catmull.md`.

## Goal

Retire the `h_rd_val :` parameter on `Equivalence/X.lean` metaplan
theorems for the **4 opcodes** whose `h_rd_val` is honestly
dischargeable from circuit primitives within the infrastructure that
exists at the start of this branch + one tiny Spec-lemma authoring
step:

| Opcode | Closure path |
|---|---|
| ADD | already Tier-1 (commit `be7264c`) |
| LUI | already Tier-1 (commit `3dfaf88`) |
| ADDI | needs `Spec/Addi::addi_compositional_with_binaryadd` (small, ~50 lines, analogue of `add_compositional`) |
| SUB | needs `Spec/Sub::sub_compositional_with_binaryadd` (same shape) |

All four go through the **`store_pc = 0`** path (rd-write via Main's
`c_0`/`c_1` lanes) and use the **additive carry chain** (BinaryAdd
or analog). They are the only opcodes whose Tier-1 derivation is
feasible with:

- Phase 1 keystones (K1-A, K2 Layer 1, K3, K4) — already shipped
- Wave B.5 toolkit (`Fundamentals/PackedBitVec/NoWrap.lean`) — already shipped
- One inline Spec-lemma authoring step (the two `_compositional_with_binaryadd` analogues)

Other archetypes have been pulled out into successor plans:

| Originally proposed scope | Closure work | Now in |
|---|---|---|
| ADDW, ADDIW, SUBW (3) | needs `BinaryExtension` AIR extraction | finishing2 |
| SLT, SLTU, SLTI, SLTIU (4) | needs `Binary` AIR extraction | finishing2 |
| Logic ops (AND/OR/XOR + I-immediates, 6) | needs `Binary` AIR | finishing2 |
| Shift ops (12) | needs `BinaryExtension` AIR | finishing2 |
| MUL, MULHU, DIVU, REMU, MULW (5 unsigned) | needs multiplicative no-wrap toolkit | finishing4 |
| MULH, MULHSU, DIV, DIVW, DIVUW, REM, REMW, REMUW (8 signed) | needs multiplicative + signed BitVec.toInt toolkit | finishing4 |
| JAL, JALR, AUIPC (3 store_pc=1) | needs `transpile_PC` axiom + `_store_value_hi_bv` Spec lemmas + `store_pc_lanes_match_*` predicates + wide-PC no-wrap toolkit | finishing5 |
| Loads (7) | needs `Mem` AIR extraction | finishing3 |
| Stores (4) | needs `Mem` AIR extraction | finishing3 |

This narrowed scope captures **what the existing in-tree
infrastructure plus a single small authoring step actually closes**.
Everything else is a bigger missing-infrastructure class with its own
plan; cf. `docs/fv/track-n-traps.md` for the per-opcode escalation
manifests already authored.

## The trust chain (for the 4 in-scope opcodes)

```
[byte-bus rd-write entry e2]
  ↓ K2 writes-side lane-match (parameterized; finishing3 closes)
[Main's c_0, c_1 lanes]
  ↓ <op>_compositional_with_binaryadd (FGL identity; ADD shipped, ADDI/SUB to author)
[BinaryAdd's a/b/c chunks]
  ↓ K1-A binary_add_chunks_eq_bv_add (BitVec lift)
[BitVec spec result, expressed in BinaryAdd chunk form]
  ↓ Wave B.5 toolkit + transpile bridges
[Sail input r1_val, r2_val, imm]
```

After Phase 3 closes for these 4 opcodes, the metaplan theorems take
only:

- circuit-constraint bundles (`<op>_circuit_holds`)
- K2 lane-match (Layer 1; closes in finishing2/3)
- byte/chunk range hypotheses (range-check trusted surface)
- transpile bridges (Main columns ↔ Sail BitVec inputs; CLAUDE.md
  trusted surface)

**No `h_rd_val :`, `h_byte_sum :`, `h_input_val :`, `h_chunk_sum :`,
or any other OUTPUT-EQ parameter survives.** The "honest Tier-1"
semantic test is: every parameter's RHS depends only on **spec
inputs** (`r1_val`, `r2_val`, `imm`), never on **spec outputs**
(`r1_val + r2_val`, `BitVec.signExtend ...`, etc.).

## What shipped (Phase 1 — keystones)

| Keystone | File | Commit |
|---|---|---|
| K1-A | `Airs/Binary/BinaryAddPackedCorrect.lean` | `f92a1ca` |
| K2 (Layer 1) | `Airs/MemoryBus/LaneMatch.lean` | `2c627ac` |
| K3 | `Fundamentals/PackedBitVec/Extensions.lean` | `74005bf` + `92305eb` (high-half) |
| K4 | `Fundamentals/PackedBitVec/Signed.lean` + `Spec/MulFieldSigned.lean` + `Spec/DivFieldSigned.lean` | `919b0a2` |

Plus three docs: `docs/fv/track-n-traps.md`, `docs/fv/air-inventory.md`, `.gitignore`.

## What shipped (Phase 2 — discharge lemmas)

`Equivalence/RdValDerivation/{Arith,JumpUType,MulDivRemUnsigned,MulDivRemSigned}.lean`
(commits `be7264c`, `ec7dd8e`, `bed62b7`, `23e5669`, `86ec279`).

Most are Tier-2 wrappers (output-equality parameters survive); ADD
in `Arith.lean` is genuinely Tier-1; LUI in `JumpUType.lean` is
genuinely Tier-1 after the B.6 LUI-only work in `3dfaf88`. The other
Phase 2 files are kept in tree for use by the successor plans; their
Tier-2 forms remain consumable but explicitly mark the trust gap in
their docstrings.

The Wave B.6 retries (`b91e94f` for ALU-Arith, `442ef86` for JumpUType)
reverted gate-gaming sonnet outputs to clean Tier-1.5 forms and
appended escalation manifests to `docs/fv/track-n-traps.md` for the
non-in-scope archetypes.

## What shipped (Phase 2.5-pre — toolkit)

`Fundamentals/PackedBitVec/NoWrap.lean` at commit `c74b4ce`. Three
core lemmas (`fgl_eq_to_nat_eq`, `fgl_packed_2_lanes_natCast`,
`fgl_packed_4_chunks_natCast`) plus a worked example. Built by hand
with TDD discipline. Sufficient for the additive `store_pc = 0` path.

## Wave C — the only remaining work in this branch

### C-1: author 2 small Spec lemmas (by hand, TDD)

Two new theorems, by close analogy with `Spec/Add::add_compositional`:

#### `ZiskFv/ZiskFv/Spec/Addi.lean::addi_compositional_with_binaryadd`

```lean
theorem addi_compositional_with_binaryadd
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (h : addi_circuit_holds_with_binaryadd m b r_main r_binary) :
    main_c_packed m r_main
      = main_a_packed m r_main + main_b_packed m r_main
        - b.cout_1 r_binary * (4294967296 * 4294967296)
```

(or whatever the `Spec/Addi.lean` file's `addi_circuit_holds`
already names — verify before authoring; the `_with_binaryadd`
variant takes both Main and BinaryAdd hypothesis bundles.)

The proof is a copy of `add_compositional`'s — ADDI's PIL row is
ADD's row with the immediate folded into Main's `b` lanes upstream
of BinaryAdd, so the carry-chain composition is identical.

#### `ZiskFv/ZiskFv/Spec/Sub.lean::sub_compositional_with_binaryadd`

Analogous shape; SUB routes through BinaryAdd just like ADD (per the
Wave B.6 retry's escalation manifest in `docs/fv/track-n-traps.md`).

The proof reuses the carry chain, accounting for SUB's negation of
`b` upstream of BinaryAdd. Field-level identity unchanged from ADD's
shape:

```lean
main_c_packed m r_main
  = main_a_packed m r_main - main_b_packed m r_main
    - b.cout_1 r_binary * (4294967296 * 4294967296)
```

(Verify the existing `Spec/Sub::sub_compositional` to see if the
"with_binaryadd" variant is just a re-pluralization, or genuine new
work. If the existing `sub_compositional` already takes a BinaryAdd
parameter, no new authoring needed — the existing form may suffice.)

**Verification gate (C-1):**

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv
lake build ZiskFv.Spec.Addi
lake build ZiskFv.Spec.Sub
lake build ZiskFv  # full
# expected: 0 errors, 0 sorries
```

### C-2: upgrade ADDI and SUB discharge lemmas to Tier-1

Edit `Equivalence/RdValDerivation/Arith.lean` to replace ADDI's and
SUB's existing Tier-1.5 form (with `h_input_val` parameter) with a
real Tier-1 derivation that mirrors ADD's structure:

- Replace `bus_entry : OperationBusEntry FGL` parameter with a
  `b : Valid_BinaryAdd C FGL FGL` parameter (or whichever shape the
  new `_with_binaryadd` Spec hypothesis takes).
- Take the new circuit-holds bundle as `h_circuit`.
- Take K2 `register_write_lanes_match` as `h_lane_rd`.
- Take chunk ranges + byte ranges.
- Take TRANSPILE-BRIDGE input hypotheses (r1_val and either r2_val or imm).
- Inside the proof: invoke the new `_compositional_with_binaryadd`
  + K1-A's `binary_add_chunks_eq_bv_add` + Wave B.5 toolkit; close as
  ADD does.

**Verification gate (C-2):**

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv
lake build ZiskFv.Equivalence.RdValDerivation.Arith
lake build ZiskFv  # full
# Hard semantic gate — manual classification, not just grep:
# every parameter on h_rd_val_arith_addi and h_rd_val_arith_sub must be
# CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE, or TRANSPILE-BRIDGE (RHS depends
# only on spec inputs).
```

### C-3: Phase 3 — cleanup `Equivalence/{Add,Lui,Addi,Sub}.lean`

For each of the 4 opcode files:

1. Remove `h_rd_val :` from the metaplan theorem signatures
   (`_metaplan`, `_metaplan_from_bus`, `_metaplan_bus_self`,
   `_metaplan_op_bus`).
2. Replace its call site with the appropriate `h_rd_val_<archetype>_<op>`
   from `RdValDerivation/`.
3. Add the new circuit-hypothesis parameters the Tier-1 lemma
   requires.

**Verification gate (C-3):**

```bash
for op in Add Lui Addi Sub; do
  echo -n "$op: " ; grep -c 'h_rd_val :' "ZiskFv/ZiskFv/Equivalence/${op}.lean" || echo 0
done
# expected: 0 for each
cd ZiskFv && lake build
```

## Trust state at end of branch (for the 4 in-scope opcodes)

| Trust item | Status | Closes in |
|---|---|---|
| `h_rd_val` parameter on metaplan theorems | **retired** ✅ | this branch |
| K2 reads-side lane-match | parameterized (Layer 1) | finishing2 |
| K2 writes-side lane-match | parameterized (Layer 1) | finishing3 |
| Operation-bus `matches_entry` | parameterized; consequence of permutation soundness | trust-scoped (assumed) |
| Range-check / lookup soundness | parameterized | trust-scoped (assumed) |
| Transpile bridges (Main columns ↔ Sail BitVec inputs) | parameterized | CLAUDE.md trusted surface |

## Status / next action

- All Phase 1 keystones complete.
- All Phase 2 discharge lemmas complete (Tier-1 for ADD + LUI; Tier-1.5
  documented for the remainder).
- Wave B.5 toolkit complete.
- Wave B.6 retries complete (honest escalation manifests).
- **Next step:** Wave C-1 — author the two Spec lemmas by hand with
  TDD. Then C-2 (Tier-1 upgrade for ADDI/SUB; one subagent at most).
  Then C-3 cleanup (one subagent for the 4 Equivalence files).

The 4-opcode scope is small enough that one or two careful agent
dispatches close the entire branch. After this branch closes, the
b-r-a-n-c-h-i-n-g into finishing2/3/4/5 covers everything else.
