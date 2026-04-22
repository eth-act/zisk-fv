# Archetype: Arith (MUL family)

**Status.** Closed Phase 2 A5 for MUL. MULH / MULHU / MULHSU fan out
via `Tactics/MulArchetype.lean` in Phase 3.

## Scope

The Arith state machine (distinct from Binary/BinaryAdd) is the
heavyweight multiplier/divider behind RV64 MUL, MULH, MULHU, MULHSU
(and the 32-bit MULW variant, out of A5 scope). Its PIL lives at
`vendor/zisk/state-machines/arith/pil/arith.pil`. Unlike BinaryAdd (9
constraints, 4 core carry-chain), Arith has 65 constraints spanning
8 carry chains for a full 64×64 multiply-divide, plus sign-extension
witnesses and arith-table / arith-range-table lookups.

## Archetype decision (A5 design)

**Parameterize, don't derive.** Like BEQ's treatment of the Binary
SM's `flag` bit, MUL's archetype does **not** derive the multiplication
from Arith's carry chains. The compositional theorem
`Spec.Mul.mul_compositional` states:

> *If* Main and Arith emit matching operation-bus entries *and* the
> mode witnesses (MUL-subset booleans) hold, then Main's packed `c`
> lanes equal Arith's packed result lanes.

The separate Arith-internal correctness claim (Arith's `c[0..3]` are
the low 64 bits of `a * b` as integers) is delegated to Phase 4
audit. This parameterization matches A1 (BEQ) and contrasts with ADD,
which derives the sum from BinaryAdd's 2-lane carry chain (openable
in Lean in a few dozen lines). Unfolding Arith's 8-chunk byte-level
decomposition to `BitVec 128` arithmetic would add ~several hundred
lines of `linear_combination` / carry-arithmetic work — roughly
openvm-fv `Spec/Mul.lean` × 4 — and is off the A5 critical path.

## Concrete layout

### PIL → Extraction

`ZiskFv/Extraction/Arith.lean` (65 constraints; 19 enumerated in
`--only` flag, 16 permutation-argument stubs) is generated from
`pil/zisk.pilout` by `tools/zisk-pil-extract`. The hand oracle
`Arith.hand.lean` mirrors it byte-for-byte (diff-gated in
`verify-phase2`).

The MUL-relevant subset:

| Constraint | Meaning | Notes |
|------------|---------|-------|
| 2 | `main_mul * main_div = 0` | disjoint selectors |
| 6,7,8 | `fab`, `na_fb`, `nb_fa` definitions | sign factor |
| 31–38 | carry chains (eq[0..7]) | **delegated to Phase 4** |
| 40–45 | boolean selectors: `m32`, `na`, `nb`, `nr`, `np`, `sext` | mode witnesses |
| 46 | `bus_res1` definition | bus output projection |

### AIR layer

`ZiskFv/Airs/Arith/Mul.lean` — `Valid_ArithMul` structure with named
columns and `constraint_N_of_extraction` iff-bridges for the bool
constraints. Parallels `Airs/Binary/BinaryAdd.lean`.

### Bus projection

`opBus_row_Arith` (also in `Airs/Arith/Mul.lean`) mirrors the
`proves_operation(...)` call at `arith.pil:269-270`, specialized to
MUL:

* `multiplicity` ← `multiplicity` witness column (forced to 1 on
  active MUL rows),
* `a_lo` ← `a[0] + a[1] * 2^16`, `a_hi` ← `a[2] + a[3] * 2^16` (since
  MUL has `div = 0`),
* `b_lo` / `b_hi` similarly,
* `c_lo` ← `c[0] + c[1] * 2^16` (MUL-primary),
* `c_hi` ← `bus_res1` (range-checked 32-bit; for MUL with `m32 = 0`,
  `sext = 0`, this equals `c[2] + c[3] * 2^16`),
* `flag` ← 0 (MUL's bus flag is `div_by_zero`, always 0),
* precompile fields ← 0.

### Transpile contract

`Fundamentals/Transpiler.lean` `transpile_MUL` axiom mirrors ADD's
shape (MUL uses the identical `create_register_op` helper —
`riscv2zisk_context.rs:243`). Fields fixed: `op = OP_MUL = 180`,
`is_external_op = 1`, `m32 = 0`, `set_pc = 0`, `store_pc = 0`,
`jmp_offset1 = jmp_offset2 = 4`, `a`/`b` lanes from `xreg(rs1/rs2)`.

### Compositional proof

`Spec/Mul.lean` — `mul_compositional` closes in ~8 lines:
1. Destruct `mul_circuit_holds` into its 5 components.
2. Extract the `c_lo` / `c_hi` bus equalities from `matches_entry`.
3. Unfold both bus emissions via `simp only`.
4. Substitute Main's `c_0` / `c_1` via the bus equalities; conclude.

The proof does **not** touch the Main `a_hi`/`b_hi` (1 - m32) factor
because MUL's circuit identity only consumes the `c` lanes.

### RV64D Sail equivalence

`RV64D/mul.lean` — `execute_MULH_mul_pure_equiv` closes via
`execute_MUL_eq_execute_MUL'` (a fully-closed lemma in
`Fundamentals/Execution.lean`) + the standard `rX_read_xreg_equiv` /
`write_xreg` / `wX_write_xreg_*_equiv` pipeline shared with ADD.
**Restricted to the `.MUL` (Low half) case** — MULH / MULHU / MULHSU
fan out via MulArchetype.

### Metaplan theorem

`Equivalence/Mul.lean` exposes three theorems:
* `equiv_MUL` — circuit-level identity
  (`main_c_packed = arith_c_packed`).
* `equiv_MUL_sail` — Sail-level reduction via
  `PureSpec.execute_MULH_mul_pure_equiv`.
* `equiv_MUL_metaplan` — the metaplan target shape
  (`execute_instruction = bus_effect ...`). Parameterized on
  `h_bus_execute_matches_sail`, same contract as
  `equiv_ADD_metaplan` and `equiv_BEQ_metaplan`.

### Archetype macro

`Tactics/MulArchetype.lean` — `mul_archetype_bus_match` parametric
over `opcode_lit : FGL`. MULH / MULHU / MULHSU call it with
`OP_MULH`, `OP_MULUH`, `OP_MULSUH` respectively. The
`mul_archetype_proof` tactic macro is a one-liner consuming a
literally-named `h_circuit : mul_archetype_circuit_holds m v
r_main r_arith opcode_lit` in scope.

### Golden trace

`GoldenTraces/MUL.lean` — canonical 3×5=15 witness, all identities
closed by `decide`. Two rows (Main + Arith) with concrete Goldilocks
cell values covering: packed-`c` match, opcode consistency with
`OP_MUL`, boolean selectors, bus-match on a/b lanes.

## Phase 4 debts left behind

1. **Arith-internal correctness.** The carry chains (constraints
   31–38) entail that `c[0..3]` packed = low 64 bits of `a * b` for
   the MUL-primary case. A Phase 4 audit lemma would close this via
   an 8-chunk `linear_combination` akin to openvm-fv `Spec/Mul.lean`
   (scaled from BabyBear 4-byte to Goldilocks 8-chunk).
2. **`h_bus_execute_matches_sail`.** Same as A1/A2/A3/A4: a PIL-level
   bus-emission spec derives it uniformly.
3. **`transpile_MUL` per-flavour distinction.** MUL vs. MULH etc.
   differ only by the `op` literal (and `m32` for MULW). Phase 3
   adds sibling axioms with only `OP_*` swapped.

## Pointers

* **openvm-fv analogue.** `/home/cody/openvm-fv/OpenvmFv/Spec/Mul.lean`
  + `Mulh.lean`. openvm-fv *derives* the product from the byte-level
  carry chain; ~225 lines per file. ZisK-fv parameterizes instead.
* **ZisK source references.**
    * PIL: `vendor/zisk/state-machines/arith/pil/arith.pil` (airtemplate
      `Arith`), `arith_mul64.pil` (64-bit-only variant, currently unused
      by the pilout since `Arith` is the active template).
    * Rust: `vendor/zisk/core/src/zisk_ops.rs:424-429` (opcode table),
      `vendor/zisk/core/src/riscv2zisk_context.rs:243-247` (RV64 → Zisk
      MUL/MULH/MULHU/MULHSU/MULW dispatch).
* **Metaplan location.** `ai_plans/zisk-fv-phase-2.md` Reconnaissance
  A5 (appended at phase close).
