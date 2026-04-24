# Phase 4 Package C — residuals

Phase 4 Package C targeted the Arith state-machine internal correctness
proof: deriving from the 8-chunk carry-chain constraints that the PIL
row witness satisfies `c + d * 2^64 = a * b` (for MUL-family) and
`a * b + d = c` (for DIV-family), thereby closing the structural
hypothesis threaded through the nine
`equiv_{MUL,MULH,MULHU,MULHSU,MULW,DIV,DIVU,REM,REMU}_metaplan` theorems.

This document catalogues what shipped in the first pass and what
remains for a follow-on pass.

## What shipped (commits 0db8b9e, 8ee913f on `worktree-agent-a66100cc`)

### Step 1 — `Airs/Arith/CarryChain.lean` (164 lines)

Two pure-field theorems closing the 8-chunk × 16-bit carry-chain
identity on an arbitrary field:

* `arith_mul_unsigned_carry_identity` — given the 8 MUL-mode carry
  equations (`fab = 1`, `na = nb = np = nr = sext = m32 = div = 0`),
  derive `a_packed * b_packed = c_packed + d_packed * 2^64`.
* `arith_div_unsigned_carry_identity` — given the 8 DIV-mode carry
  equations (`div = 1`, otherwise same zeroing), derive
  `a_packed * b_packed + d_packed = c_packed`.

Both close via `linear_combination` with coefficients `65536^k` in
factored form (per Phase 1 ring-atom trap). No elevated `maxHeartbeats`
required.

### Step 2 — per-family specializations (`Airs/Arith/{Mul,Div}.lean`)

* `arith_mul_unsigned_packed_correct` (Mul.lean) — takes raw extraction
  constraints 6/7/8 + 31-38 at `v.circuit` and the 7 mode witnesses,
  concludes the packed MUL identity over named columns.
* `arith_div_unsigned_packed_correct` (Div.lean) — mirror for DIV mode
  (`div = 1`).

Both proofs:
1. Unfold constraints 6/7/8, substitute `na = nb = 0`, extract
   `fab = 1`, `na_fb = 0`, `nb_fa = 0` via `linear_combination`.
2. Unfold constraints 31-38, rewrite back to named columns, apply mode
   witnesses via `simp only` with a custom lemma set that tolerates
   missing atoms (avoiding the `rw` failure mode where a specific
   hypothesis lacks the symbol being rewritten).
3. Close via `linear_combination` on coefficients `65536^k * h(31+k)`.

Combined line count: ~200 lines for Mul.lean extension + ~140 lines
for Div.lean extension.

## What did not ship (Step 3 + Step 4)

Steps 3 and 4 — rewiring `Spec/*.lean` and dropping the `h_rd_match`
hypothesis from `Equivalence/*.lean`'s nine metaplan theorems — did
**not** ship this pass. They require additional plumbing beyond the
carry-chain identity:

### Missing bridge 1: `bus_res1` normalization via constraint 46

The current `arith_c_packed` in `Spec/Mul.lean:85` is defined as

```
(v.c_0 r + v.c_1 r * 65536) + v.bus_res1 r * 4294967296
```

where `bus_res1` is the range-checked 32-bit witness column (col 40).
Constraint 46 pins

```
bus_res1 = sext * 0xFFFF_FFFF + (1 - m32) * bus_res1_64
```

where `bus_res1_64 = main_mul * (c[2] + c[3]*65536) + main_div *
(a[2] + a[3]*65536) + (1 - main_mul - main_div) * (d[2] + d[3]*65536)`.

For MUL-unsigned (sext = 0, m32 = 0, main_mul = 1, main_div = 0), this
reduces to `bus_res1 = c[2] + c[3] * 65536`, which would let us
rewrite `arith_c_packed = c_chunks_packed` — the named-column packing
used by Step 2. This bridge is a ~40-line `constraint_46_of_extraction`
specialization that was **not** authored.

### Missing bridge 2: Main ↔ Arith operand equivalence at the bus

`main_c_packed` in `Spec/Mul.lean` is `m.c_0 r_main + m.c_1 r_main * 2^32`
(two 32-bit lanes). The bus-match identity already gives
`m.c_0 r_main = v.c_0 r_arith + v.c_1 r_arith * 65536`, etc. So far
this bridges the c-side; the a/b lanes use `(1 - m.m32 r_main)` factors
that collapse to 1 under `m.m32 = 0`.

Separately, `m.a_0 r_main` and `m.b_0 r_main` land on Arith's
`v.a_0 + v.a_1 * 65536` and `v.b_0 + v.b_1 * 65536` via the bus-match
on `a_lo`/`a_hi`/`b_lo`/`b_hi`. Composing these with Step 2 yields

```
main_c_packed = (m.a_0 + m.a_1 * 2^32) * (m.b_0 + m.b_1 * 2^32)
                - (high 64 bits, landed into d)
```

i.e. the low 64 bits of the 128-bit product. This composition is
~30 lines of `rw` and `linear_combination` per opcode.

### Missing bridge 3: From field identity to `BitVec 64` semantics

The nine `equiv_<OP>_metaplan` theorems target

```
execute_instruction (...) state = (bus_effect exec_row mem_row state).2
```

where the LHS is the Sail pure-spec block. The `h_rd_match` hypothesis
currently discharges the connection between the memory-bus row's
`e2.x0..e2.x7` bytes (which land as `U64.toBV` into `write_xreg`) and
the pure-spec's `rd_val` (a `BitVec 64` computed as
`r1_val * r2_val` truncated or high-half'd).

To drop `h_rd_match` we need:

* `U64.toBV` lemma connecting the 8 `e2.x*` bytes to
  `BitVec.ofNat 64 (c_packed.val)` when `c_packed.val < 2^64`.
* Range-lemma witnessing `c_packed.val < 2^64` from the chunk-bound
  properties on `c[0..3]` (each `< 2^16`).
* `BitVec.ofNat` ↔ `mul` commutation for the bounded-product case.

These are feasibility-known (the openvm-fv project discharges the
analogous RV32 property over BabyBear), but require ~100-150 lines of
`BitVec` arithmetic per family.

### Signed modes

Neither `arith_mul_unsigned_packed_correct` nor `arith_div_unsigned_packed_correct`
covers signed modes (`na = 1` or `nb = 1`). Signed MUL/DIV requires a
case-split on `(na, nb) ∈ {0,1}^2` with the `np`/`nr` sign-extend
witness bounds pinning the quadrant. This is ~300-400 additional lines
of per-case `linear_combination` and would retire MULH, MUL (for
negative operands), DIV, REM.

## Trust-base impact

The nine `equiv_<OP>_metaplan` theorems still take `h_rd_match` as a
structural hypothesis. Trust-base entries for these theorems were never
Sail-equivalence axioms (they were proof-signature parameters), so
**no axioms retire from this pass**. The pure-field + per-family
carry-chain theorems authored here are *proof-enablers* — they exist
so that a follow-on pass can close the three bridges above and drop
`h_rd_match` without introducing new axioms.

## Follow-on scope

The three bridges above are the path to fully closing Package C. Rough
estimates:

* Bridge 1 (constraint 46 specialization): ~40 lines, ≤½ day.
* Bridge 2 (Main ↔ Arith operand composition): ~30 lines × 9 opcodes
  = ~270 lines, 1 day.
* Bridge 3 (field ↔ BitVec lift): ~100 lines × 3 families (MUL, MUL-high,
  DIV) = ~300 lines, 1-2 days.
* Signed-mode closure: ~400 lines, 1-2 days.

Total: ~1000 lines, 3-5 days. No new axioms expected.
