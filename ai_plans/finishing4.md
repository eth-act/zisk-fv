# finishing4 — MDR multiplicative + signed Tier-1

**Branch:** TBD (likely `feature/track-n4-mdr`).
**Predecessor:** `finishing1.md` closes the additive ALU; this plan
handles the multiplicative family (MUL/DIV/REM and their W/signed
variants) where the trust gap is a different toolkit problem.

## Goal — h_rd_val Tier-1 retirement for 13 opcodes

| Sub-archetype | Opcodes (count) |
|---|---|
| MDR-unsigned | MUL, MULHU, DIVU, REMU, MULW (5) |
| MDR-signed | MULH, MULHSU, DIV, DIVW, DIVUW, REM, REMW, REMUW (8) |

These opcodes already have **Tier-2 discharge lemmas in tree** at
`ZiskFv/ZiskFv/Equivalence/RdValDerivation/MulDivRemUnsigned.lean`
(commits `bed62b7` + `92305eb`) and `MulDivRemSigned.lean` (commit
`23e5669`). Each takes `h_byte_sum` as a parameter saying "the bus
entry's bytes pack to spec.toNat" — same trust class as `h_rd_val`,
just rephrased. This plan retires those `h_byte_sum` parameters.

## Why this needs its own plan — the multiplicative gap

The Wave B.5 `Fundamentals/PackedBitVec/NoWrap.lean` toolkit handles
the additive case: given chunk-bounded ℕ values whose sum is `<
GL_prime`, lift an FGL equality to a ℕ equality. That works for ADD
because the carry-chain identity stays inside `< GL_prime`.

For MUL, the field-level identity is `a_packed * b_packed = c_packed
+ d_packed * 2^64` in FGL. With chunk-bounded operands, the *product*
`a_nat * b_nat` can range up to `2^128`, which exceeds `GL_prime`
many times over. The FGL-to-ℕ lift therefore *cannot* be a single
no-wrap argument over the whole equation. Instead, it requires
**chunk-level carry-chain reasoning over up to 16 chunks** —
analogous to K1-A's `BinaryAddPackedCorrect` but for the 4×16-chunk
× 4×16-chunk → 8×16-chunk multiplicative carry chain that lives
inside `Spec/MulField::main_mul_unsigned_field_correct`'s proof.

The signed half is harder still: `BitVec.toInt` decomposition + the
four-quadrant `(na, nb, np)` sign-witness pattern from Track P's
arith_table requires further bridges that K4 (commit `919b0a2`)
shipped only partially.

Both Wave B (sonnet) and Wave B.6 retry (sonnet) DONE_WITH_CONCERNS
escalations on these archetypes pinpointed exactly this gap. See
`docs/fv/track-n-traps.md` "ALU-Arith abstract bus-entry gap"
section (the same gap surfaces here).

## Scope items

### S1. Multiplicative no-wrap toolkit

New file `ZiskFv/ZiskFv/Fundamentals/PackedBitVec/MulNoWrap.lean`,
parallel to Wave B.5's `NoWrap.lean`.

**Required lemmas:**

```lean
-- 8-chunk Nat-level carry chain. Given the 8 carry equations from
-- arith_mul_unsigned_packed_correct + chunk range bounds, conclude
-- a_nat * b_nat = c_nat + d_nat * 2^64 (in ℕ).
theorem fgl_mul_unsigned_chunks_to_nat_identity ...

-- Combined with chunk-pack lemmas, gives:
theorem fgl_mul_unsigned_to_bv64_lo : c_nat = (a_nat * b_nat) % 2^64
theorem fgl_mul_unsigned_to_bv64_hi : d_nat = (a_nat * b_nat) / 2^64

-- Plus DIV/REM analogues for arith_div_unsigned_packed_correct:
theorem fgl_div_unsigned_to_bv64 : ...
theorem fgl_rem_unsigned_to_bv64 : ...
```

This is **chunk-level carry-chain reasoning**, scoped tightly. The
proofs are tedious but mechanical. The toolkit factors the per-chunk
`Fin.val_natCast + omega` chain so per-opcode upgrades stay small.

### S2. Signed BitVec.toInt toolkit extension

New file `ZiskFv/ZiskFv/Fundamentals/PackedBitVec/SignedNoWrap.lean`,
parallel to K4's `Signed.lean`.

**Required lemmas:**

```lean
-- Lift the multiplicative ℕ identity (S1) to BitVec.toInt under the
-- four-quadrant sign-witness pattern.
theorem fgl_mul_signed_chunks_to_int_identity
    (na nb np : FGL) (h_na_witness : ...) ... :
    (BitVec.ofNat 64 c_nat).toInt * (BitVec.ofNat 64 d_nat).toInt = ...

-- INT_MIN / -1 overflow handling for signed DIV/REM
theorem int_tdiv_overflow_full : Int.tdiv INT_MIN (-1) = INT_MIN

-- Similar for BitVec.toInt of W-variant 32-bit signExtended forms.
```

K4 already shipped the BitVec.toInt sign-bit case analysis +
`int_tdiv_overflow_case`; S2 supplies the **byte-level** signed
bridges that compose with S1 + K4 for full Tier-1.

### S3. Tier-1 upgrade for `RdValDerivation/MulDivRem{Unsigned,Signed}.lean`

For each of the 13 opcodes, replace its existing `h_byte_sum`
parameter with internal composition of:

- The opcode's field-level identity (already shipped:
  `Spec/MulField::main_mul_unsigned_field_correct`,
  `Spec/MulFieldSigned::main_mul_signed_field_correct`,
  `Spec/DivFieldSigned::main_{div,rem}_{unsigned,signed}_field_correct_main_level`)
- The S1 multiplicative no-wrap toolkit
- The S2 signed BitVec.toInt extension (signed opcodes only)
- K2 lane-match (Layer 1; closes in finishing3)
- K3's existing byte-bridges (`mul_lo_bv64_of_byte_sum`,
  `mul_hi_bv64_of_byte_sum`)

**Hard semantic gate:** every parameter on each
`h_rd_val_mdru_<op>` / `h_rd_val_mdrs_<op>` lemma is one of
{CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE, TRANSPILE-BRIDGE}. No
OUTPUT-EQ parameters survive (RHS depending on spec output).

### S4. Phase 3 cleanup — remove h_rd_val from 13 metaplan theorems

For each of `Equivalence/{Mul, MulHU, Divu, Remu, MulW, MulH,
MulHSU, Div, Divw, Divuw, Rem, Remw, Remuw}.lean`:

1. Remove `h_rd_val :` from each metaplan theorem signature.
2. Replace with the upgraded Tier-1 discharge call.
3. Add new circuit-hypothesis parameters as needed.

## Verification gates

```bash
cd /home/cody/zisk-fv/.worktrees/track-n/ZiskFv

# After S1
lake build ZiskFv.Fundamentals.PackedBitVec.MulNoWrap

# After S2
lake build ZiskFv.Fundamentals.PackedBitVec.SignedNoWrap

# After S3
lake build ZiskFv.Equivalence.RdValDerivation.MulDivRemUnsigned
lake build ZiskFv.Equivalence.RdValDerivation.MulDivRemSigned

# After S4
for op in Mul MulHU Divu Remu MulW MulH MulHSU Div Divw Divuw Rem Remw Remuw; do
  echo -n "$op: " ; grep -c 'h_rd_val :' "ZiskFv/ZiskFv/Equivalence/${op}.lean" 2>/dev/null || echo 0
done
# expected: 0 each

# Final
cd ZiskFv && lake build
# expected: 0 errors, 0 sorries
```

## Out of scope

- ALU-Arith / ALU-W / Logic / Shift / Compare / Loads / Stores /
  JAL/JALR/AUIPC — covered by finishing1, 2, 3, 5 respectively.
- Multiplicative or signed extensions to PIL behavior beyond what's
  already in the existing `Spec/MulField*`, `Spec/DivFieldSigned`,
  and Track P arith_table layers.

## Status / next action

Plan only. Branch not started. Predecessor `finishing1.md` must close
first. After that, the natural ordering is S1 (single subagent or
hand work) → S2 (single subagent or hand work) → S3 (2 parallel
subagents, one per archetype, post-S1+S2) → S4 (2 parallel subagents).
