# Track N — `h_rd_val` retirement: traps and idioms

Library-reference notes harvested during Phase 1 keystone implementation
(`feature/track-n-h-rd-val`). These are durable facts about the Lean
proof environment that future agents extending the BitVec-lift family
(K1-B, K1-C, K3, K4, and the Phase 2 derivation lemmas) need to know.

## K1-A findings (BinaryAddPackedCorrect, commit `f92a1ca`)

### 1. FGL-packed `.val` is **not** the raw Nat sum

The natural packing `a_packed := a_0 + a_1 · 2^32 : FGL` can exceed
`GL_prime = 2^64 - 2^32 + 1`: the maximum value is `2^64 - 1`, and
`2^64 - 1 > GL_prime`, so `a_packed.val ≠ a_0.val + a_1.val · 2^32`
in general. The `mod GL_prime` introduced by `ZMod` is *not* a no-op
even under per-chunk range bounds.

**Implication for the BitVec lift.** Statements of the form

```lean
BitVec.ofNat 64 (a_packed v row).val
  = BitVec.ofNat 64 (a_0.val + a_1.val · 2^32)
```

do **not** hold — they fail at the `(2^64 - 2^32, 2^64)` window where
`mod GL_prime` wraps but `mod 2^64` does not.

**Mitigation: state theorems in chunk-`.val` form.** Phrase
conclusions as

```lean
BitVec.ofNat 64 ((v.a_0 row).val + (v.a_1 row).val * 4294967296)
```

where each chunk's `.val` is taken individually and combined at the
ℕ level. The Goldilocks-no-wrap bound is then automatic from the
per-chunk range bounds (`a_0.val < 2^32 ∧ a_1.val < 2^32 ⟹
a_0.val + a_1.val · 2^32 < 2^64 < 2 · GL_prime`).

This is a **breaking deviation from the plan's signature.** The plan
wrote `BitVec.ofNat 64 (a_packed v row)` as if `a_packed : FGL` could
be lifted directly. In practice, downstream Phase 2 derivation lemmas
must consume the chunk-level form.

### 2. `simp only [BitVec.toNat_add]` causes kernel deep-recursion

```
simp only [BitVec.toNat_add]
-- (kernel) deep recursion detected
```

Same for `simp only [BitVec.toNat_ofNat]` on goals that mention
`BitVec.ofNat 64 n` for several distinct `n`. Lean's kernel ends up
trying to compute `2^64` recursively to verify the simp rewrite.

**Mitigation: use `rw` instead of `simp only` for these lemmas.**

```lean
rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
```

`rw` produces a lighter proof term — the kernel can verify it without
expanding `2^64` numerically.

### 3. Carry-chain ℕ lift idiom

To lift a field equation `x = y : FGL` to `x.val = y.val : ℕ` under
range bounds:

```lean
have h_rhs_cast : <rhs FGL expr>
    = (((<rhs Nat expr> : ℕ) : FGL)) := by push_cast; ring  -- not rfl!
have h_lhs_cast : <lhs FGL expr>
    = (((<lhs Nat expr> : ℕ) : FGL)) := by push_cast; ring
rw [h_lhs_cast, h_rhs_cast] at h_fgl
have heq := congr_arg Fin.val h_fgl
simp only [Fin.val_natCast] at heq
omega   -- closes via range bounds + boolean cases
```

**`push_cast; ring`, not `push_cast; rfl`** — the latter triggers a
definitional-equality check that recurses into `2^64` computation.

### 4. Final BitVec close: strip mods then `Nat.add_mul_mod_self_right`

After `BitVec.eq_of_toNat_eq` and the `rw` chain through `BitVec.toNat_add`
+ `BitVec.toNat_ofNat`, the goal is

```
(a_nat + b_nat) % 2^64 = c_nat
```

where the carry chain says `a_nat + b_nat = c_nat + k₁ · 2^64`.
Rewrite the LHS into the form `c_nat + k₁ · (2^64)` (via plain `ring`
with the chain hypotheses), then close with

```lean
rw [Nat.add_mul_mod_self_right]   -- (x + k · m) % m = x % m
exact Nat.mod_eq_of_lt h_c_bound
```

## Project-wide invariants reminded by K1-A

- **Factored form `4294967296 * 4294967296`** is required wherever
  `2^64` appears in carry-chain coefficients. `ring` and
  `linear_combination` treat `4294967296 * 4294967296` and
  `18446744073709551616` as different polynomial atoms even though
  they're numerically equal. (Documented in CLAUDE.md trap #2.)

- **Never re-quantify `[Field FGL]`** at the lemma level — declare it
  once globally in `Fundamentals/Goldilocks.lean`. (CLAUDE.md trap #1.)
