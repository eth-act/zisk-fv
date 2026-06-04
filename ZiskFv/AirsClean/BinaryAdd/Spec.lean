import ZiskFv.AirsClean.BinaryAdd.Row

/-!
# BinaryAdd Spec + Assumptions

The Clean-side spec for the BinaryAdd AIR. **Assumptions** are the
per-row range bounds + carry-pin (caller-supplied or provided by a
parent range channel); **Spec** is the proved relation
`cPacked = (packed32 a + packed32 b) % 2^64`.

Adapted from the extraction harness branch's `ZiskFvClean/BinaryAdd/Soundness.lean`,
specialized from generic `F p` to `FGL` (Goldilocks `p ≈ 2^64`).

## Adaptation note — pGt

The extraction harness used `[Fact (p > 2^65)]` so that `4 * 2^32 + 2^16 < p`
(needed for `ZMod.val_add_of_lt` to fire on the carry-chain
equations). For Goldilocks p = `2^64 - 2^32 + 1`, we instead use:

* `2 * 2^32 + 2^16 = 8590000128 < p` — well under p
* `2 * 2^32 < p / 2`                 — tighter than the extraction harness

The Soundness proof's range-discharging steps need to use these
Goldilocks-specific bounds instead of the extraction harness's pGt.

## Trust note

No axioms. Pure definitional content.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks

/-- Assumptions on a BinaryAdd row, as expected by the Clean
    Component. Range bounds + carry pin.

    Range bounds: `a_0, a_1, b_0, b_1 < 2^32`, `c_chunks_* < 2^16`.

    Carry pin: `cout_0` and `cout_1` are the exact arithmetic
    carries of the per-half adds. This is needed because in the
    extracted Component cout_0/cout_1 are row-input columns (not
    `witness` outputs), so the soundness proof needs to *consume*
    them, not derive them.

    Note: cout_0/cout_1 booleanness is enforced by the Component's
    own constraints (the `cout * (1 - cout) = 0` clauses), so not
    declared here. -/
def Assumptions (row : BinaryAddRow FGL) : Prop :=
  row.a_0.val < 2 ^ 32 ∧ row.a_1.val < 2 ^ 32 ∧
  row.b_0.val < 2 ^ 32 ∧ row.b_1.val < 2 ^ 32 ∧
  row.c_chunks_0.val < 2 ^ 16 ∧ row.c_chunks_1.val < 2 ^ 16 ∧
  row.c_chunks_2.val < 2 ^ 16 ∧ row.c_chunks_3.val < 2 ^ 16 ∧
  row.cout_0.val = (row.a_0.val + row.b_0.val) / 2 ^ 32 ∧
  row.cout_1.val = (row.a_1.val + row.b_1.val + row.cout_0.val) / 2 ^ 32

/-- The BinaryAdd Spec: c-packed equals (a-packed + b-packed) mod 2^64. -/
def Spec (row : BinaryAddRow FGL) : Prop :=
  cPacked row = (packed32 row.a_0 row.a_1 + packed32 row.b_0 row.b_1) % 2 ^ 64

/-- Useful lemma: Goldilocks prime exceeds `2 * 2^32 + 2^16`.
    Needed for `ZMod.val_add_of_lt` on the carry-chain equations. -/
lemma GL_gt_carry_sum : 2 * 2 ^ 32 + 2 ^ 16 < GL_prime := by decide

/-- And exceeds `2 * 2^32` alone. -/
lemma GL_gt_2pow33 : 2 ^ 33 < GL_prime := by decide

end ZiskFv.AirsClean.BinaryAdd
