import ZiskFv.AirsClean.ArithMul.Row
import ZiskFv.AirsClean.ArithTable

/-!
# ArithMul Spec + Assumptions (4-limb MUL-mode carry chain)

ArithMul is the **MUL-mode view** of ZisK's Arith AIR. The Clean
Component this `Spec` belongs to constrains the MUL-mode carry-chain
slice of that AIR: the 11 named-form constraints `6/7/8` + `31..38`,
i.e. exactly the `Airs/Arith/Mul.lean::mul_carry_chain_holds`
predicate the MUL-family equivalence proofs consume as their
AIR-fidelity surface.

* Constraints 6/7/8 — the sign-product helper columns `fab`,
  `na_fb`, `nb_fa` (Arith cols 30-32) pinned to
  `1 − 2·na − 2·nb + 4·na·nb`, `na · (1 − 2·nb)`, `nb · (1 − 2·na)`.
  PIL: `arith.pil:58`, `:59`, `:60`.
* Constraints 31..38 — the 4-limb (8-chunk × 16-bit) carry-chain
  identity `a · b = c + d · 2^64`, parameterized by the sign-product
  helpers and 7 carry witnesses (cols 0-6). PIL: `arith.pil:205`,
  `:207`, `:209`, `:211`, `:213`, `:215`, `:217`, `:219`.

Each clause below is a verbatim algebraic mirror of the corresponding
`constraint_N_every_row` in `build/extraction/Extraction/Arith.lean`
after substituting the named accessor for the corresponding
`Circuit.main … (column := N)` expression — **non-vacuous**, every
clause cited to a PIL line (plan D-2 / V-3).

The Arith AIR's 9 boolean flag constraints (na/nb/nr/np/sext/m32/div
+ the two `main_*` selectors) and the ROM lookup against the
74-row `ArithTable` are **not** part of this MUL-view Component's
`Spec` — they are consumed at the opcode-equiv level (the boolean
flags via `Airs/Arith/Mul.lean::mul_mode_booleans`; the ArithTable
via the `arith_table_*` class-#6b axioms). A narrower faithful view
is sound: it constrains a subset of the AIR's `assertZero`s.

## Trust note

No axioms. Pure definitional content.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

/-- ArithMul carries no soundness-assumptions: the 11-clause carry-chain
    `Spec` follows from the 11 definitional `assertZero` constraints
    alone (plan D-2 / F-4). -/
def Assumptions (_row : ArithMulRow FGL) : Prop := True

/-- The ArithMul MUL-mode carry-chain `Spec`: the 11 named-form
    constraints `6/7/8` + `31..38` of ZisK's Arith AIR. -/
def Spec (row : ArithMulRow FGL) : Prop :=
  -- Constraint 6 (`arith.pil:58`): fab − ((1 − 2·na) − 2·nb + 4·na·nb) = 0.
  row.carries.fab - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
        + 4 * row.flags.na * row.flags.nb) = 0
  -- Constraint 7 (`arith.pil:59`): na_fb − na·(1 − 2·nb) = 0.
  ∧ row.carries.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0
  -- Constraint 8 (`arith.pil:60`): nb_fa − nb·(1 − 2·na) = 0.
  ∧ row.carries.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0
  -- Constraint 31 (`arith.pil:205`): (fab·a_0·b_0 − c_0) + 2·np·c_0
  --   + div·d_0 − 2·nr·d_0 − carry_0·65536 = 0.
  ∧ row.carries.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.carries.carry_0 * 65536 = 0
  -- Constraint 32 (`arith.pil:207`).
  ∧ row.carries.fab * row.chunks.a_1 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.carries.carry_0
        - row.carries.carry_1 * 65536 = 0
  -- Constraint 33 (`arith.pil:209`).
  ∧ row.carries.fab * row.chunks.a_2 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_1 * row.chunks.b_1
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_2
        + row.chunks.a_0 * row.carries.nb_fa * row.flags.m32
        + row.chunks.b_0 * row.carries.na_fb * row.flags.m32
        - row.chunks.c_2
        + 2 * row.flags.np * row.chunks.c_2
        + row.flags.div * row.chunks.d_2
        - 2 * row.flags.nr * row.chunks.d_2
        - row.flags.np * row.flags.div * row.flags.m32
        + row.flags.nr * row.flags.m32
        + row.carries.carry_1
        - row.carries.carry_2 * 65536 = 0
  -- Constraint 34 (`arith.pil:211`).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_1
        + row.carries.fab * row.chunks.a_1 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_3
        + row.chunks.a_1 * row.carries.nb_fa * row.flags.m32
        + row.chunks.b_1 * row.carries.na_fb * row.flags.m32
        - row.chunks.c_3
        + 2 * row.flags.np * row.chunks.c_3
        + row.flags.div * row.chunks.d_3
        - 2 * row.flags.nr * row.chunks.d_3
        + row.carries.carry_2
        - row.carries.carry_3 * 65536 = 0
  -- Constraint 35 (`arith.pil:213` — half-byte boundary).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_1
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_1 * row.chunks.b_3
        + row.flags.na * row.flags.nb * row.flags.m32
        + row.chunks.b_0 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_0 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.flags.np * row.flags.m32 * (1 - row.flags.div)
        - row.flags.np * (1 - row.flags.m32) * row.flags.div
        + row.flags.nr * (1 - row.flags.m32)
        - row.chunks.d_0 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_0 * (1 - row.flags.div)
        + row.carries.carry_3
        - row.carries.carry_4 * 65536 = 0
  -- Constraint 36 (`arith.pil:215`).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.carries.carry_4
        - row.carries.carry_5 * 65536 = 0
  -- Constraint 37 (`arith.pil:217`).
  ∧ row.carries.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.carries.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.carries.carry_5
        - row.carries.carry_6 * 65536 = 0
  -- Constraint 38 (`arith.pil:219`, final chunk).
  ∧ 65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.carries.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.carries.carry_6 = 0

/-- The lookup half of the full ArithTable contract for this row.
    This is separated from `Spec` so the existing carry-chain re-root
    remains usable until the global theorem supplies lookup membership
    constructibly. -/
@[reducible]
def ArithTableSpec (row : ArithMulRow FGL) : Prop :=
  ArithTable.arithTable.Spec (arithTableRow row)

/-- Constraint 46 (`arith.pil:262`): the `bus_res1` output mux.
    Pins `bus_res1` to its mode-specialised value — sign-extension path
    (`sext * 4294967295`) or the appropriate high-chunk pair depending
    on `m32`, `main_mul`, and `main_div`.

    This is a verbatim algebraic mirror of `constraint_46_every_row` in
    `build/extraction/Extraction/Arith.lean:165`.  Constructibility:
    real Arith rows satisfy this because `arith_full.rs` computes
    `bus_res1` as exactly this mux (PIL `arith.pil:262`).  No axiom is
    introduced — the constraint is discharged by the `assertZero` in
    `mainWithArithTable`. -/
@[reducible]
def C46Spec (row : ArithMulRow FGL) : Prop :=
  row.flags.bus_res1
    - (row.flags.sext * 4294967295
      + (1 - row.flags.m32) * (
          (1 - row.flags.main_mul - row.flags.main_div)
              * (row.chunks.d_2 + row.chunks.d_3 * 65536)
          + row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536)
          + row.flags.main_div
              * (row.chunks.a_2 + row.chunks.a_3 * 65536))) = 0

/-- The sixteen 16-bit chunk column range constraints (`arith.pil:18-21`):
    each of the a/b/c/d chunks is a 16-bit value.  These hold for every
    Arith row (signed or unsigned), so they are part of the shared
    component's contract.  Constructibility: real ZisK Arith rows have
    16-bit chunks by construction in `arith_full.rs`. -/
@[reducible]
def ChunkRangeSpec (row : ArithMulRow FGL) : Prop :=
  (row.chunks.a_0).val < 2 ^ 16 ∧ (row.chunks.a_1).val < 2 ^ 16
  ∧ (row.chunks.a_2).val < 2 ^ 16 ∧ (row.chunks.a_3).val < 2 ^ 16
  ∧ (row.chunks.b_0).val < 2 ^ 16 ∧ (row.chunks.b_1).val < 2 ^ 16
  ∧ (row.chunks.b_2).val < 2 ^ 16 ∧ (row.chunks.b_3).val < 2 ^ 16
  ∧ (row.chunks.c_0).val < 2 ^ 16 ∧ (row.chunks.c_1).val < 2 ^ 16
  ∧ (row.chunks.c_2).val < 2 ^ 16 ∧ (row.chunks.c_3).val < 2 ^ 16
  ∧ (row.chunks.d_0).val < 2 ^ 16 ∧ (row.chunks.d_1).val < 2 ^ 16
  ∧ (row.chunks.d_2).val < 2 ^ 16 ∧ (row.chunks.d_3).val < 2 ^ 16

/-- Full ArithMul row contract once the ArithTable lookup, the
    `bus_res1` mux constraint (c46), and the sixteen 16-bit chunk range
    lookups are plumbed into Compliance: carry-chain algebra + ROM
    membership + `bus_res1` pinning + 16-bit chunk bounds. -/
@[reducible]
def FullSpec (row : ArithMulRow FGL) : Prop :=
  Spec row ∧ ArithTableSpec row ∧ C46Spec row ∧ ChunkRangeSpec row

end ZiskFv.AirsClean.ArithMul
