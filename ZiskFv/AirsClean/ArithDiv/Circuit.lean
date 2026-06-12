import ZiskFv.AirsClean.ArithDiv.Constraints
import ZiskFv.AirsClean.ArithDiv.Soundness
import ZiskFv.Airs.Arith.CarryChainCompleteness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# ArithDiv Clean Component (Phase C4)

Packages the Arith AIR's **DIV carry-chain sub-circuit** as a Clean
`Air.Flat.Component`:

* `arithDivElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean`. Its `main`
  emits the 11 `assertZero` DIV carry-chain constraints (arith.pil:58-60
  + 205-209). No channel interaction — the Arith op-bus is a shared
  channel wired family-terminal (plan phase C7/CZ).
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan
  D-2 / finding F-4: a Component carries no soundness-assumptions — the
  11-clause carry-chain `Spec` follows from the 11 definitional
  `assertZero`s alone, with no range reasoning and no flag-value pins).
  `soundness` discharges the DIV carry-chain relation; completeness is
  intentionally a visible non-claim.
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an
ensemble non-vacuously (the `AssumptionsConsistency` obligation becomes
trivial). No completeness claim is made. The `soundness` field is
genuinely proved from the 11 `assertZero` constraints by
`linear_combination` (no range reasoning, hence no `range_bus_sound`).
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks
open ZiskFv.Airs.ArithCarryChainCompleteness

/-- Columns not constrained by the unsigned DIV carry-chain completeness slice. -/
structure ArithDivFreeCols where
  sext : FGL
  div_by_zero : FGL
  div_overflow : FGL
  main_div : FGL
  main_mul : FGL
  signed : FGL
  range_ab : FGL
  range_cd : FGL
  op : FGL
  bus_res1 : FGL
  multiplicity : FGL

def arithDivE0 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 0 : FGL) * (chunk16 b 0 : FGL) + (chunk16 (c % b) 0 : FGL) -
    (chunk16 c 0 : FGL)

def arithDivE1 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 1 : FGL) * (chunk16 b 0 : FGL) +
    (chunk16 (c / b) 0 : FGL) * (chunk16 b 1 : FGL) + (chunk16 (c % b) 1 : FGL) -
    (chunk16 c 1 : FGL)

def arithDivE2 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 2 : FGL) * (chunk16 b 0 : FGL) +
    (chunk16 (c / b) 1 : FGL) * (chunk16 b 1 : FGL) +
    (chunk16 (c / b) 0 : FGL) * (chunk16 b 2 : FGL) + (chunk16 (c % b) 2 : FGL) -
    (chunk16 c 2 : FGL)

def arithDivE3 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 3 : FGL) * (chunk16 b 0 : FGL) +
    (chunk16 (c / b) 2 : FGL) * (chunk16 b 1 : FGL) +
    (chunk16 (c / b) 1 : FGL) * (chunk16 b 2 : FGL) +
    (chunk16 (c / b) 0 : FGL) * (chunk16 b 3 : FGL) + (chunk16 (c % b) 3 : FGL) -
    (chunk16 c 3 : FGL)

def arithDivE4 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 3 : FGL) * (chunk16 b 1 : FGL) +
    (chunk16 (c / b) 2 : FGL) * (chunk16 b 2 : FGL) +
    (chunk16 (c / b) 1 : FGL) * (chunk16 b 3 : FGL)

def arithDivE5 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 3 : FGL) * (chunk16 b 2 : FGL) +
    (chunk16 (c / b) 2 : FGL) * (chunk16 b 3 : FGL)

def arithDivE6 (c b : ℕ) : FGL :=
  (chunk16 (c / b) 3 : FGL) * (chunk16 b 3 : FGL)

def arithDivE7 (_c _b : ℕ) : FGL :=
  0

lemma arithDivQuotient_lt (c b : ℕ) (hc : c < 65536 ^ 4) :
    c / b < 65536 ^ 4 := by
  have hle : c / b ≤ c := Nat.div_le_self c b
  omega

lemma arithDivRemainder_lt (c b : ℕ) (hb : b < 65536 ^ 4) (hb_ne : b ≠ 0) :
    c % b < 65536 ^ 4 := by
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne
  have hmod := Nat.mod_lt c hb_pos
  omega

lemma arithDivChainSum_zero (c b : ℕ) (hc : c < 65536 ^ 4) (hb : b < 65536 ^ 4)
    (hb_ne : b ≠ 0) :
    arithDivE0 c b + arithDivE1 c b * (65536 : FGL) +
      arithDivE2 c b * (65536 : FGL) ^ 2 + arithDivE3 c b * (65536 : FGL) ^ 3 +
      arithDivE4 c b * (65536 : FGL) ^ 4 + arithDivE5 c b * (65536 : FGL) ^ 5 +
      arithDivE6 c b * (65536 : FGL) ^ 6 + arithDivE7 c b * (65536 : FGL) ^ 7 =
        0 := by
  have hq := arithDivQuotient_lt c b hc
  have hr := arithDivRemainder_lt c b hb hb_ne
  have hq_decomp := fgl_decomp4 (c / b) hq
  have hb_decomp := fgl_decomp4 b hb
  have hr_decomp := fgl_decomp4 (c % b) hr
  have hc_decomp := fgl_decomp4 c hc
  have hdiv :
      ((c / b : ℕ) : FGL) * (b : FGL) + ((c % b : ℕ) : FGL) = (c : FGL) := by
    have hcast := congrArg (fun n : ℕ => (n : FGL)) (Nat.div_add_mod c b)
    simp only [Nat.cast_add, Nat.cast_mul] at hcast
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcast
  rw [hq_decomp, hb_decomp, hr_decomp, hc_decomp] at hdiv
  unfold arithDivE0 arithDivE1 arithDivE2 arithDivE3 arithDivE4 arithDivE5 arithDivE6
    arithDivE7
  linear_combination hdiv

/-- Honest unsigned ArithDiv row built from a dividend and nonzero divisor. -/
def arithDivRowOf (c b : ℕ) (free : ArithDivFreeCols) : ArithDivRow FGL :=
  { chunks :=
      { a_0 := (chunk16 (c / b) 0 : FGL)
        a_1 := (chunk16 (c / b) 1 : FGL)
        a_2 := (chunk16 (c / b) 2 : FGL)
        a_3 := (chunk16 (c / b) 3 : FGL)
        b_0 := (chunk16 b 0 : FGL)
        b_1 := (chunk16 b 1 : FGL)
        b_2 := (chunk16 b 2 : FGL)
        b_3 := (chunk16 b 3 : FGL)
        c_0 := (chunk16 c 0 : FGL)
        c_1 := (chunk16 c 1 : FGL)
        c_2 := (chunk16 c 2 : FGL)
        c_3 := (chunk16 c 3 : FGL)
        d_0 := (chunk16 (c % b) 0 : FGL)
        d_1 := (chunk16 (c % b) 1 : FGL)
        d_2 := (chunk16 (c % b) 2 : FGL)
        d_3 := (chunk16 (c % b) 3 : FGL) }
    flags :=
      { na := 0
        nb := 0
        nr := 0
        np := 0
        sext := free.sext
        m32 := 0
        div := 1
        div_by_zero := free.div_by_zero
        div_overflow := free.div_overflow
        main_div := free.main_div
        main_mul := free.main_mul
        signed := free.signed
        range_ab := free.range_ab
        range_cd := free.range_cd
        op := free.op
        bus_res1 := free.bus_res1
        multiplicity := free.multiplicity }
    aux :=
      { carry_0 := cc0 65536 (arithDivE0 c b)
        carry_1 := cc1 65536 (arithDivE0 c b) (arithDivE1 c b)
        carry_2 := cc2 65536 (arithDivE0 c b) (arithDivE1 c b) (arithDivE2 c b)
        carry_3 := cc3 65536 (arithDivE0 c b) (arithDivE1 c b) (arithDivE2 c b)
          (arithDivE3 c b)
        carry_4 := cc4 65536 (arithDivE0 c b) (arithDivE1 c b) (arithDivE2 c b)
          (arithDivE3 c b) (arithDivE4 c b)
        carry_5 := cc5 65536 (arithDivE0 c b) (arithDivE1 c b) (arithDivE2 c b)
          (arithDivE3 c b) (arithDivE4 c b) (arithDivE5 c b)
        carry_6 := cc6 65536 (arithDivE0 c b) (arithDivE1 c b) (arithDivE2 c b)
          (arithDivE3 c b) (arithDivE4 c b) (arithDivE5 c b) (arithDivE6 c b)
        fab := 1
        na_fb := 0
        nb_fa := 0 } }

set_option maxHeartbeats 4000000 in
/-- ArithDiv (the Arith AIR's DIV carry-chain sub-circuit) as a Clean
    `GeneralFormalCircuit`. `Assumptions := True` — the 11-clause
    carry-chain `Spec` follows from the 11 definitional `assertZero`
    constraints alone (plan D-2 / F-4).

    The `soundness` field is **adapted from**
    `ArithDiv.soundness_of_constraints` (`Soundness.lean`) — the same
    11 `linear_combination` discharges, reshaped to consume the
    `circuit_norm`-normalized constraints (in `a + -b` form) directly. -/
def circuit : GeneralFormalCircuit FGL ArithDivRow unit :=
  { arithDivElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers unsigned rows built from a dividend and nonzero divisor.
    ProverAssumptions := fun row _ _ =>
      ∃ c b free, c < 65536 ^ 4 ∧ b < 65536 ^ 4 ∧ b ≠ 0 ∧
        row = arithDivRowOf c b free
    ProverSpec := fun _ _ _ => True
    soundness := by
      -- `circuit_proof_start`'s `provable_struct_simp` step is far too
      -- costly on the 3-level-nested 38-field `ArithDivRow` × 11 large
      -- constraints (plan finding F-3). Discharge with the *core* of
      -- `circuit_proof_start` (just the `intro`s — no struct-
      -- decomposition `repeat`-loop), `subst` the input, then
      -- `circuit_norm`-normalize `h_holds` AND the `Spec` goal together:
      -- both the 11 `assertZero` constraints and the 11 `Spec` clauses
      -- land in the same `Expression.eval`-distributed form, so each
      -- `Spec` clause closes by `linear_combination` against the
      -- matching constraint. (The same algebraic content as
      -- `ArithDiv.soundness_of_constraints` — adapted to the
      -- `circuit_norm`-normalized goal shape, per plan D-REFACTOR.)
      circuit_proof_start_core
      subst h_input
      refine ⟨?_, ?_⟩
      · -- normalize the 11 `assertZero` constraints AND the 11-clause
        -- `Spec` goal together — both land in the same
        -- `circuit_norm`-distributed `Expression.eval` form, so each
        -- `Spec` clause closes by `linear_combination` against the
        -- matching constraint.
        simp only [Spec, circuit_norm, main] at h_holds ⊢
        obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_holds
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · linear_combination h6
        · linear_combination h7
        · linear_combination h8
        · linear_combination h31
        · linear_combination h32
        · linear_combination h33
        · linear_combination h34
        · linear_combination h35
        · linear_combination h36
        · linear_combination h37
        · linear_combination h38
      · -- no channel interaction → empty `Operations.Requirements`.
        simp only [circuit_norm, main]
    completeness := by
      circuit_proof_start_core
      simp only [main, circuit_norm]
      obtain ⟨c, b, free, hc, hb, hb_ne, hrow⟩ := h_assumptions
      rw [hrow] at h_input
      simp only [circuit_norm] at h_input
      injection h_input with h_chunks h_flags h_aux
      injection h_chunks with h_a_0 h_a_1 h_a_2 h_a_3 h_b_0 h_b_1 h_b_2 h_b_3
        h_c_0 h_c_1 h_c_2 h_c_3 h_d_0 h_d_1 h_d_2 h_d_3
      injection h_flags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div_by_zero
        h_div_overflow h_main_div h_main_mul h_signed h_range_ab h_range_cd h_op h_bus_res1
        h_multiplicity
      injection h_aux with h_fab h_na_fb h_nb_fa h_carry_0 h_carry_1 h_carry_2
        h_carry_3 h_carry_4 h_carry_5 h_carry_6
      subst_vars
      simp only [h_a_0, h_a_1, h_a_2, h_a_3, h_b_0, h_b_1, h_b_2, h_b_3,
        h_c_0, h_c_1, h_c_2, h_c_3, h_d_0, h_d_1, h_d_2, h_d_3, h_na, h_nb,
        h_nr, h_np, h_m32, h_div, h_carry_0, h_carry_1, h_carry_2, h_carry_3,
        h_carry_4, h_carry_5, h_carry_6, h_fab, h_na_fb, h_nb_fa]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · ring
      · ring
      · ring
      · simpa [arithDivE0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_0 (B := (65536 : FGL)) (e0 := arithDivE0 c b) fgl_65536_ne_zero)
      · simpa [arithDivE1, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_1 (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) fgl_65536_ne_zero)
      · simpa [arithDivE2, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_2 (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) (e2 := arithDivE2 c b) fgl_65536_ne_zero)
      · simpa [arithDivE3, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_3 (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) (e2 := arithDivE2 c b) (e3 := arithDivE3 c b)
            fgl_65536_ne_zero)
      · simpa [arithDivE4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_4 (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) (e2 := arithDivE2 c b) (e3 := arithDivE3 c b)
            (e4 := arithDivE4 c b) fgl_65536_ne_zero)
      · simpa [arithDivE5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_5 (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) (e2 := arithDivE2 c b) (e3 := arithDivE3 c b)
            (e4 := arithDivE4 c b) (e5 := arithDivE5 c b) fgl_65536_ne_zero)
      · simpa [arithDivE6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_6 (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) (e2 := arithDivE2 c b) (e3 := arithDivE3 c b)
            (e4 := arithDivE4 c b) (e5 := arithDivE5 c b) (e6 := arithDivE6 c b)
            fgl_65536_ne_zero)
      · simpa [arithDivE7, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_last (B := (65536 : FGL)) (e0 := arithDivE0 c b)
            (e1 := arithDivE1 c b) (e2 := arithDivE2 c b) (e3 := arithDivE3 c b)
            (e4 := arithDivE4 c b) (e5 := arithDivE5 c b) (e6 := arithDivE6 c b)
            (e7 := arithDivE7 c b) fgl_65536_ne_zero
            (arithDivChainSum_zero c b hc hb hb_ne)) }

/-- ArithDiv as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

set_option maxHeartbeats 1000000 in
/-- The ArithDiv DIV carry-chain `Spec` for a row, derived **through the
    Clean Component `circuit`** — its proven `soundness` field — rather
    than through `ArithDiv.soundness_of_constraints` directly. Any
    consumer genuinely depends on `circuit`; this is the C4 re-root
    entry point that makes `AirsClean/ArithDiv/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the
    `operations` `whnf` explodes — plan finding F-3); the working idiom
    is to normalize its type with the `circuit_norm` simp set first,
    then feed it a constant-expression row. Mirrors
    `BinaryAdd.spec_via_component` / `MemAlignByte.spec_via_component`. -/
theorem spec_via_component (row : ArithDivRow FGL)
    (h_c6 : row.aux.fab
              - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
                  + 4 * row.flags.na * row.flags.nb) = 0)
    (h_c7 : row.aux.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0)
    (h_c8 : row.aux.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0)
    (h_c31 :
      row.aux.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.aux.carry_0 * 65536 = 0)
    (h_c32 :
      row.aux.fab * row.chunks.a_1 * row.chunks.b_0
        + row.aux.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.aux.carry_0
        - row.aux.carry_1 * 65536 = 0)
    (h_c33 :
      row.aux.fab * row.chunks.a_2 * row.chunks.b_0
        + row.aux.fab * row.chunks.a_1 * row.chunks.b_1
        + row.aux.fab * row.chunks.a_0 * row.chunks.b_2
        + row.chunks.a_0 * row.aux.nb_fa * row.flags.m32
        + row.chunks.b_0 * row.aux.na_fb * row.flags.m32
        - row.chunks.c_2
        + 2 * row.flags.np * row.chunks.c_2
        + row.flags.div * row.chunks.d_2
        - 2 * row.flags.nr * row.chunks.d_2
        - row.flags.np * row.flags.div * row.flags.m32
        + row.flags.nr * row.flags.m32
        + row.aux.carry_1
        - row.aux.carry_2 * 65536 = 0)
    (h_c34 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_0
        + row.aux.fab * row.chunks.a_2 * row.chunks.b_1
        + row.aux.fab * row.chunks.a_1 * row.chunks.b_2
        + row.aux.fab * row.chunks.a_0 * row.chunks.b_3
        + row.chunks.a_1 * row.aux.nb_fa * row.flags.m32
        + row.chunks.b_1 * row.aux.na_fb * row.flags.m32
        - row.chunks.c_3
        + 2 * row.flags.np * row.chunks.c_3
        + row.flags.div * row.chunks.d_3
        - 2 * row.flags.nr * row.chunks.d_3
        + row.aux.carry_2
        - row.aux.carry_3 * 65536 = 0)
    (h_c35 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_1
        + row.aux.fab * row.chunks.a_2 * row.chunks.b_2
        + row.aux.fab * row.chunks.a_1 * row.chunks.b_3
        + row.flags.na * row.flags.nb * row.flags.m32
        + row.chunks.b_0 * row.aux.na_fb * (1 - row.flags.m32)
        + row.chunks.a_0 * row.aux.nb_fa * (1 - row.flags.m32)
        - row.flags.np * row.flags.m32 * (1 - row.flags.div)
        - row.flags.np * (1 - row.flags.m32) * row.flags.div
        + row.flags.nr * (1 - row.flags.m32)
        - row.chunks.d_0 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_0 * (1 - row.flags.div)
        + row.aux.carry_3
        - row.aux.carry_4 * 65536 = 0)
    (h_c36 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_2
        + row.aux.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.a_1 * row.aux.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_1 * row.aux.na_fb * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.aux.carry_4
        - row.aux.carry_5 * 65536 = 0)
    (h_c37 :
      row.aux.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.aux.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.aux.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.aux.carry_5
        - row.aux.carry_6 * 65536 = 0)
    (h_c38 :
      65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.aux.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.aux.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.aux.carry_6 = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, arithDivElaborated,
    circuit_norm] at hsound
  -- The `circuit_norm`-normalized constraint goals are in `a + -b`
  -- form; re-express the caller's `a - b` hypotheses to match.
  simp only [sub_eq_add_neg] at h_c6 h_c7 h_c8 h_c31 h_c32 h_c33 h_c34 h_c35 h_c36 h_c37 h_c38
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { chunks :=
        { a_0 := .const row.chunks.a_0, a_1 := .const row.chunks.a_1,
          a_2 := .const row.chunks.a_2, a_3 := .const row.chunks.a_3,
          b_0 := .const row.chunks.b_0, b_1 := .const row.chunks.b_1,
          b_2 := .const row.chunks.b_2, b_3 := .const row.chunks.b_3,
          c_0 := .const row.chunks.c_0, c_1 := .const row.chunks.c_1,
          c_2 := .const row.chunks.c_2, c_3 := .const row.chunks.c_3,
          d_0 := .const row.chunks.d_0, d_1 := .const row.chunks.d_1,
          d_2 := .const row.chunks.d_2, d_3 := .const row.chunks.d_3 }
      flags :=
        { na := .const row.flags.na, nb := .const row.flags.nb,
          nr := .const row.flags.nr, np := .const row.flags.np,
          sext := .const row.flags.sext, m32 := .const row.flags.m32,
          div := .const row.flags.div,
          div_by_zero := .const row.flags.div_by_zero,
          div_overflow := .const row.flags.div_overflow,
          main_div := .const row.flags.main_div,
          main_mul := .const row.flags.main_mul, op := .const row.flags.op,
          signed := .const row.flags.signed,
          range_ab := .const row.flags.range_ab,
          range_cd := .const row.flags.range_cd,
          bus_res1 := .const row.flags.bus_res1,
          multiplicity := .const row.flags.multiplicity }
      aux :=
        { fab := .const row.aux.fab, na_fb := .const row.aux.na_fb,
          nb_fa := .const row.aux.nb_fa,
          carry_0 := .const row.aux.carry_0, carry_1 := .const row.aux.carry_1,
          carry_2 := .const row.aux.carry_2, carry_3 := .const row.aux.carry_3,
          carry_4 := .const row.aux.carry_4, carry_5 := .const row.aux.carry_5,
          carry_6 := .const row.aux.carry_6 } }
    row ?_ ?_)
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34, h_c35, h_c36, h_c37, h_c38⟩

end ZiskFv.AirsClean.ArithDiv
