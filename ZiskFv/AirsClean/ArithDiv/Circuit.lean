import ZiskFv.AirsClean.ArithDiv.Constraints
import ZiskFv.AirsClean.ArithDiv.Soundness
import ZiskFv.AirsClean.Completeness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# ArithDiv Clean Component (Phase C4)

Packages the Arith AIR's **DIV carry-chain sub-circuit** as a Clean
`Air.Flat.Component`:

* `arithDivElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean` (so the completeness axiom can name it). Its `main`
  emits the 11 `assertZero` DIV carry-chain constraints (arith.pil:58-60
  + 205-209). No channel interaction — the Arith op-bus is a shared
  channel wired family-terminal (plan phase C7/CZ).
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan
  D-2 / finding F-4: a Component carries no soundness-assumptions — the
  11-clause carry-chain `Spec` follows from the 11 definitional
  `assertZero`s alone, with no range reasoning and no flag-value pins).
  `soundness` discharges the DIV carry-chain relation
  (`ArithDiv.soundness_of_constraints`). `completeness` is the declared
  axiom `arithDiv_circuit_completeness` (`AirsClean/Completeness.lean`;
  plan D-COMPLETE — zisk-fv is soundness-only).
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an
ensemble non-vacuously (the `AssumptionsConsistency` obligation becomes
trivial). Axioms in the closure: `arithDiv_circuit_completeness`
(completeness-direction, non-security-critical). **NO new soundness
axiom** — the `soundness` field is genuinely proved from the 11
`assertZero` constraints by `linear_combination` (no range reasoning,
hence no `range_bus_sound`). No `sorry`.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

set_option maxHeartbeats 1000000 in
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
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      -- `circuit_proof_start`'s `provable_struct_simp` step is far too
      -- costly on the 3-level-nested 38-field `ArithDivRow` × 11 large
      -- constraints (plan finding F-3). Discharge with the *core* of
      -- `circuit_proof_start` (just the `intro`s — no struct-
      -- decomposition `repeat`-loop), `subst` the input, then
      -- `circuit_norm`-normalize `h_holds` AND the goal together: both
      -- the 11 `assertZero` constraints and the 11 `Spec` clauses land
      -- in the same `Expression.eval`-distributed form, so
      -- `soundness_of_constraints` (over the row `eval env input_var`)
      -- closes via `linear_combination`.
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
    completeness := arithDiv_circuit_completeness }

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
          div := .const row.flags.div, main_div := .const row.flags.main_div,
          main_mul := .const row.flags.main_mul, op := .const row.flags.op,
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
