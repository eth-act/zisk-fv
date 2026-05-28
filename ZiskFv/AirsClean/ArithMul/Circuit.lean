import ZiskFv.AirsClean.ArithMul.Constraints
import ZiskFv.AirsClean.ArithMul.Soundness
import ZiskFv.AirsClean.Completeness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# ArithMul Clean Component (Phase C3)

Packages ZisK's Arith AIR (MUL-mode carry-chain view) as a Clean
`Air.Flat.Component`:

* `arithMulElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean` (so the completeness axiom can name it). Its `main`
  emits the 11 `assertZero` carry-chain constraints (named-form `6/7/8`
  + `31..38`) and the operation-bus proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — the ArithMul `soundness`
  proof needs none; the 11-clause carry-chain `Spec` follows from the 11
  definitional `assertZero` constraints alone, by `linear_combination`).
  `soundness` discharges the ArithMul carry-chain relation
  (`ArithMul.soundness`). `completeness` is the declared axiom
  `arithMul_circuit_completeness` (`AirsClean/Completeness.lean`; plan
  D-COMPLETE — zisk-fv is soundness-only).
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Axioms in the closure: `arithMul_circuit_completeness` (completeness-
direction, non-security-critical). NO new soundness axiom — the `soundness`
field is genuinely proved: every `Spec` clause is a syntactic
re-expression of the corresponding `assertZero` constraint, closed by
`linear_combination`, with no range reasoning (hence no `range_bus_sound`).
No `sorry`.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel)
open Air.Flat

set_option maxHeartbeats 1000000 in
/-- ArithMul as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the 11-clause carry-chain `Spec` follows from the 11 definitional
    `assertZero` constraints alone (plan D-2 / F-4).

    The `soundness` field is **adapted from** `ArithMul.soundness`
    (`Soundness.lean`) — same per-clause `linear_combination` discharge,
    reshaped to consume the `circuit_norm`-normalized constraints
    directly. -/
def circuit : GeneralFormalCircuit FGL ArithMulRow unit :=
  { arithMulElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the ArithMul carry-chain relation: the 11 definitional
        -- constraints imply the 11-clause `Spec`.
        obtain ⟨h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34,
                h_c35, h_c36, h_c37, h_c38⟩ := h_holds
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · linear_combination h_c6
        · linear_combination h_c7
        · linear_combination h_c8
        · linear_combination h_c31
        · linear_combination h_c32
        · linear_combination h_c33
        · linear_combination h_c34
        · linear_combination h_c35
        · linear_combination h_c36
        · linear_combination h_c37
        · linear_combination h_c38
      · -- the op-bus push's requirement: `OpBusChannel.Guarantees` is `True`.
        intro _
        trivial
    completeness := arithMul_circuit_completeness }

/-- ArithMul as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-- Project the generic Clean component `Spec` to the concrete ArithMul row
    `Spec`. -/
theorem component_spec (env : Environment FGL) :
    component.Spec env = Spec (component.rowInput env) := by
  rfl

set_option maxHeartbeats 1000000 in
/-- The ArithMul component exposes exactly its primary operation-bus
    provider interaction. -/
theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (primaryOpBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (primaryOpBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, arithMulElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil,
    primaryOpBusMessageExpr]

set_option maxHeartbeats 1000000 in
/-- The ArithMul `Spec` for a row, derived **through the Clean Component
    `circuit`** — its proven `soundness` field — rather than through
    `ArithMul.soundness` directly. Any consumer genuinely depends on
    `circuit`; this is the C3 re-root entry point that makes
    `AirsClean/ArithMul/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the `operations`
    `whnf` explodes — plan finding F-3); the working idiom is to normalize
    its type with the `circuit_norm` simp set first, then feed it a
    constant-expression row. Mirrors `BinaryAdd.spec_via_component` and
    `MemAlignByte.spec_via_component`. -/
theorem spec_via_component (row : ArithMulRow FGL)
    (h_c6 : row.carries.fab - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
              + 4 * row.flags.na * row.flags.nb) = 0)
    (h_c7 : row.carries.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0)
    (h_c8 : row.carries.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0)
    (h_c31 :
        row.carries.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.carries.carry_0 * 65536 = 0)
    (h_c32 :
        row.carries.fab * row.chunks.a_1 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.carries.carry_0
        - row.carries.carry_1 * 65536 = 0)
    (h_c33 :
        row.carries.fab * row.chunks.a_2 * row.chunks.b_0
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
        - row.carries.carry_2 * 65536 = 0)
    (h_c34 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_0
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
        - row.carries.carry_3 * 65536 = 0)
    (h_c35 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_1
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
        - row.carries.carry_4 * 65536 = 0)
    (h_c36 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.carries.carry_4
        - row.carries.carry_5 * 65536 = 0)
    (h_c37 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.carries.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.carries.carry_5
        - row.carries.carry_6 * 65536 = 0)
    (h_c38 :
        65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.carries.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.carries.carry_6 = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, arithMulElaborated,
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
      carries :=
        { carry_0 := .const row.carries.carry_0, carry_1 := .const row.carries.carry_1,
          carry_2 := .const row.carries.carry_2, carry_3 := .const row.carries.carry_3,
          carry_4 := .const row.carries.carry_4, carry_5 := .const row.carries.carry_5,
          carry_6 := .const row.carries.carry_6, fab := .const row.carries.fab,
          na_fb := .const row.carries.na_fb, nb_fa := .const row.carries.nb_fa } }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34, h_c35,
      h_c36, h_c37, h_c38⟩

end ZiskFv.AirsClean.ArithMul
