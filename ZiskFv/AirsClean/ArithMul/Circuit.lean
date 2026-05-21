import ZiskFv.AirsClean.ArithMul.Constraints
import ZiskFv.AirsClean.ArithMul.Soundness
import ZiskFv.AirsClean.Completeness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# ArithMul Clean Component (Phase C3)

Packages ZisK's Arith AIR (MUL-mode view) as a Clean `Air.Flat.Component`:

* `arithMulElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean` (so the completeness axiom can name it). Its `main`
  emits the 20 `assertZero` algebraic constraints (9 boolean flags + 11
  carry-chain) and the operation-bus proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — the ArithMul `soundness`
  proof needs none; the 20-clause algebraic `Spec` follows from the 20
  definitional `assertZero` constraints alone, by `linear_combination`).
  `soundness` discharges the ArithMul algebraic relation
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

set_option maxHeartbeats 1000000 in
/-- ArithMul as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the 20-clause algebraic `Spec` follows from the 20 definitional
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
      · -- the ArithMul algebraic relation: the 20 definitional
        -- constraints imply the 20-clause `Spec`.
        obtain ⟨h_na, h_nb, h_nr, h_np, h_sext, h_m32, h_div, h_main_div,
                h_main_mul, h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34,
                h_c35, h_c36, h_c37, h_c38⟩ := h_holds
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · linear_combination h_na
        · linear_combination h_nb
        · linear_combination h_nr
        · linear_combination h_np
        · linear_combination h_sext
        · linear_combination h_m32
        · linear_combination h_div
        · linear_combination h_main_div
        · linear_combination h_main_mul
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

end ZiskFv.AirsClean.ArithMul
