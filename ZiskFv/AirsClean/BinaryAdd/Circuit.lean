import ZiskFv.AirsClean.BinaryAdd.Constraints
import ZiskFv.AirsClean.BinaryAdd.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# BinaryAdd Clean Component (Phase C0 — de-risk pilot)

Packages ZisK's BinaryAdd AIR as a Clean `Air.Flat.Component`:

* `binaryAddElaborated` — the `ElaboratedCircuit` over the existing `main`
  (the 4 `assertZero` constraints; no fresh witnesses).
* `circuit` — the `GeneralFormalCircuit`: `soundness` is discharged from the
  existing `BinaryAdd.soundness` proof; `completeness` is the declared axiom
  `binaryAdd_circuit_completeness` (plan decision D-COMPLETE — zisk-fv is a
  soundness-only verification; completeness is axiomatized, not proved).
* `component` — the `Air.Flat.Component`.

## Trust note

One declared axiom: `binaryAdd_circuit_completeness` — completeness-direction,
non-security-critical (a falsehood in it cannot make a wrong execution
verify). No `sorry`. The `soundness` field is genuinely proved.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks

/-- The elaborated circuit for BinaryAdd's `main` — 4 `assertZero`
    constraints, no fresh witnesses (`localLength = 0`, `unit` output). -/
@[reducible] def binaryAddElaborated : ElaboratedCircuit FGL BinaryAddRow unit where
  name := "BinaryAdd"
  main := main
  localLength _ := 0
  output _ _ := ()

/-- Honest-prover assumptions for the (axiomatized) completeness field —
    a genuine BinaryAdd row (range bounds + carry pins). -/
@[reducible] def proverAssumptions :
    BinaryAddRow FGL → ProverData FGL → ProverHint FGL → Prop :=
  fun row _ _ => Assumptions row

/-- **Completeness axiom** (plan D-COMPLETE). zisk-fv is a soundness-only
    verification and does not claim completeness; Clean's
    `GeneralFormalCircuit` makes the field mandatory, so it is filled by this
    declared, non-security-critical axiom rather than proved. -/
axiom binaryAdd_circuit_completeness :
    GeneralFormalCircuit.Completeness FGL binaryAddElaborated
      proverAssumptions (fun _ _ _ => True)

/-- BinaryAdd as a Clean `GeneralFormalCircuit`. -/
def circuit : GeneralFormalCircuit FGL BinaryAddRow unit :=
  { binaryAddElaborated with
    Assumptions := fun row _ => Assumptions row
    Spec := fun row _ _ => Spec row
    ProverAssumptions := proverAssumptions
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      obtain ⟨hb0, hc0, hb1, hc1⟩ := h_holds
      exact BinaryAdd.soundness _ h_assumptions hb0 hc0 hb1 hc1
    completeness := binaryAdd_circuit_completeness }

/-- BinaryAdd as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

end ZiskFv.AirsClean.BinaryAdd
