import ZiskFv.AirsClean.BinaryAdd.Constraints
import ZiskFv.AirsClean.BinaryAdd.Soundness
import ZiskFv.Channels.RangeBusSoundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# BinaryAdd Clean Component (Phase C0 — de-risk pilot)

Packages ZisK's BinaryAdd AIR as a Clean `Air.Flat.Component`:

* `binaryAddElaborated` — the `ElaboratedCircuit` over the existing `main`
  (the 4 `assertZero` constraints + the op-bus push; no fresh witnesses).
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — every fact comes from its
  constraints or its channel interactions). `soundness` discharges the
  BinaryAdd relation from the 4 constraints (`soundness_of_ranges`), drawing
  the 8 column range bounds from `range_bus_sound` (the range-checker bus).
  `completeness` is the declared axiom `binaryAdd_circuit_completeness`
  (plan D-COMPLETE — zisk-fv is soundness-only).
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Axioms in the closure: `binaryAdd_circuit_completeness` (completeness-
direction, non-security-critical) and `range_bus_sound` (the range-checker
bus — a pre-existing trust-ledger axiom, retired epic-terminal). No `sorry`;
the `soundness` field is genuinely proved.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.RangeBusSoundness (range_bus_sound)

/-- The elaborated circuit for BinaryAdd's `main` — 4 `assertZero`
    constraints + the op-bus push, no fresh witnesses (`localLength = 0`,
    `unit` output). -/
@[reducible] def binaryAddElaborated : ElaboratedCircuit FGL BinaryAddRow unit where
  name := "BinaryAdd"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]

/-- **Completeness axiom** (plan D-COMPLETE). zisk-fv is a soundness-only
    verification and does not claim completeness; Clean's
    `GeneralFormalCircuit` makes the field mandatory, so it is filled by this
    declared, non-security-critical axiom rather than proved. -/
axiom binaryAdd_circuit_completeness :
    GeneralFormalCircuit.Completeness FGL binaryAddElaborated
      (fun _ _ _ => True) (fun _ _ _ => True)

/-- BinaryAdd as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the 8 column range bounds the soundness proof needs are supplied by
    `range_bus_sound`, not by a caller assumption (plan D-2). -/
def circuit : GeneralFormalCircuit FGL BinaryAddRow unit :=
  { binaryAddElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the BinaryAdd algebraic relation: 4 assertZero constraints +
        -- the 8 `bits(N)` column range bounds from the range-checker bus.
        obtain ⟨hb0, hc0, hb1, hc1⟩ := h_holds
        exact BinaryAdd.soundness_of_ranges _
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.a_0) 32 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.a_1) 32 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.b_0) 32 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.b_1) 32 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.c_chunks_0) 16 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.c_chunks_1) 16 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.c_chunks_2) 16 trivial 0)
          (range_bus_sound _ (fun (r : BinaryAddRow FGL) _ => r.c_chunks_3) 16 trivial 0)
          hb0 hc0 hb1 hc1
      · -- the op-bus push's requirement: `OpBusChannel.Guarantees` is `True`
        intro _
        trivial
    completeness := binaryAdd_circuit_completeness }

/-- BinaryAdd as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

end ZiskFv.AirsClean.BinaryAdd
