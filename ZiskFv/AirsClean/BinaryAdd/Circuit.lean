import ZiskFv.AirsClean.BinaryAdd.Constraints
import ZiskFv.AirsClean.BinaryAdd.Soundness
import ZiskFv.AirsClean.Completeness
import ZiskFv.Channels.RangeBusSoundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# BinaryAdd Clean Component (Phase C0 — de-risk pilot)

Packages ZisK's BinaryAdd AIR as a Clean `Air.Flat.Component`:

* `binaryAddElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean` (so the completeness axiom can name it).
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — every fact comes from its
  constraints or its channel interactions). `soundness` discharges the
  BinaryAdd relation from the 4 constraints (`soundness_of_ranges`), drawing
  the 8 column range bounds from `range_bus_sound` (the range-checker bus).
  `completeness` is the declared axiom `binaryAdd_circuit_completeness`
  (`AirsClean/Completeness.lean`; plan D-COMPLETE — zisk-fv is soundness-only).
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
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.RangeBusSoundness (range_bus_sound)

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

theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, binaryAddElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

/-- The BinaryAdd `Spec` for a row, derived **through the Clean Component
    `circuit`** — its proven `soundness` field — rather than through
    `BinaryAdd.soundness` directly. Any consumer genuinely depends on
    `circuit`; this is the C0d re-root entry point that makes
    `AirsClean/BinaryAdd/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the `operations`
    `whnf` explodes); the working idiom is to normalize its type with the
    `circuit_norm` simp set first, then feed it a constant-expression row. -/
theorem spec_via_component (row : BinaryAddRow FGL)
    (h0 : row.cout_0 * (1 + -row.cout_0) = 0)
    (h1 : row.a_0 + row.b_0
            + -(row.cout_0 * 4294967296 + row.c_chunks_1 * 65536 + row.c_chunks_0) = 0)
    (h2 : row.cout_1 * (1 + -row.cout_1) = 0)
    (h3 : row.a_1 + row.b_1 + row.cout_0
            + -(row.cout_1 * 4294967296 + row.c_chunks_3 * 65536 + row.c_chunks_2) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, binaryAddElaborated,
    circuit_norm] at hsound
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { a_0 := .const row.a_0, a_1 := .const row.a_1,
      b_0 := .const row.b_0, b_1 := .const row.b_1,
      c_chunks_0 := .const row.c_chunks_0, c_chunks_1 := .const row.c_chunks_1,
      c_chunks_2 := .const row.c_chunks_2, c_chunks_3 := .const row.c_chunks_3,
      cout_0 := .const row.cout_0, cout_1 := .const row.cout_1 }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h0, h1, h2, h3⟩

end ZiskFv.AirsClean.BinaryAdd
