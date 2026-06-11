import ZiskFv.AirsClean.BinaryAdd.Constraints
import ZiskFv.AirsClean.BinaryAdd.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# BinaryAdd Clean Component (Phase C0 — de-risk pilot)

Packages ZisK's BinaryAdd AIR as a Clean `Air.Flat.Component`:

* `binaryAddElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` for
  soundness; completeness is intentionally a visible non-claim.
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
No completeness claim is made; the `soundness` field is genuinely proved.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- BinaryAdd as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the 8 column range bounds the soundness proof needs are supplied by
    Clean static lookups, not by a caller assumption. -/
def circuit : GeneralFormalCircuit FGL BinaryAddRow unit :=
  { binaryAddElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness is intentionally NOT claimed (zisk-fv is soundness-
    -- only). `ProverAssumptions := False` makes this field a visible
    -- non-claim. See trust/defects.md
    -- ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS.
    ProverAssumptions := fun _ _ _ => False
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the BinaryAdd algebraic relation: 4 assertZero constraints +
        -- the 8 `bits(N)` column range bounds from Clean static lookups.
        obtain ⟨ha0, ha1, hb0, hb1, hc0r, hc1r, hc2r, hc3r,
          hb0eq, hc0eq, hb1eq, hc1eq⟩ := h_holds
        exact BinaryAdd.soundness_of_ranges _
          ha0 ha1 hb0 hb1 hc0r hc1r hc2r hc3r
          hb0eq hc0eq hb1eq hc1eq
      · -- the op-bus push's requirement: `OpBusChannel.Guarantees` is `True`
        intro _
        trivial
    completeness := fun _ _ _ _ _ _ h => h.elim }

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
    (h_a0 : row.a_0.val < 2 ^ 32) (h_a1 : row.a_1.val < 2 ^ 32)
    (h_b0 : row.b_0.val < 2 ^ 32) (h_b1 : row.b_1.val < 2 ^ 32)
    (h_c0 : row.c_chunks_0.val < 2 ^ 16) (h_c1 : row.c_chunks_1.val < 2 ^ 16)
    (h_c2 : row.c_chunks_2.val < 2 ^ 16) (h_c3 : row.c_chunks_3.val < 2 ^ 16)
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
    exact ⟨h_a0, h_a1, h_b0, h_b1, h_c0, h_c1, h_c2, h_c3,
      h0, h1, h2, h3⟩

end ZiskFv.AirsClean.BinaryAdd
