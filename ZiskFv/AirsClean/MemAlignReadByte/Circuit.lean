import ZiskFv.AirsClean.MemAlignReadByte.Constraints
import ZiskFv.AirsClean.MemAlignReadByte.Soundness
import ZiskFv.AirsClean.Completeness
import ZiskFv.Channels.RangeBusSoundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlignReadByte Clean Component (Phase C2)

Packages ZisK's MemAlignReadByte AIR as a Clean `Air.Flat.Component`:

* `memAlignReadByteElaborated` — the `ElaboratedCircuit` over `main` —
  lives in `Constraints.lean` (so the completeness axiom can name it).
  Its `main` emits the 4 `assertZero` algebraic constraints and the
  memory-bus proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — the MemAlignReadByte
  `soundness` proof needs none; the algebraic Spec clause follows from the
  definitional `composed_value` constraint alone). `soundness` discharges
  the MemAlignReadByte algebraic relation (`MemAlignReadByte.soundness`),
  drawing the `byte_value` `bits(8)` range bound from `range_bus_sound`.
  `completeness` is the declared axiom `memAlignReadByte_circuit_completeness`
  (`AirsClean/Completeness.lean`; plan D-COMPLETE — zisk-fv is
  soundness-only).
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Axioms in the closure: `memAlignReadByte_circuit_completeness` (completeness-
direction, non-security-critical) and `range_bus_sound` (the range-checker
bus — a pre-existing trust-ledger axiom, retired epic-terminal). NO new
soundness axiom — the `soundness` field is genuinely proved (the algebraic
relation follows from the definitional `assertZero` with the single range
clause from `range_bus_sound`). No `sorry`.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.RangeBusSoundness (range_bus_sound)
open Air.Flat

set_option maxHeartbeats 1000000 in
/-- MemAlignReadByte as a Clean `GeneralFormalCircuit`. `Assumptions := True`
    — the algebraic `Spec` clause follows from the definitional
    `composed_value` `assertZero` constraint alone; the `bits(8)` range
    clause comes from `range_bus_sound` (the range-checker bus) *inside*
    `soundness`, so no caller assumption is needed (plan D-2 / F-4).

    The `soundness` field is **adapted from** `MemAlignReadByte.soundness_of_ranges`
    (`Soundness.lean`) — same `linear_combination` algebraic discharge,
    reshaped to consume the `circuit_norm`-normalized constraints (in
    `a + -b` form) directly, with the range clause fed from
    `range_bus_sound`. The three boolean selector constraints (0, 1, 2)
    are unused. -/
def circuit : GeneralFormalCircuit FGL MemAlignReadByteRow unit :=
  { memAlignReadByteElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      -- The input row reassembled from its destructured field
      -- variables — `range_bus_sound` consumes a genuine column
      -- projection off it.
      set inputRow : MemAlignReadByteRow FGL :=
        { sel_high_4b := input_sel_high_4b, sel_high_2b := input_sel_high_2b,
          sel_high_b := input_sel_high_b, direct_value := input_direct_value,
          composed_value := input_composed_value,
          value_16b := input_value_16b, value_8b := input_value_8b,
          byte_value := input_byte_value, addr_w := input_addr_w,
          step := input_step } with _
      refine ⟨?_, ?_⟩
      · -- the MemAlignReadByte algebraic relation: the definitional
        -- `composed_value` constraint implies the algebraic Spec clause;
        -- the `bits(8)` range clause comes from `range_bus_sound` over a
        -- genuine `MemAlignReadByteRow` column projection. The 3 boolean
        -- constraints (0, 1, 2) are unused.
        obtain ⟨_h0, _h1, _h2, h_composed⟩ := h_holds
        simp only [byte_value_factor, value_8b_factor, value_16b_factor]
        refine ⟨?_, ?_⟩
        · linear_combination h_composed
        -- The `bits(8)` range clause, sourced from the range-checker
        -- bus. `range_bus_sound` is applied to a genuine
        -- `MemAlignReadByteRow` column projection — the witness row is
        -- the input reassembled from its `circuit_proof_start`-
        -- destructured fields, so `col row 0` is definitionally the
        -- column value.
        · exact range_bus_sound inputRow (fun r _ => r.byte_value) 8 trivial 0
      · -- the memory-bus push's requirement: `MemBusChannel.Guarantees`
        -- is `True`.
        intro _
        trivial
    completeness := memAlignReadByte_circuit_completeness }

/-- MemAlignReadByte as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

theorem component_interactionsWith_memBus :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [((MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [((MemBusChannel.pushed (memBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, memAlignReadByteElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

set_option maxHeartbeats 1000000 in
/-- The MemAlignReadByte `Spec` for a row, derived **through the Clean
    Component `circuit`** — its proven `soundness` field — rather than
    through `MemAlignReadByte.soundness` directly. Any consumer genuinely
    depends on `circuit`; this is the C2 re-root entry point that makes
    `AirsClean/MemAlignReadByte/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the `operations`
    `whnf` explodes — plan finding F-3); the working idiom is to normalize
    its type with the `circuit_norm` simp set first, then feed it a
    constant-expression row. Mirrors `MemAlignByte.spec_via_component`. -/
theorem spec_via_component (row : MemAlignReadByteRow FGL)
    (h_composed :
      row.composed_value
        - (row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b) = 0)
    (h_b0 : row.sel_high_4b * (1 - row.sel_high_4b) = 0)
    (h_b1 : row.sel_high_2b * (1 - row.sel_high_2b) = 0)
    (h_b2 : row.sel_high_b * (1 - row.sel_high_b) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, memAlignReadByteElaborated,
    circuit_norm] at hsound
  -- The `circuit_norm`-normalized constraint goals are in `a + -b`
  -- form; re-express the caller's `a - b` hypotheses to match.
  simp only [byte_value_factor, value_8b_factor, value_16b_factor,
    sub_eq_add_neg] at h_composed h_b0 h_b1 h_b2
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { sel_high_4b := .const row.sel_high_4b, sel_high_2b := .const row.sel_high_2b,
      sel_high_b := .const row.sel_high_b, direct_value := .const row.direct_value,
      composed_value := .const row.composed_value,
      value_16b := .const row.value_16b, value_8b := .const row.value_8b,
      byte_value := .const row.byte_value, addr_w := .const row.addr_w,
      step := .const row.step }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h_b0, h_b1, h_b2, h_composed⟩

end ZiskFv.AirsClean.MemAlignReadByte
