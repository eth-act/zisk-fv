import ZiskFv.AirsClean.MemAlignByte.Constraints
import ZiskFv.AirsClean.MemAlignByte.Soundness
import ZiskFv.AirsClean.Completeness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlignByte Clean Component (Phase C1)

Packages ZisK's MemAlignByte AIR as a Clean `Air.Flat.Component`:

* `memAlignByteElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean` (so the completeness axiom can name it). Its `main`
  emits the 9 `assertZero` algebraic constraints and the memory-bus
  proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — the MemAlignByte `soundness`
  proof needs none; the algebraic Spec follows from the 5 definitional
  constraints alone). `soundness` discharges the MemAlignByte algebraic
  relation (`MemAlignByte.soundness`). `completeness` is the declared axiom
  `memAlignByte_circuit_completeness` (`AirsClean/Completeness.lean`; plan
  D-COMPLETE — zisk-fv is soundness-only).
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Axioms in the closure: `memAlignByte_circuit_completeness` (completeness-
direction, non-security-critical). NO new soundness axiom — the `soundness`
field is genuinely proved (the algebraic relations follow from the
definitional `assertZero`s with no range reasoning, hence no
`range_bus_sound`). No `sorry`.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks
open ZiskFv.Channels.MemAlignBus (MemAlignBusChannel)

set_option maxHeartbeats 1000000 in
/-- MemAlignByte as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the algebraic `Spec` follows from the 5 definitional `assertZero`
    constraints alone; no range bounds and no caller assumption needed
    (plan D-2).

    The `soundness` field is **adapted from** `MemAlignByte.soundness`
    (`Soundness.lean`) — same `linear_combination` discharge, reshaped
    to consume the `circuit_norm`-normalized constraints (in `a + -b`
    form) directly. The four boolean constraints (0, 1, 2, 4) are
    unused, exactly as in `MemAlignByte.soundness`. -/
def circuit : GeneralFormalCircuit FGL MemAlignByteRow unit :=
  { memAlignByteElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the MemAlignByte algebraic relation: the 5 definitional
        -- constraints (3, 5, 6, 7, 8) imply the 5-clause Spec. The 4
        -- boolean constraints (0, 1, 2, 4) are unused.
        obtain ⟨_h0, _h1, _h2, h_composed, _h4, h_written, h_m0, h_m1, h_bus⟩ := h_holds
        simp only [byte_value_factor, value_8b_factor, value_16b_factor]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · linear_combination h_composed
        · linear_combination h_written
        · linear_combination h_m0
        · linear_combination h_m1
        · linear_combination h_bus
      · -- the memory-bus push's requirement: `MemAlignBusChannel.Guarantees`
        -- is `True`.
        intro _
        trivial
    completeness := memAlignByte_circuit_completeness }

/-- MemAlignByte as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

set_option maxHeartbeats 1000000 in
/-- The MemAlignByte `Spec` for a row, derived **through the Clean Component
    `circuit`** — its proven `soundness` field — rather than through
    `MemAlignByte.soundness` directly. Any consumer genuinely depends on
    `circuit`; this is the C1 re-root entry point that makes
    `AirsClean/MemAlignByte/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the `operations`
    `whnf` explodes — plan finding F-3); the working idiom is to normalize
    its type with the `circuit_norm` simp set first, then feed it a
    constant-expression row. Mirrors `BinaryAdd.spec_via_component`. -/
theorem spec_via_component (row : MemAlignByteRow FGL)
    (h_composed :
      row.composed_value
        - (row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b) = 0)
    (h_written :
      row.written_composed_value
        - (row.written_byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b) = 0)
    (h_m0 :
      row.mem_write_values_0
        - (row.sel_high_4b * (row.direct_value - row.written_composed_value)
            + row.written_composed_value) = 0)
    (h_m1 :
      row.mem_write_values_1
        - (row.sel_high_4b * (row.written_composed_value - row.direct_value)
            + row.direct_value) = 0)
    (h_bus :
      row.bus_byte
        - (row.is_write * (row.written_byte_value - row.byte_value)
            + row.byte_value) = 0)
    (h_b0 : row.sel_high_4b * (1 - row.sel_high_4b) = 0)
    (h_b1 : row.sel_high_2b * (1 - row.sel_high_2b) = 0)
    (h_b2 : row.sel_high_b * (1 - row.sel_high_b) = 0)
    (h_b4 : row.is_write * (1 - row.is_write) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, memAlignByteElaborated,
    circuit_norm] at hsound
  -- The `circuit_norm`-normalized constraint goals are in `a + -b`
  -- form; re-express the caller's `a - b` hypotheses to match.
  simp only [byte_value_factor, value_8b_factor, value_16b_factor,
    sub_eq_add_neg] at h_composed h_written h_m0 h_m1 h_bus h_b0 h_b1 h_b2 h_b4
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { sel_high_4b := .const row.sel_high_4b, sel_high_2b := .const row.sel_high_2b,
      sel_high_b := .const row.sel_high_b, direct_value := .const row.direct_value,
      composed_value := .const row.composed_value,
      written_composed_value := .const row.written_composed_value,
      written_byte_value := .const row.written_byte_value,
      value_16b := .const row.value_16b, value_8b := .const row.value_8b,
      byte_value := .const row.byte_value, addr_w := .const row.addr_w,
      step := .const row.step, is_write := .const row.is_write,
      mem_write_values_0 := .const row.mem_write_values_0,
      mem_write_values_1 := .const row.mem_write_values_1,
      bus_byte := .const row.bus_byte }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h_b0, h_b1, h_b2, h_composed, h_b4, h_written, h_m0, h_m1, h_bus⟩

end ZiskFv.AirsClean.MemAlignByte
