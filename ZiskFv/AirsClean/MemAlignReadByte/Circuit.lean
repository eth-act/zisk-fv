import ZiskFv.AirsClean.MemAlignReadByte.Constraints
import ZiskFv.AirsClean.MemAlignReadByte.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlignReadByte Clean Component (Phase C2)

Packages ZisK's MemAlignReadByte AIR as a Clean `Air.Flat.Component`:

* `memAlignReadByteElaborated` — the `ElaboratedCircuit` over `main` —
  lives in `Constraints.lean`.
  Its `main` emits the 4 `assertZero` algebraic constraints and the
  memory-bus proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` for
  soundness; completeness is proved for honest rows built from Boolean byte
  selectors and an 8-bit byte value.
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Completeness is a constructibility claim for rows equal to
`memAlignReadByteRowOf ...` with `byteVal < 2^8`: the builder computes the
`composed_value` byte reconstruction used by this constraint slice. It does
not claim that arbitrary input rows are honest MemAlignReadByte executions.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open Air.Flat

/-- Honest read-side byte reconstruction for MemAlignReadByte. -/
def memAlignReadByteComposedValueOf (sel_high_2b sel_high_b : Bool)
    (byte_value value_8b value_16b : FGL) : FGL :=
  byte_value * byte_value_factor (boolF sel_high_2b) (boolF sel_high_b)
    + value_8b * value_8b_factor (boolF sel_high_2b) (boolF sel_high_b)
    + value_16b * value_16b_factor (boolF sel_high_2b)

/-- Honest row for MemAlignReadByte: byte selectors are Boolean, the byte value
    is range-bounded, and `composed_value` is computed from the read-side
    reconstruction expression. -/
def memAlignReadByteRowOf (sel_high_4b sel_high_2b sel_high_b : Bool)
    (byteVal : ℕ) (direct_value value_16b value_8b addr_w step : FGL) :
    MemAlignReadByteRow FGL :=
  { sel_high_4b := boolF sel_high_4b
    sel_high_2b := boolF sel_high_2b
    sel_high_b := boolF sel_high_b
    direct_value := direct_value
    composed_value :=
      memAlignReadByteComposedValueOf sel_high_2b sel_high_b
        (byteVal : FGL) value_8b value_16b
    value_16b := value_16b
    value_8b := value_8b
    byte_value := (byteVal : FGL)
    addr_w := addr_w
    step := step }

set_option maxHeartbeats 1000000 in
/-- MemAlignReadByte as a Clean `GeneralFormalCircuit`. `Assumptions := True`
    — the algebraic `Spec` clause follows from the definitional
    `composed_value` `assertZero` constraint alone; the `bits(8)` range
    clause comes from a Clean static lookup emitted by `main` inside
    `soundness`, so no caller assumption is needed (plan D-2 / F-4).

    The `soundness` field is **adapted from** `MemAlignReadByte.soundness_of_ranges`
    (`Soundness.lean`) — same `linear_combination` algebraic discharge,
    reshaped to consume the `circuit_norm`-normalized constraints (in
    `a + -b` form) directly, with the range clause fed from static lookup
    soundness. The three boolean selector constraints (0, 1, 2)
    are unused. -/
def circuit : GeneralFormalCircuit FGL MemAlignReadByteRow unit :=
  { memAlignReadByteElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built by `memAlignReadByteRowOf`; fields not
    -- constrained by this slice remain free operands.
    ProverAssumptions := fun row _ _ =>
      ∃ sel_high_4b sel_high_2b sel_high_b byteVal
        direct_value value_16b value_8b addr_w step,
        byteVal < 2 ^ 8 ∧
          row = memAlignReadByteRowOf sel_high_4b sel_high_2b sel_high_b
            byteVal direct_value value_16b value_8b addr_w step
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the MemAlignReadByte algebraic relation: the definitional
        -- `composed_value` constraint implies the algebraic Spec clause;
        -- the `bits(8)` range clause comes from the static range lookup
        -- prepended to `main`. The 3 boolean constraints (0, 1, 2) are
        -- unused.
        obtain ⟨h_byte_range, _h0, _h1, _h2, h_composed⟩ := h_holds
        simp only [byte_value_factor, value_8b_factor, value_16b_factor]
        refine ⟨?_, ?_⟩
        · linear_combination h_composed
        · exact h_byte_range
      · -- the memory-bus push's requirement: `MemBusChannel.Guarantees`
        -- is `True`.
        intro _
        trivial
    completeness := by
      circuit_proof_start [MemBusChannel, Lookup.completeness_def]
      obtain ⟨sel_high_4b, sel_high_2b, sel_high_b, byteVal,
        direct_value, value_16b, value_8b, addr_w, step, h_byte, hrow⟩ :=
        h_assumptions
      injection hrow with h_sel_high_4b h_sel_high_2b h_sel_high_b h_direct_value
        h_composed_value h_value_16b h_value_8b h_byte_value h_addr_w h_step
      subst_vars
      simp [memAlignReadByteComposedValueOf, byte_value_factor, value_8b_factor,
        value_16b_factor] at h_input ⊢
      refine ⟨?_, ?_⟩
      · simp only [RangeTables.rangeTable8, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) h_byte
      · ring }

/-- MemAlignReadByte as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-- Project the generic Clean component `Spec` to the concrete
    MemAlignReadByte row `Spec`. -/
theorem component_spec (env : Environment FGL) :
    component.Spec env = Spec (component.rowInput env) := by
  rfl

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
    (h_b2 : row.sel_high_b * (1 - row.sel_high_b) = 0)
    (h_byte_value_range : row.byte_value.val < 2 ^ 8) :
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
    exact ⟨h_byte_value_range, h_b0, h_b1, h_b2, h_composed⟩

end ZiskFv.AirsClean.MemAlignReadByte
