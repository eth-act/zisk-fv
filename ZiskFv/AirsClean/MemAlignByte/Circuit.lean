import ZiskFv.AirsClean.MemAlignByte.Constraints
import ZiskFv.AirsClean.MemAlignByte.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlignByte Clean Component (Phase C1)

Packages ZisK's MemAlignByte AIR as a Clean `Air.Flat.Component`:

* `memAlignByteElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean`. Its `main`
  emits the 9 `assertZero` algebraic constraints and the memory-bus
  proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` for
  soundness; completeness is proved for honest rows built from Boolean byte
  selectors, a Boolean write flag, and 8-bit read/write byte values.
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Completeness is a constructibility claim for rows equal to
`memAlignByteRowOf ...` with `byteVal < 2^8` and `writtenByteVal < 2^8`: the
builder computes the read/write composed values, write-lane muxes, and bus
byte used by this constraint slice. It does not claim that arbitrary input
rows are honest MemAlignByte executions.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open Air.Flat

/-- Read/write byte reconstruction used by the MemAlignByte honest-row builder. -/
def memAlignByteComposedValueOf (sel_high_2b sel_high_b : Bool)
    (byte_value value_8b value_16b : FGL) : FGL :=
  byte_value * byte_value_factor (boolF sel_high_2b) (boolF sel_high_b)
    + value_8b * value_8b_factor (boolF sel_high_2b) (boolF sel_high_b)
    + value_16b * value_16b_factor (boolF sel_high_2b)

/-- Honest low write lane for MemAlignByte. -/
def memAlignByteMemWriteValues0Of (sel_high_4b : Bool)
    (direct_value written_composed_value : FGL) : FGL :=
  boolF sel_high_4b * (direct_value - written_composed_value) + written_composed_value

/-- Honest high write lane for MemAlignByte. -/
def memAlignByteMemWriteValues1Of (sel_high_4b : Bool)
    (direct_value written_composed_value : FGL) : FGL :=
  boolF sel_high_4b * (written_composed_value - direct_value) + direct_value

/-- Honest memory-bus byte mux for MemAlignByte. -/
def memAlignByteBusByteOf (isWrite : Bool) (byte_value written_byte_value : FGL) : FGL :=
  boolF isWrite * (written_byte_value - byte_value) + byte_value

lemma memAlignByteBusByteOf_eq (isWrite : Bool) (byte_value written_byte_value : FGL) :
    memAlignByteBusByteOf isWrite byte_value written_byte_value =
      if isWrite then written_byte_value else byte_value := by
  cases isWrite <;> simp [memAlignByteBusByteOf, boolF]

/-- Honest row for MemAlignByte: selectors and write flag are Boolean, byte
    operands are range-bounded naturals, and dependent mux/reconstruction
    columns are computed. -/
def memAlignByteRowOf (sel_high_4b sel_high_2b sel_high_b isWrite : Bool)
    (byteVal writtenByteVal : ℕ)
    (direct_value value_16b value_8b addr_w step : FGL) : MemAlignByteRow FGL :=
  let byte_value : FGL := (byteVal : FGL)
  let written_byte_value : FGL := (writtenByteVal : FGL)
  let composed_value :=
    memAlignByteComposedValueOf sel_high_2b sel_high_b byte_value value_8b value_16b
  let written_composed_value :=
    memAlignByteComposedValueOf sel_high_2b sel_high_b written_byte_value value_8b value_16b
  { sel_high_4b := boolF sel_high_4b
    sel_high_2b := boolF sel_high_2b
    sel_high_b := boolF sel_high_b
    direct_value := direct_value
    composed_value := composed_value
    written_composed_value := written_composed_value
    written_byte_value := written_byte_value
    value_16b := value_16b
    value_8b := value_8b
    byte_value := byte_value
    addr_w := addr_w
    step := step
    is_write := boolF isWrite
    mem_write_values_0 := memAlignByteMemWriteValues0Of sel_high_4b direct_value
      written_composed_value
    mem_write_values_1 := memAlignByteMemWriteValues1Of sel_high_4b direct_value
      written_composed_value
    bus_byte := memAlignByteBusByteOf isWrite byte_value written_byte_value }

set_option maxHeartbeats 1000000 in
/-- MemAlignByte as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the algebraic `Spec` clauses follow from the 5 definitional
    `assertZero` constraints alone; the 3 `bits(N)` range clauses come
    from Clean static lookups emitted by `main` inside `soundness`,
    so no caller assumption is needed (plan D-2 / F-4).

    The `soundness` field is **adapted from** `MemAlignByte.soundness_of_ranges`
    (`Soundness.lean`) — same `linear_combination` algebraic discharge,
    reshaped to consume the `circuit_norm`-normalized constraints (in
    `a + -b` form) directly, with the 3 range clauses fed from static
    lookup soundness. The four boolean constraints (0, 1, 2, 4) are
    unused. -/
def circuit : GeneralFormalCircuit FGL MemAlignByteRow unit :=
  { memAlignByteElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built by `memAlignByteRowOf`; fields not
    -- constrained by this slice remain free operands.
    ProverAssumptions := fun row _ _ =>
      ∃ sel_high_4b sel_high_2b sel_high_b isWrite byteVal writtenByteVal
        direct_value value_16b value_8b addr_w step,
        byteVal < 2 ^ 8 ∧ writtenByteVal < 2 ^ 8 ∧
          row = memAlignByteRowOf sel_high_4b sel_high_2b sel_high_b isWrite
            byteVal writtenByteVal direct_value value_16b value_8b addr_w step
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the MemAlignByte algebraic relation: the 5 definitional
        -- constraints (3, 5, 6, 7, 8) imply the 5 algebraic Spec
        -- clauses; the 3 `bits(N)` range clauses come from the static
        -- range lookups prepended to `main`. The 4 boolean constraints
        -- (0, 1, 2, 4) are unused.
        obtain ⟨h_bus_range, h_byte_range, h_is_write_range,
          _h0, _h1, _h2, h_composed, _h4, h_written, h_m0, h_m1, h_bus⟩ := h_holds
        simp only [byte_value_factor, value_8b_factor, value_16b_factor]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · linear_combination h_composed
        · linear_combination h_written
        · linear_combination h_m0
        · linear_combination h_m1
        · linear_combination h_bus
        · exact h_bus_range
        · exact h_byte_range
        · exact h_is_write_range
      · -- the memory-bus push's requirement: `MemBusChannel.Guarantees`
        -- is `True`.
        intro _
        trivial
    completeness := by
      circuit_proof_start [MemBusChannel, Lookup.completeness_def]
      obtain ⟨sel_high_4b, sel_high_2b, sel_high_b, isWrite, byteVal, writtenByteVal,
        direct_value, value_16b, value_8b, addr_w, step, h_byte, h_written, hrow⟩ :=
        h_assumptions
      injection hrow with h_sel_high_4b h_sel_high_2b h_sel_high_b h_direct_value
        h_composed_value h_written_composed_value h_written_byte_value h_value_16b
        h_value_8b h_byte_value h_addr_w h_step h_is_write h_mem_write_values_0
        h_mem_write_values_1 h_bus_byte
      subst_vars
      simp [memAlignByteComposedValueOf, memAlignByteMemWriteValues0Of,
        memAlignByteMemWriteValues1Of, byte_value_factor, value_8b_factor,
        value_16b_factor] at h_input ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [RangeTables.rangeTable8, RangeTables.rangeStaticTable]
        rw [memAlignByteBusByteOf_eq]
        cases isWrite
        · exact fgl_natCast_val_lt_of_lt (by decide) h_byte
        · exact fgl_natCast_val_lt_of_lt (by decide) h_written
      · simp only [RangeTables.rangeTable8, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) h_byte
      · simp only [RangeTables.rangeTable1, RangeTables.rangeStaticTable]
        cases isWrite <;> simp [boolF]
      · ring
      · ring
      · ring
      · ring
      · simp [memAlignByteBusByteOf]
        ring }

/-- MemAlignByte as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := { circuit := circuit }

/-- Project the generic Clean component `Spec` to the concrete
    MemAlignByte row `Spec`. -/
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
  simp only [component, circuit, memAlignByteElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

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
    (h_b4 : row.is_write * (1 - row.is_write) = 0)
    (h_bus_byte_range : row.bus_byte.val < 2 ^ 8)
    (h_byte_value_range : row.byte_value.val < 2 ^ 8)
    (h_is_write_range : row.is_write.val < 2 ^ 1) :
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
    exact ⟨h_bus_byte_range, h_byte_value_range, h_is_write_range,
      h_b0, h_b1, h_b2, h_composed, h_b4, h_written, h_m0, h_m1, h_bus⟩

end ZiskFv.AirsClean.MemAlignByte
