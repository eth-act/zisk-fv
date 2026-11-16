import ZiskFv.AirsClean.MemAlignWriteByte.Circuit

/-! Finite WriteByte logical-row slice, independent of legacy SourceTrace and
its free otherMain reader. These fourteen cells are DATA, not a source-validity
certificate. The separate source-owned consumer must obtain them from the sole
canonical native trace getter; no arbitrary callback is accepted here.

Order: b632 pil/src/pil_helpers/traces.rs366–370 and mem_align_byte.pil8–119,
read=0/write=1. Three selectors, fourteen fields, seven F-only polynomials.
Native shape/profile/ABI, source-to-current serialized-program correlation and
live Accepted integration are NOT established merely by this finite bijection.
Range interfaces remain the existing actual lookups, not witness bits validators. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeRow

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.DualByte (DualByteChannel DualByteMessage)
open ZiskFv.AirsClean.MemAlignByte (byte_value_factor value_8b_factor value_16b_factor)

abbrev Cells := Vector FGL 14

def ofCells (cells : Cells) : MemAlignWriteByteRow FGL :=
  ⟨cells[0], cells[1], cells[2], cells[3], cells[4], cells[5], cells[6],
    cells[7], cells[8], cells[9], cells[10], cells[11], cells[12], cells[13]⟩

/-- Direct scalar constant embedding of exactly the fourteen source cells.
This avoids a whole-row serialize/extract round trip through ProvableType.const. -/
def rowVar (cells : Cells) : Var MemAlignWriteByteRow FGL :=
  ⟨.const cells[0], .const cells[1], .const cells[2], .const cells[3],
    .const cells[4], .const cells[5], .const cells[6], .const cells[7],
    .const cells[8], .const cells[9], .const cells[10], .const cells[11],
    .const cells[12], .const cells[13]⟩

theorem eval_rowVar (cells : Cells) (env : Environment FGL) :
    ProvableStruct.eval env (rowVar cells) = ofCells cells := by
  simp [circuit_norm, rowVar, ofCells]

def toCells (row : MemAlignWriteByteRow FGL) : Cells :=
  #v[row.sel_high_4b, row.sel_high_2b, row.sel_high_b, row.direct_value,
    row.composed_value, row.written_composed_value, row.written_byte_value,
    row.value_16b, row.value_8b, row.byte_value, row.addr_w, row.step,
    row.mem_write_values_0, row.mem_write_values_1]

theorem of_to (row : MemAlignWriteByteRow FGL) : ofCells (toCells row) = row := by
  cases row
  rfl

theorem to_of (cells : Cells) : toCells (ofCells cells) = cells := by
  apply Vector.ext
  intro index hindex
  interval_cases index <;> rfl

/-- No extra per-row gauge/auxiliary field is present in this local data view. -/
theorem cells_injective : Function.Injective ofCells := by
  intro left right h
  have := congrArg toCells h
  simpa only [to_of] using this

theorem rows_injective : Function.Injective toCells := by
  intro left right h
  have := congrArg ofCells h
  simpa only [of_to] using this

/-- Source expression factors written over actual column positions, independent
of the existing row Spec. No stage2/public/exposed/default-zero reader is used. -/
def sourceByteFactor (cells : Cells) : FGL :=
  16777216 * cells[1] * cells[2] + 65536 * cells[1] * (1 - cells[2]) +
    256 * (1 - cells[1]) * cells[2] + (1 - cells[1]) * (1 - cells[2])

def source8Factor (cells : Cells) : FGL :=
  16777216 * cells[1] * (1 - cells[2]) + 65536 * cells[1] * cells[2] +
    256 * (1 - cells[1]) * (1 - cells[2]) + (1 - cells[1]) * cells[2]

def source16Factor (cells : Cells) : FGL := 65536 * (1 - cells[1]) + cells[1]

/-- Exactly source c0..c6, in order, without ranges or extra input validators. -/
def residuals (cells : Cells) : Vector FGL 7 :=
  #v[cells[0] * (1 - cells[0]), cells[1] * (1 - cells[1]),
    cells[2] * (1 - cells[2]),
    cells[4] - (cells[9] * sourceByteFactor cells + cells[8] * source8Factor cells +
      cells[7] * source16Factor cells),
    cells[5] - (cells[6] * sourceByteFactor cells + cells[8] * source8Factor cells +
      cells[7] * source16Factor cells),
    cells[12] - (cells[0] * (cells[3] - cells[5]) + cells[5]),
    cells[13] - (cells[0] * (cells[5] - cells[3]) + cells[3])]

def ResidualsHold (cells : Cells) : Prop :=
  (residuals cells)[0] = 0 ∧ (residuals cells)[1] = 0 ∧
  (residuals cells)[2] = 0 ∧ (residuals cells)[3] = 0 ∧
  (residuals cells)[4] = 0 ∧ (residuals cells)[5] = 0 ∧ (residuals cells)[6] = 0

theorem residuals_iff_polynomialSpec (cells : Cells) :
    ResidualsHold cells ↔ PolynomialSpec (ofCells cells) := by
  simp [ResidualsHold, residuals, PolynomialSpec, ofCells, sourceByteFactor,
    source8Factor, source16Factor, byte_value_factor, value_8b_factor,
    value_16b_factor, sub_eq_zero]

/-- Actual local component operations on the computed row, not an input
certificate asserting some independently chosen row agrees with the source. -/
def operations (cells : Cells) (offset : Nat) : Operations FGL :=
  (main (rowVar cells)).operations offset

theorem spec_of_operations (cells : Cells) (offset : Nat) (env : Environment FGL)
    (h : ConstraintsHold.Soundness env (operations cells offset)) : Spec (ofCells cells) := by
  have hs := spec_of_main_constraints offset env (rowVar cells) h
  simpa only [ProvableStruct.eval_eq_eval, eval_rowVar] using hs

theorem residuals_of_operations (cells : Cells) (offset : Nat) (env : Environment FGL)
    (h : ConstraintsHold.Soundness env (operations cells offset)) : ResidualsHold cells :=
  (residuals_iff_polynomialSpec cells).mpr (spec_of_operations cells offset env h).1

/-- All eight byte routes, classified from source equations, not from a stronger
source-shape validator or a supplied Boolean-route oracle. -/
theorem byte_routes (cells : Cells) (h : ResidualsHold cells) :
    ∃ high4 high2 high1 : Bool,
      (ofCells cells).sel_high_4b = boolF high4 ∧
      (ofCells cells).sel_high_2b = boolF high2 ∧
      (ofCells cells).sel_high_b = boolF high1 ∧
      (ofCells cells).written_composed_value - (ofCells cells).composed_value =
        ((ofCells cells).written_byte_value - (ofCells cells).byte_value) *
          (256 : FGL) ^ ((if high2 then 2 else 0) + (if high1 then 1 else 0)) ∧
      (ofCells cells).mem_write_values_0 =
        (if high4 then (ofCells cells).direct_value else (ofCells cells).written_composed_value) ∧
      (ofCells cells).mem_write_values_1 =
        (if high4 then (ofCells cells).written_composed_value else (ofCells cells).direct_value) :=
  write_routes_exhaustive (ofCells cells) ((residuals_iff_polynomialSpec cells).mp h)

/-- Honest logical cells retain every selector, limb, byte, address and step
route; only existing Spec's real lookup ranges restrict free operands. -/
def honestCells (high4 high2 high1 : Bool)
    (byte writtenByte direct value16 value8 addr step : FGL) : Cells :=
  toCells (rowOf high4 high2 high1 byte writtenByte direct value16 value8 addr step)

theorem honest_polynomials (high4 high2 high1 : Bool)
    (byte writtenByte direct value16 value8 addr step : FGL) :
    ResidualsHold (honestCells high4 high2 high1 byte writtenByte direct value16 value8 addr step) := by
  apply (residuals_iff_polynomialSpec _).mpr
  rw [honestCells, of_to]
  cases high4 <;> cases high2 <;> cases high1 <;>
    simp [PolynomialSpec, rowOf, composedValueOf, boolF, byte_value_factor,
      value_8b_factor, value_16b_factor]

theorem honest_spec (high4 high2 high1 : Bool)
    (byte writtenByte direct value16 value8 addr step : FGL)
    (hw : writtenByte.val < 256) (h16 : value16.val < 65536)
    (hb : byte.val < 256) (h8 : value8.val < 256) :
    Spec (ofCells (honestCells high4 high2 high1 byte writtenByte direct value16 value8 addr step)) := by
  refine ⟨(residuals_iff_polynomialSpec _).mp
    (honest_polynomials high4 high2 high1 byte writtenByte direct value16 value8 addr step), ?_⟩
  simpa [honestCells, of_to, RangeSpec, rowOf] using And.intro hw (And.intro h16 (And.intro hb h8))

def alignedRead (cells : Cells) : MemBusMessage FGL :=
  let row := ofCells cells
  ⟨1, row.addr_w * 8, row.step, 8,
    row.sel_high_4b * (row.direct_value - row.composed_value) + row.composed_value,
    row.sel_high_4b * (row.composed_value - row.direct_value) + row.direct_value⟩

def alignedWrite (cells : Cells) : MemBusMessage FGL :=
  let row := ofCells cells
  ⟨2, row.addr_w * 8, row.step + 1, 8, row.mem_write_values_0, row.mem_write_values_1⟩

def selectedWrite (cells : Cells) : MemBusMessage FGL :=
  let row := ofCells cells
  ⟨2, row.addr_w * 8 + (row.sel_high_4b * 4 + row.sel_high_2b * 2 + row.sel_high_b),
    row.step, 1, row.written_byte_value, 0⟩

def dualRead (cells : Cells) : DualByteMessage FGL :=
  ⟨(ofCells cells).byte_value, (ofCells cells).value_8b⟩

/-- The four actual row messages, retaining the aligned load/store as distinct
pulls and selected one-byte store as a push. Padding is NOT row emission. -/
def interactionValues (cells : Cells) : List (Interaction FGL) :=
  [MemBusChannel.pulledValue (alignedRead cells),
    MemBusChannel.pulledValue (alignedWrite cells),
    MemBusChannel.pushedValue (selectedWrite cells),
    DualByteChannel.pulledValue (dualRead cells)]

theorem interaction_multiplicities (cells : Cells) :
    (interactionValues cells).map Interaction.mult = [-1, -1, 1, -1] := rfl

theorem alignedRead_expr (cells : Cells) (env : Environment FGL) :
    ProvableStruct.eval env (memReadMessageExpr (rowVar cells)) =
      alignedRead cells := by
  simp [circuit_norm, alignedRead, ofCells, rowVar, sub_eq_add_neg]

theorem alignedWrite_expr (cells : Cells) (env : Environment FGL) :
    ProvableStruct.eval env (memWriteMessageExpr (rowVar cells)) =
      alignedWrite cells := by
  simp [circuit_norm, alignedWrite, ofCells, rowVar]

theorem selectedWrite_expr (cells : Cells) (env : Environment FGL) :
    ProvableStruct.eval env (memBusMessageExpr (rowVar cells)) =
      selectedWrite cells := by
  simp [circuit_norm, selectedWrite, ofCells, rowVar]

theorem dualRead_expr (cells : Cells) (env : Environment FGL) :
    ProvableStruct.eval env (dualByteMessageExpr (rowVar cells)) =
      dualRead cells := by
  simp [circuit_norm, dualRead, ofCells, rowVar]

/-- Actual compiled local operations expose exactly these four interactions.
Neither static range membership nor Direct padding is added as a row message. -/
theorem operations_interactions (cells : Cells) (offset : Nat) :
    (operations cells offset).interactions =
      [(MemBusChannel.pulled
        (memReadMessageExpr (rowVar cells))).toRaw,
       (MemBusChannel.pulled
        (memWriteMessageExpr (rowVar cells))).toRaw,
       (MemBusChannel.pushed
        (memBusMessageExpr (rowVar cells))).toRaw,
       (DualByteChannel.pulled
        (dualByteMessageExpr (rowVar cells))).toRaw] := by
  simp [operations, main, circuit_norm, Operations.interactions]

theorem operations_interaction_values (cells : Cells) (offset : Nat)
    (env : Environment FGL) :
    ((operations cells offset).interactions.map (fun interaction => interaction.eval env)) =
      interactionValues cells := by
  rw [operations_interactions]
  simp only [List.map_cons, List.map_nil, Channel.eval_pulled, Channel.eval_pushed,
    ProvableStruct.eval_eq_eval, alignedRead_expr, alignedWrite_expr,
    selectedWrite_expr, dualRead_expr]
  rfl

end ZiskFv.AirsClean.MemAlignWriteByte.NativeRow
