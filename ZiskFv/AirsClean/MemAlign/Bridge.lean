import ZiskFv.AirsClean.MemAlign.Constraints
import ZiskFv.AirsClean.MemAlign.Soundness
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Channels.MemoryBus

/-!
# `Valid_MemAlign` ↔ `MemAlignRow` compatibility bridge

The Bridge routes v1 `Valid_MemAlign` consumers through the Clean
Component's per-row Spec (16 clauses). Cross-row continuity clauses
(`down_to_up_continuity_N`, `delta_addr_definition`) live in a
separate `cross_row_at` predicate (`CrossRow.lean`) that downstream
consumers invoke once the per-row Spec is established.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open ZiskFv.Channels.MemoryBus


@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ) :
    MemAlignRow FGL where
  addr := v.addr r
  offset := v.offset r
  width := v.width r
  wr := v.wr r
  pc := v.pc r
  reset := v.reset r
  sel_up_to_down := v.sel_up_to_down r
  sel_down_to_up := v.sel_down_to_up r
  reg_0 := v.reg_0 r
  reg_1 := v.reg_1 r
  reg_2 := v.reg_2 r
  reg_3 := v.reg_3 r
  reg_4 := v.reg_4 r
  reg_5 := v.reg_5 r
  reg_6 := v.reg_6 r
  reg_7 := v.reg_7 r
  sel_0 := v.sel_0 r
  sel_1 := v.sel_1 r
  step := v.step r
  sel_2 := v.sel_2 r
  sel_3 := v.sel_3 r
  sel_4 := v.sel_4 r
  sel_5 := v.sel_5 r
  sel_6 := v.sel_6 r
  sel_7 := v.sel_7 r
  sel_prove := v.sel_prove r
  preL1 := v.preL1 r
  delta_addr := v.delta_addr r
  value_0 := v.value_0 r
  value_1 := v.value_1 r

@[reducible]
def validOfRow (row : MemAlignRow FGL) :
    ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL where
  addr := fun _ => row.addr
  offset := fun _ => row.offset
  width := fun _ => row.width
  wr := fun _ => row.wr
  pc := fun _ => row.pc
  reset := fun _ => row.reset
  sel_up_to_down := fun _ => row.sel_up_to_down
  sel_down_to_up := fun _ => row.sel_down_to_up
  reg_0 := fun _ => row.reg_0
  reg_1 := fun _ => row.reg_1
  reg_2 := fun _ => row.reg_2
  reg_3 := fun _ => row.reg_3
  reg_4 := fun _ => row.reg_4
  reg_5 := fun _ => row.reg_5
  reg_6 := fun _ => row.reg_6
  reg_7 := fun _ => row.reg_7
  sel_0 := fun _ => row.sel_0
  sel_1 := fun _ => row.sel_1
  sel_2 := fun _ => row.sel_2
  sel_3 := fun _ => row.sel_3
  sel_4 := fun _ => row.sel_4
  sel_5 := fun _ => row.sel_5
  sel_6 := fun _ => row.sel_6
  sel_7 := fun _ => row.sel_7
  step := fun _ => row.step
  delta_addr := fun _ => row.delta_addr
  sel_prove := fun _ => row.sel_prove
  value_0 := fun _ => row.value_0
  value_1 := fun _ => row.value_1
  preL1 := fun _ => row.preL1

/-- Concrete MemAlign memory-bus message:
`[wr + 1, addr * 8 + offset, step, width, value_0, value_1]`.

This is the same PIL-shaped message emitted by `memBusMessageExpr`.
-/
@[reducible]
def memBusMessage (row : MemAlignRow FGL) : MemBusMessage FGL :=
  { mem_op := row.wr + 1
    ptr := row.addr * 8 + row.offset
    timestamp := row.step
    width := row.width
    value_0 := row.value_0
    value_1 := row.value_1 }

theorem eval_memBusMessageExpr
    (env : Environment FGL) (row : Var MemAlignRow FGL) :
    eval env (memBusMessageExpr row) = memBusMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [memBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp

/-- Project a Clean MemAlign prove-row message match back to the legacy
load-provider predicate used by the existing MemAlign bridge.

The Clean message carries the real PIL tuple; the legacy predicate keeps
only the fields consumed by `bus_effect` plus explicit row pins. -/
theorem memalign_row_matches_load_entry_of_message_match_valid
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r_ma : ℕ)
    (row : MemAlignRow FGL) (e : Interaction.MemoryBusEntry FGL)
    (h_row : row = rowAt ma r_ma)
    (h_sel_prove : ma.sel_prove r_ma = 1)
    (h_sel_up_to_down : ma.sel_up_to_down r_ma = 0)
    (h_sel_down_to_up : ma.sel_down_to_up r_ma = 0)
    (h_wr : ma.wr r_ma = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (memBusMessage row) 1 2)) :
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_row_matches_load_entry
      ma r_ma e := by
  obtain ⟨_h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
  rw [h_row] at h_ptr h_v0 h_v1 h_ts
  refine ⟨h_sel_prove, h_sel_up_to_down, h_sel_down_to_up, h_wr,
    ?_, ?_, ?_, ?_, h_as⟩
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry] using h_ptr.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry] using h_ts.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry,
      ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_v0.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry,
      ZiskFv.Airs.MemoryBus.memory_entry_hi] using h_v1.symm

/-- Field projection shared by MemAlign prove and assume rows once a
PIL-shaped Clean memory-bus message has been adapted to a legacy
`MemoryBusEntry`.

This predicate intentionally does not encode protocol facts such as
`sel_prove`, `sel_up_to_down`, `sel_down_to_up`, `wr`, or `width`; those
must stay explicit at call sites so they cannot hide an RMW promise. -/
@[simp]
def memalign_row_matches_memory_entry
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ)
    (e : Interaction.MemoryBusEntry FGL) : Prop :=
  ma.addr r * 8 + ma.offset r = e.ptr
  ∧ ma.step r = e.timestamp
  ∧ ma.value_0 r = ZiskFv.Airs.MemoryBus.memory_entry_lo e
  ∧ ma.value_1 r = ZiskFv.Airs.MemoryBus.memory_entry_hi e
  ∧ e.as = 2

/-- Generic Clean MemAlign memory-entry adapter.

This is the store/RMW counterpart to
`memalign_row_matches_load_entry_of_message_match_valid`: it projects the
Clean message equality into the field equalities needed by later RMW
lemmas, without asserting any protocol-specific selector or width facts. -/
theorem memalign_row_matches_memory_entry_of_message_match_valid
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r_ma : ℕ)
    (row : MemAlignRow FGL) (e : Interaction.MemoryBusEntry FGL)
    (h_row : row = rowAt ma r_ma)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (memBusMessage row) e.multiplicity 2)) :
    memalign_row_matches_memory_entry ma r_ma e := by
  obtain ⟨_h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
  rw [h_row] at h_ptr h_v0 h_v1 h_ts
  refine ⟨?_, ?_, ?_, ?_, h_as⟩
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry] using h_ptr.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry] using h_ts.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry,
      ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_v0.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry,
      ZiskFv.Airs.MemoryBus.memory_entry_hi] using h_v1.symm

/-- The 16 per-row F-typed constraints at row `r`, expressed against
    a `Valid_MemAlign`. -/
def constraints_at (v : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ) : Prop :=
  v.wr r * (1 - v.wr r) = 0
  ∧ v.reset r * (1 - v.reset r) = 0
  ∧ v.sel_up_to_down r * (1 - v.sel_up_to_down r) = 0
  ∧ v.sel_down_to_up r * (1 - v.sel_down_to_up r) = 0
  ∧ v.sel_0 r * (1 - v.sel_0 r) = 0
  ∧ v.sel_1 r * (1 - v.sel_1 r) = 0
  ∧ v.sel_2 r * (1 - v.sel_2 r) = 0
  ∧ v.sel_3 r * (1 - v.sel_3 r) = 0
  ∧ v.sel_4 r * (1 - v.sel_4 r) = 0
  ∧ v.sel_5 r * (1 - v.sel_5 r) = 0
  ∧ v.sel_6 r * (1 - v.sel_6 r) = 0
  ∧ v.sel_7 r * (1 - v.sel_7 r) = 0
  ∧ v.preL1 r * v.pc r = 0
  ∧ v.sel_prove r * (v.sel_up_to_down r + v.sel_down_to_up r) = 0
  ∧ v.value_0 r -
      (v.sel_prove r *
        (v.sel_0 r * (v.reg_0 r + v.reg_1 r * 256 + v.reg_2 r * 65536 + v.reg_3 r * 16777216)
         + v.sel_1 r * (v.reg_1 r + v.reg_2 r * 256 + v.reg_3 r * 65536 + v.reg_4 r * 16777216)
         + v.sel_2 r * (v.reg_2 r + v.reg_3 r * 256 + v.reg_4 r * 65536 + v.reg_5 r * 16777216)
         + v.sel_3 r * (v.reg_3 r + v.reg_4 r * 256 + v.reg_5 r * 65536 + v.reg_6 r * 16777216)
         + v.sel_4 r * (v.reg_4 r + v.reg_5 r * 256 + v.reg_6 r * 65536 + v.reg_7 r * 16777216)
         + v.sel_5 r * (v.reg_5 r + v.reg_6 r * 256 + v.reg_7 r * 65536 + v.reg_0 r * 16777216)
         + v.sel_6 r * (v.reg_6 r + v.reg_7 r * 256 + v.reg_0 r * 65536 + v.reg_1 r * 16777216)
         + v.sel_7 r * (v.reg_7 r + v.reg_0 r * 256 + v.reg_1 r * 65536 + v.reg_2 r * 16777216))
       + (v.sel_up_to_down r + v.sel_down_to_up r)
         * (v.reg_0 r + v.reg_1 r * 256 + v.reg_2 r * 65536 + v.reg_3 r * 16777216)) = 0
  ∧ v.value_1 r -
      (v.sel_prove r *
        (v.sel_0 r * (v.reg_4 r + v.reg_5 r * 256 + v.reg_6 r * 65536 + v.reg_7 r * 16777216)
         + v.sel_1 r * (v.reg_5 r + v.reg_6 r * 256 + v.reg_7 r * 65536 + v.reg_0 r * 16777216)
         + v.sel_2 r * (v.reg_6 r + v.reg_7 r * 256 + v.reg_0 r * 65536 + v.reg_1 r * 16777216)
         + v.sel_3 r * (v.reg_7 r + v.reg_0 r * 256 + v.reg_1 r * 65536 + v.reg_2 r * 16777216)
         + v.sel_4 r * (v.reg_0 r + v.reg_1 r * 256 + v.reg_2 r * 65536 + v.reg_3 r * 16777216)
         + v.sel_5 r * (v.reg_1 r + v.reg_2 r * 256 + v.reg_3 r * 65536 + v.reg_4 r * 16777216)
         + v.sel_6 r * (v.reg_2 r + v.reg_3 r * 256 + v.reg_4 r * 65536 + v.reg_5 r * 16777216)
         + v.sel_7 r * (v.reg_3 r + v.reg_4 r * 256 + v.reg_5 r * 65536 + v.reg_6 r * 16777216))
       + (v.sel_up_to_down r + v.sel_down_to_up r)
         * (v.reg_4 r + v.reg_5 r * 256 + v.reg_6 r * 65536 + v.reg_7 r * 16777216)) = 0

theorem spec_of_valid
    (v : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
    h_constraints
  exact soundness (rowAt v r) h_assumptions h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16

end ZiskFv.AirsClean.MemAlign
