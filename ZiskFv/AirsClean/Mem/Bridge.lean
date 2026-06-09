import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Channels.MemoryBus

/-!
# `Valid_Mem` ↔ `MemRow` compatibility bridge

Connects the v1 `Valid_Mem` record (parameterized over `[Circuit F ExtF C]`)
to the Clean Component's `MemRow`. The Bridge supplies:

* `rowAt v r` — projection `Valid_Mem → MemRow FGL` at row `r`
* `constraints_at v r` — the 9 F-typed Mem constraints at row `r`,
  expressed against the v1 record's named accessors
* `spec_of_valid v r h_assumptions h_constraints : Spec (rowAt v r)`
  — routes through the Component's `soundness` theorem

This is the v1 ↔ v2 compatibility shim. Phase D will remove the
`[Circuit F ExtF C]` parameterization; until then, consumers can
continue to take `m : Valid_Mem` and derive the Component Spec via
this bridge.

## Trust note

No new axioms. The Bridge is pure projection + soundness invocation.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.Channels.MemoryBus


@[reducible]
def rowAt (v : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) (r : ℕ) : MemRow FGL where
  addr := v.addr r
  step := v.step r
  sel := v.sel r
  addr_changes := v.addr_changes r
  step_dual := v.step_dual r
  sel_dual := v.sel_dual r
  value_0 := v.value_0 r
  value_1 := v.value_1 r
  wr := v.wr r
  previous_step := v.previous_step r
  increment_0 := v.increment_0 r
  increment_1 := v.increment_1 r
  read_same_addr := v.read_same_addr r

@[reducible]
def validOfRow (row : MemRow FGL) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL where
  addr := fun _ => row.addr
  step := fun _ => row.step
  sel := fun _ => row.sel
  addr_changes := fun _ => row.addr_changes
  step_dual := fun _ => row.step_dual
  sel_dual := fun _ => row.sel_dual
  value_0 := fun _ => row.value_0
  value_1 := fun _ => row.value_1
  wr := fun _ => row.wr
  previous_step := fun _ => row.previous_step
  increment_0 := fun _ => row.increment_0
  increment_1 := fun _ => row.increment_1
  read_same_addr := fun _ => row.read_same_addr
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0

/-- Concrete counterpart of Mem's provider-side PIL memory-bus message:
`[wr + 1, addr * 8, step, 8, value_0, value_1]`. -/
@[reducible]
def memBusMessage (row : MemRow FGL) : MemBusMessage FGL :=
  { mem_op := row.wr + 1
    ptr := row.addr * 8
    timestamp := row.step
    width := 8
    value_0 := row.value_0
    value_1 := row.value_1 }

/-- Concrete counterpart of Mem's pinned `dual_mem = 1` provider-side
memory-bus message: `[MEMORY_LOAD_OP, addr * 8, step_dual, 8, value_0,
value_1]`. -/
@[reducible]
def memBusDualMessage (row : MemRow FGL) : MemBusMessage FGL :=
  { mem_op := 1
    ptr := row.addr * 8
    timestamp := row.step_dual
    width := 8
    value_0 := row.value_0
    value_1 := row.value_1 }

theorem eval_memBusMessageExpr
    (env : Environment FGL) (row : Var MemRow FGL) :
    eval env (memBusMessageExpr row) = memBusMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [memBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp

theorem eval_memBusDualMessageExpr
    (env : Environment FGL) (row : Var MemRow FGL) :
    eval env (memBusDualMessageExpr row) = memBusDualMessage (eval env row) := by
  rw [MemBusMessage.mk.injEq]
  simp only [memBusDualMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor <;> simp

/-- Payload-only Clean Mem provider adapter.

Clean balance relates Main memory pulls and Mem provider pushes by the
PIL-shaped message payload. Their legacy multiplicities have opposite
polarity, so full `matches_memory_entry` is too strong for provider-row
soundness. The Mem provider predicate only needs address-space, pointer,
timestamp, and value lanes; selector/write polarity stay explicit. -/
theorem mem_row_matches_entry_of_payload_match_valid
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) (r_mem : ℕ)
    (row : MemRow FGL) (e : Interaction.MemoryBusEntry FGL)
    (h_row : row = rowAt mem r_mem)
    (h_sel : mem.sel r_mem = 1)
    (h_legacy_addr : mem.addr r_mem = e.ptr)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload e
        (MemBusMessage.toEntry (memBusMessage row) 1 2)) :
    ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e := by
  obtain ⟨h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
  rw [h_row] at h_ptr h_v0 h_v1 h_ts
  refine ⟨h_sel, ?_, ?_, h_as, ?_, ?_⟩
  · exact h_legacy_addr
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry] using h_ts.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry,
      ZiskFv.Airs.MemoryBus.MemBridge.entry_packs_mem_row_value,
      ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_v0.symm
  · simpa [rowAt, memBusMessage, MemBusMessage.toEntry,
      ZiskFv.Airs.MemoryBus.MemBridge.entry_packs_mem_row_value,
      ZiskFv.Airs.MemoryBus.memory_entry_hi] using h_v1.symm

/-- Clean Mem provider messages use byte addresses (`addr * 8`), while the
legacy `mem_row_matches_entry` predicate currently stores the raw Mem
`addr` column in its `addr = ptr` field. The `h_legacy_addr` premise is
therefore an explicit compatibility pin for the legacy predicate; callers
must discharge it from the same structural address model before this can
replace `lookup_consumer_matches_provider_load`. -/
theorem mem_row_matches_entry_of_message_match_valid
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) (r_mem : ℕ)
    (row : MemRow FGL) (e : Interaction.MemoryBusEntry FGL)
    (h_row : row = rowAt mem r_mem)
    (h_sel : mem.sel r_mem = 1)
    (h_legacy_addr : mem.addr r_mem = e.ptr)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e
        (MemBusMessage.toEntry (memBusMessage row) 1 2)) :
    ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e := by
  exact mem_row_matches_entry_of_payload_match_valid
    mem r_mem row e h_row h_sel h_legacy_addr
    (ZiskFv.Airs.MemoryBus.matches_memory_payload_of_matches_memory_entry h_match)

/-- The 9 F-typed Mem row constraints at row `r`, expressed against a
    `Valid_Mem`. -/
def constraints_at (v : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) (r : ℕ) : Prop :=
  v.sel_dual r * (1 - v.sel_dual r) = 0
  ∧ (1 - v.sel r) * v.sel_dual r = 0
  ∧ v.sel r * (1 - v.sel r) = 0
  ∧ v.addr_changes r * (1 - v.addr_changes r) = 0
  ∧ v.wr r * (1 - v.wr r) = 0
  ∧ v.wr r * (1 - v.sel r) = 0
  ∧ v.read_same_addr r - (1 - v.addr_changes r) * (1 - v.wr r) = 0
  ∧ (v.addr_changes r * (1 - v.wr r)) * v.value_0 r = 0
  ∧ (v.addr_changes r * (1 - v.wr r)) * v.value_1 r = 0

/-- The generated segment/continuity Mem surface contains the current local
    Clean bridge constraints as a projection. -/
theorem constraints_at_of_segment_every_row
    (v : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (cols : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (r : ℕ)
    (h_segment : ZiskFv.Airs.Mem.segment_every_row cols v r) :
    constraints_at v r := by
  simpa [constraints_at, ZiskFv.Airs.Mem.core_every_row] using
    ZiskFv.Airs.Mem.core_every_row_of_segment_every_row
      (cols := cols) (v := v) (row := r) h_segment

/-- The complete generated Mem every-row surface contains the current local
    Clean bridge constraints as a projection. -/
theorem constraints_at_of_generated_every_row
    (v : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (seg : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (perm : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (r : ℕ)
    (h_generated : ZiskFv.Airs.Mem.generated_every_row seg perm v r) :
    constraints_at v r := by
  exact constraints_at_of_segment_every_row v seg r h_generated.1

/-- **Bridge theorem.** Given a row of a `Valid_Mem` satisfying the
    9 Clean Component constraints and the boolean range assumptions,
    the Mem per-row Spec holds. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  exact spec_via_component (rowAt v r) h_assumptions
    (by simpa only [constraints_at, Spec, rowAt] using h_constraints)

end ZiskFv.AirsClean.Mem
