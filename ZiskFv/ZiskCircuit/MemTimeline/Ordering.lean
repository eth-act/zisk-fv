import ZiskFv.Airs.Mem
import ZiskFv.AirsClean.Mem.Spec

/-!
# Mem Timeline Ordering

Circuit-side ordering facts for the memory argument.

The generated Mem AIR segment constraints sort rows by address.  These lemmas
collect the adjacent-row consequences needed by the later replay construction:
inside one address class, the carried timestamp is monotone, same-address reads
carry the previous value, and writes break the read-carry chain.
-/

namespace ZiskFv.ZiskCircuit.MemTimeline

open Goldilocks

/-- Clean per-row `Spec` exposes that a non-writing same-address row is a
same-address read. -/
theorem clean_read_same_addr_eq_one_of_same_addr_read
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_same_addr : row.addr_changes = 0)
    (h_read : row.wr = 0) :
    row.read_same_addr = 1 := by
  rw [ZiskFv.AirsClean.Mem.read_same_addr_eq_of_spec row h_spec,
    h_same_addr, h_read]
  norm_num

/-- Clean per-row `Spec` exposes that writes do not use the same-address read
carry path.  Their row value is the update value consumed by the replay fold. -/
theorem clean_read_same_addr_eq_zero_of_write
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_write : row.wr = 1) :
    row.read_same_addr = 0 := by
  rw [ZiskFv.AirsClean.Mem.read_same_addr_eq_of_spec row h_spec, h_write]
  norm_num

/-- Generated segment constraints expose that a non-writing same-address AIR row
sets the `read_same_addr` witness. -/
theorem read_same_addr_eq_one_of_same_addr_read_segment_every_row
    {cols : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {row : ℕ}
    (h : ZiskFv.Airs.Mem.segment_every_row cols mem row)
    (h_same_addr : mem.addr_changes row = 0)
    (h_read : mem.wr row = 0) :
    mem.read_same_addr row = 1 := by
  have h_core := ZiskFv.Airs.Mem.core_every_row_of_segment_every_row h
  rcases h_core with ⟨_, _, _, _, _, _, h_read_same_addr, _, _⟩
  unfold ZiskFv.Airs.Mem.read_same_addr_def_eq at h_read_same_addr
  rw [h_same_addr, h_read] at h_read_same_addr
  linear_combination h_read_same_addr

/-- Generated segment constraints expose that writes do not use the read-carry
path. -/
theorem read_same_addr_eq_zero_of_write_segment_every_row
    {cols : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {row : ℕ}
    (h : ZiskFv.Airs.Mem.segment_every_row cols mem row)
    (h_write : mem.wr row = 1) :
    mem.read_same_addr row = 0 := by
  have h_core := ZiskFv.Airs.Mem.core_every_row_of_segment_every_row h
  rcases h_core with ⟨_, _, _, _, _, _, h_read_same_addr, _, _⟩
  unfold ZiskFv.Airs.Mem.read_same_addr_def_eq at h_read_same_addr
  rw [h_write] at h_read_same_addr
  linear_combination h_read_same_addr

/-- Adjacent same-address read-chain facts at a non-boundary Mem row. -/
structure SameAddressReadChainFacts
    (cols : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (row : ℕ) : Prop where
  addr_eq_previous : mem.addr row = mem.addr (row - 1)
  read_same_addr_eq : mem.read_same_addr row = 1
  value_0_eq_previous : mem.value_0 row = mem.value_0 (row - 1)
  value_1_eq_previous : mem.value_1 row = mem.value_1 (row - 1)
  previous_step_le_current : (mem.previous_step row).val ≤ (mem.step row).val

/-- At a non-boundary row in the same address class, a read preserves both value
chunks and advances monotonically in timestamp. -/
theorem same_address_read_chain_facts_of_segment_every_row
    {cols : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {row : ℕ}
    (h : ZiskFv.Airs.Mem.segment_every_row cols mem row)
    (h_same_addr : mem.addr_changes row = 0)
    (h_read : mem.wr row = 0)
    (h_not_boundary : cols.segment_l1 row = 0)
    (h_steps : ZiskFv.Airs.Mem.step_columns_in_range mem row)
    (h_range : ZiskFv.Airs.Mem.increment_chunks_in_range mem row) :
    SameAddressReadChainFacts cols mem row where
  addr_eq_previous :=
    ZiskFv.Airs.Mem.addr_eq_previous_of_same_addr_segment_every_row
      (cols := cols) (v := mem) (row := row) h h_same_addr h_not_boundary
  read_same_addr_eq :=
    read_same_addr_eq_one_of_same_addr_read_segment_every_row
      (cols := cols) (mem := mem) (row := row) h h_same_addr h_read
  value_0_eq_previous :=
    (ZiskFv.Airs.Mem.values_eq_previous_of_read_same_addr_segment_every_row
      (cols := cols) (v := mem) (row := row) h
      (read_same_addr_eq_one_of_same_addr_read_segment_every_row
        (cols := cols) (mem := mem) (row := row) h h_same_addr h_read)
      h_not_boundary).1
  value_1_eq_previous :=
    (ZiskFv.Airs.Mem.values_eq_previous_of_read_same_addr_segment_every_row
      (cols := cols) (v := mem) (row := row) h
      (read_same_addr_eq_one_of_same_addr_read_segment_every_row
        (cols := cols) (mem := mem) (row := row) h h_same_addr h_read)
      h_not_boundary).2
  previous_step_le_current :=
    ZiskFv.Airs.Mem.previous_step_le_step_of_same_addr_segment_every_row
      (cols := cols) (v := mem) (row := row) h h_same_addr h_steps
      (by rw [h_read]; norm_num) h_range

/-- Non-boundary specialization: if the previous row has no dual event, its
primary timestamp is no later than the current same-address row. -/
theorem previous_primary_step_le_current_of_same_addr_read_segment_every_row
    {cols : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {row : ℕ}
    (h : ZiskFv.Airs.Mem.segment_every_row cols mem row)
    (h_same_addr : mem.addr_changes row = 0)
    (h_read : mem.wr row = 0)
    (h_not_boundary : cols.segment_l1 row = 0)
    (h_steps : ZiskFv.Airs.Mem.step_columns_in_range mem row)
    (h_range : ZiskFv.Airs.Mem.increment_chunks_in_range mem row)
    (h_no_dual : mem.sel_dual (row - 1) = 0) :
    (mem.step (row - 1)).val ≤ (mem.step row).val :=
  ZiskFv.Airs.Mem.previous_primary_step_le_step_of_same_addr_not_boundary_segment_every_row
    (cols := cols) (v := mem) (row := row) h h_same_addr h_not_boundary
    h_steps (by rw [h_read]; norm_num) h_range h_no_dual

/-- Non-boundary specialization: if the previous row carries a dual event, its
dual timestamp is no later than the current same-address row. -/
theorem previous_dual_step_le_current_of_same_addr_read_segment_every_row
    {cols : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {row : ℕ}
    (h : ZiskFv.Airs.Mem.segment_every_row cols mem row)
    (h_same_addr : mem.addr_changes row = 0)
    (h_read : mem.wr row = 0)
    (h_not_boundary : cols.segment_l1 row = 0)
    (h_steps : ZiskFv.Airs.Mem.step_columns_in_range mem row)
    (h_range : ZiskFv.Airs.Mem.increment_chunks_in_range mem row)
    (h_dual : mem.sel_dual (row - 1) = 1) :
    (mem.step_dual (row - 1)).val ≤ (mem.step row).val :=
  ZiskFv.Airs.Mem.previous_dual_step_le_step_of_same_addr_not_boundary_segment_every_row
    (cols := cols) (v := mem) (row := row) h h_same_addr h_not_boundary
    h_steps (by rw [h_read]; norm_num) h_range h_dual

/-- A dual Mem row's second event is chronologically no earlier than its primary
event, using the generated dual-step range check. -/
theorem primary_step_le_dual_step_of_dual_row
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {row : ℕ}
    (h_steps : ZiskFv.Airs.Mem.step_columns_in_range mem row)
    (h_wr : (mem.wr row).val < 2)
    (h_delta : ZiskFv.Airs.Mem.dual_step_delta_in_range mem row) :
    (mem.step row).val ≤ (mem.step_dual row).val :=
  ZiskFv.Airs.Mem.step_le_step_dual_of_dual_step_delta_range
    (v := mem) (row := row) h_steps h_wr h_delta

/-- Tiny two-row exercise: row 1 can be packaged as a same-address read-chain
step from row 0. -/
example
    {cols : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h : ZiskFv.Airs.Mem.segment_every_row cols mem 1)
    (h_same_addr : mem.addr_changes 1 = 0)
    (h_read : mem.wr 1 = 0)
    (h_not_boundary : cols.segment_l1 1 = 0)
    (h_steps : ZiskFv.Airs.Mem.step_columns_in_range mem 1)
    (h_range : ZiskFv.Airs.Mem.increment_chunks_in_range mem 1) :
    SameAddressReadChainFacts cols mem 1 :=
  same_address_read_chain_facts_of_segment_every_row
    (cols := cols) (mem := mem) (row := 1)
    h h_same_addr h_read h_not_boundary h_steps h_range

#print axioms clean_read_same_addr_eq_one_of_same_addr_read
#print axioms clean_read_same_addr_eq_zero_of_write
#print axioms same_address_read_chain_facts_of_segment_every_row
#print axioms previous_primary_step_le_current_of_same_addr_read_segment_every_row
#print axioms previous_dual_step_le_current_of_same_addr_read_segment_every_row
#print axioms primary_step_le_dual_step_of_dual_row

end ZiskFv.ZiskCircuit.MemTimeline
