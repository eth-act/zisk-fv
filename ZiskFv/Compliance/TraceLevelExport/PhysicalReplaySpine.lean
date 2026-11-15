import ZiskFv.Compliance.TraceLevelExport.SerializedExecutionRows
import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLowering

/-!
# Source-width physical replay spine

Every source physical row has a slot. Interior slots carry no architectural
memory event; the terminal slot carries the real architectural event list.
The source-neutrality connection is supplied separately by the actual Main
six-message exclusion, not by erasing any interaction from RAW balance.

Ordered flattening and every architectural-cut prefix are exact, including
empty executions and a nonfinal expanded source word. The Nat-indexed view
retains the old row-family tail outside the proved finite physical domain;
it does not manufacture a default event or an auxiliary Sail instruction.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open Interaction
open ZiskFv.ZiskCircuit.MemTrace

open scoped BigOperators

universe u

/-- Exact finite source-prefix successor, with no out-of-range index. -/
theorem finitePrefix_succ {m : Nat} (i : Fin m) :
    (List.finRange m).take (i.val + 1) =
      (List.finRange m).take i.val ++ [i] := by
  have hi : i.val < (List.finRange m).length := by simpa using i.isLt
  have atIndex : (List.finRange m)[i.val]'hi = i := by
    apply Fin.ext
    simp
  simp only [List.take_succ, List.getElem?_eq_getElem hi, atIndex, Option.toList_some]

private theorem finRange_map_val (m : Nat) :
    (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

variable {m : Nat} {words : Fin m → BitVec 32}
variable (L : ∀ i, SuccessfulRowLowering (words i))

/-- One slot per REAL physical source row; only the terminal slot owns the
architectural payload. The preceding slots are genuine source auxiliaries. -/
def sourceSpanSlots {α : Type u} (rows : Fin m → List α) (i : Fin m) :
    List (List α) :=
  List.replicate ((L i).width - 1) [] ++ [rows i]

@[simp] theorem sourceSpanSlots_length {α : Type u}
    (rows : Fin m → List α) (i : Fin m) :
    (sourceSpanSlots L rows i).length = (L i).width := by
  have hp := (L i).width_pos
  simp only [sourceSpanSlots, List.length_append, List.length_replicate,
    List.length_singleton]
  omega

@[simp] theorem sourceSpanSlots_flatten {α : Type u}
    (rows : Fin m → List α) (i : Fin m) :
    (sourceSpanSlots L rows i).flatten = rows i := by
  simp [sourceSpanSlots, List.flatten_append]

/-- Bounded source-prefix expansion; every index comes from the real Fin m. -/
def sourcePhysicalPrefix {α : Type u} (rows : Fin m → List α)
    (j : Nat) (_h : j ≤ m) : List (List α) :=
  ((List.finRange m).take j).flatMap (sourceSpanSlots L rows)

/-- The complete physical prefix, not a shortened replay domain. -/
def sourcePhysicalSlots {α : Type u} (rows : Fin m → List α) : List (List α) :=
  (List.finRange m).flatMap (sourceSpanSlots L rows)

@[simp] theorem sourcePhysicalPrefix_zero {α : Type u}
    (rows : Fin m → List α) (h : 0 ≤ m) :
    sourcePhysicalPrefix L rows 0 h = [] := by
  simp [sourcePhysicalPrefix]

theorem sourcePhysicalPrefix_succ {α : Type u}
    (rows : Fin m → List α) (i : Fin m) :
    sourcePhysicalPrefix L rows (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      sourcePhysicalPrefix L rows i.val (Nat.le_of_lt i.isLt) ++
        sourceSpanSlots L rows i := by
  simp only [sourcePhysicalPrefix, finitePrefix_succ, List.flatMap_append,
    List.flatMap_singleton]

/-- The finite spine has EXACTLY the source-derived physical cut length. -/
theorem sourcePhysicalPrefix_length {α : Type u}
    (rows : Fin m → List α) (j : Nat) (h : j ≤ m) :
    (sourcePhysicalPrefix L rows j h).length = rowPrefix (sourceWidth L) j := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
      have hj : j < m := by omega
      let i : Fin m := ⟨j, hj⟩
      have next := sourcePhysicalPrefix_succ L rows i
      change (sourcePhysicalPrefix L rows (j + 1) h).length = _
      rw [next, List.length_append, sourceSpanSlots_length, ih (by omega)]
      exact (prefix_succ (sourceWidth L) i).symm

@[simp] theorem sourcePhysicalPrefix_end {α : Type u} (rows : Fin m → List α) :
    sourcePhysicalPrefix L rows m (Nat.le_refl m) = sourcePhysicalSlots L rows := by
  have ht : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp)
  simp only [sourcePhysicalPrefix, sourcePhysicalSlots, ht]

@[simp] theorem sourcePhysicalSlots_length {α : Type u} (rows : Fin m → List α) :
    (sourcePhysicalSlots L rows).length = sourceEnd L := by
  rw [← sourcePhysicalPrefix_end L rows, sourcePhysicalPrefix_length]
  rfl

private theorem flatten_span_flatMap {α : Type u}
    (rows : Fin m → List α) (indices : List (Fin m)) :
    (indices.flatMap (sourceSpanSlots L rows)).flatten = indices.flatMap rows := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.flatten_append, sourceSpanSlots_flatten, ih]

/-- Ordered flattening preserves duplicates and source order, not just a Perm. -/
theorem sourcePhysicalPrefix_flatten {α : Type u}
    (rows : Fin m → List α) (j : Nat) (h : j ≤ m) :
    (sourcePhysicalPrefix L rows j h).flatten =
      ((List.finRange m).take j).flatMap rows :=
  flatten_span_flatMap L rows _

@[simp] theorem sourcePhysicalSlots_flatten {α : Type u} (rows : Fin m → List α) :
    (sourcePhysicalSlots L rows).flatten = (List.finRange m).flatMap rows :=
  flatten_span_flatMap L rows _

/-- Exact ordered decomposition at a source cut, before any replay erasure. -/
theorem sourcePhysicalSlots_split_after {α : Type u}
    (rows : Fin m → List α) (j : Nat) (h : j ≤ m) :
    sourcePhysicalSlots L rows = sourcePhysicalPrefix L rows j h ++
      ((List.finRange m).drop j).flatMap (sourceSpanSlots L rows) := by
  unfold sourcePhysicalSlots sourcePhysicalPrefix
  rw [← List.flatMap_append, List.take_append_drop]

/-- Positivity gives enough physical indices for every old architectural
index, without supplying a separate count/placement promise. -/
theorem architecturalCount_le_sourceEnd : m ≤ sourceEnd L := by
  have positive : (∑ _i : Fin m, 1) ≤ ∑ i : Fin m, (L i).width := by
    apply Finset.sum_le_sum
    intro i _
    exact Nat.succ_le_of_lt (L i).width_pos
  simpa [sourceEnd, rowPrefix, sourceWidth] using positive

theorem sourceSpanStop_le_sourceEnd (i : Fin m) :
    sourceStart L i + (L i).width ≤ sourceEnd L := by
  calc
    sourceStart L i + (L i).width =
        rowPrefix (sourceWidth L) (i.val + 1) := (prefix_succ (sourceWidth L) i).symm
    _ ≤ sourceEnd L := prefix_mono (sourceWidth L) (Nat.succ_le_of_lt i.isLt)

/-- Every physical owner slot is the actual offset in its source expansion.
This retains all auxiliary slots rather than comparing only flattened lists. -/
theorem sourcePhysicalSlots_get_at_offset {α : Type u}
    (rows : Fin m → List α) (i : Fin m) (offset : Nat)
    (inSpan : offset < (L i).width) :
    (sourcePhysicalSlots L rows)[sourceStart L i + offset]'(by
      rw [sourcePhysicalSlots_length]
      have stop := sourceSpanStop_le_sourceEnd L i
      omega) =
      (sourceSpanSlots L rows i)[offset]'(by rw [sourceSpanSlots_length]; exact inSpan) := by
  have preLength : (sourcePhysicalPrefix L rows i.val (Nat.le_of_lt i.isLt)).length =
      sourceStart L i := sourcePhysicalPrefix_length L rows i.val (Nat.le_of_lt i.isLt)
  have split : sourcePhysicalSlots L rows =
      (sourcePhysicalPrefix L rows i.val (Nat.le_of_lt i.isLt) ++ sourceSpanSlots L rows i) ++
        ((List.finRange m).drop (i.val + 1)).flatMap (sourceSpanSlots L rows) := by
    rw [sourcePhysicalSlots_split_after L rows (i.val + 1) (Nat.succ_le_of_lt i.isLt),
      sourcePhysicalPrefix_succ]
  have inside : sourceStart L i + offset <
      (sourcePhysicalPrefix L rows i.val (Nat.le_of_lt i.isLt) ++ sourceSpanSlots L rows i).length := by
    rw [List.length_append, preLength, sourceSpanSlots_length]
    omega
  have afterPrefix : (sourcePhysicalPrefix L rows i.val (Nat.le_of_lt i.isLt)).length ≤
      sourceStart L i + offset := by rw [preLength]; omega
  rw [split, List.getElem_append_left inside, List.getElem_append_right afterPrefix]
  simpa only [preLength, Nat.add_sub_cancel_left]

/-- A width-two interior slot is empty because it is the first SOURCE row,
not because an extra architectural instruction was inserted and ignored. -/
theorem sourcePhysicalSlots_expanded_first {α : Type u}
    (rows : Fin m → List α) (i : Fin m) (two : (L i).width = 2) :
    (sourcePhysicalSlots L rows)[sourceStart L i]'(by
      rw [sourcePhysicalSlots_length]
      exact sourceStart_lt_sourceEnd L i) = [] := by
  have first := sourcePhysicalSlots_get_at_offset L rows i 0 (by omega)
  simpa [sourceSpanSlots, two] using first

/-- Every physical architectural-cut prefix is the corresponding spine prefix. -/
theorem sourcePhysicalSlots_take_cut {α : Type u}
    (rows : Fin m → List α) (j : Nat) (h : j ≤ m) :
    (sourcePhysicalSlots L rows).take (rowPrefix (sourceWidth L) j) =
      sourcePhysicalPrefix L rows j h := by
  rw [sourcePhysicalSlots_split_after L rows j h,
    ← sourcePhysicalPrefix_length L rows j h, List.take_left]

/-- The total Nat family required by the EXISTING seed API. Within the exact
physical endpoint this reads an actual finite slot; outside it the existing
row-family tail is retained, rather than assigning a fabricated zero/default. -/
def sourcePhysicalRowsOf {α : Type u} (rowsOf : Nat → List α) : Nat → List α :=
  let slots := sourcePhysicalSlots L (fun i => rowsOf i.val)
  fun p => if hp : p < slots.length then slots[p] else rowsOf p

private theorem physicalRows_map_prefix {α : Type u}
    (rowsOf : Nat → List α) (cut : Nat) (hcut : cut ≤ sourceEnd L) :
    (List.range cut).map (sourcePhysicalRowsOf L rowsOf) =
      (sourcePhysicalSlots L (fun i => rowsOf i.val)).take cut := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take,
      sourcePhysicalSlots_length]
    omega
  · intro p hp hq
    have hpCut : p < cut := by simpa using hp
    have hpSlots : p < (sourcePhysicalSlots L (fun i => rowsOf i.val)).length := by
      rw [sourcePhysicalSlots_length]
      omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      sourcePhysicalRowsOf, dif_pos hpSlots]

/-- Exact prefix transport in the original seed's Nat-indexed vocabulary. -/
theorem sourcePhysicalRowsOf_prefix {α : Type u}
    (rowsOf : Nat → List α) (j : Nat) (h : j ≤ m) :
    (List.range (rowPrefix (sourceWidth L) j)).flatMap (sourcePhysicalRowsOf L rowsOf) =
      ((List.finRange m).take j).flatMap (fun i => rowsOf i.val) := by
  have hcut : rowPrefix (sourceWidth L) j ≤ sourceEnd L :=
    prefix_mono (sourceWidth L) h
  rw [List.flatMap_def, physicalRows_map_prefix L rowsOf _ hcut,
    sourcePhysicalSlots_take_cut L _ j h, sourcePhysicalPrefix_flatten]

/-- The WHOLE ordered execution-row list is unchanged by source expansion. -/
theorem sourcePhysicalRowsOf_flatten {α : Type u} (rowsOf : Nat → List α) :
    (List.range (sourceEnd L)).flatMap (sourcePhysicalRowsOf L rowsOf) =
      (List.range m).flatMap rowsOf := by
  have all := sourcePhysicalRowsOf_prefix L rowsOf m (Nat.le_refl m)
  change (List.range (sourceEnd L)).flatMap (sourcePhysicalRowsOf L rowsOf) = _ at all
  have ht : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp)
  rw [ht] at all
  calc
    (List.range (sourceEnd L)).flatMap (sourcePhysicalRowsOf L rowsOf) =
        (List.finRange m).flatMap (fun i => rowsOf i.val) := all
    _ = ((List.finRange m).map Fin.val).flatMap rowsOf := by
      rw [List.flatMap_map]
    _ = (List.range m).flatMap rowsOf := by rw [finRange_map_val]

/-- Replay preserves the EXACT finite memory prefix at each source cut. -/
theorem sourcePhysicalRowsOf_replay_prefix
    (rowsOf : Nat → List (MemoryBusEntry FGL))
    (memInit : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (h : j ≤ m) :
    replayMemoryAfterBusRows memInit
      ((List.range (rowPrefix (sourceWidth L) j)).flatMap (sourcePhysicalRowsOf L rowsOf)) =
      replayMemoryAfterBusRows memInit
        (((List.finRange m).take j).flatMap (fun i => rowsOf i.val)) := by
  rw [sourcePhysicalRowsOf_prefix]

/-- Recount only the unchanged accepted witness. The finite count bound is
derived from actual source/decode bounds at the old-domain call site below.
The weak inequality also handles a genuinely empty Main table at count zero. -/
def recountWithinMain {n : Nat} (trace : AcceptedZiskTrace n)
    (count : Nat) (room : count ≤ trace.mainTable.table.length) :
    AcceptedZiskTrace count where
  programLength := trace.programLength
  program := trace.program
  witness := trace.witness
  constraints_hold := trace.constraints_hold
  channels_balanced := trace.channels_balanced
  mem_replay_table := trace.mem_replay_table
  mem_replay_source_covers := trace.mem_replay_source_covers
  transitions_hold := trace.transitions_hold
  cyclic_successor_transitions_hold := trace.cyclic_successor_transitions_hold
  main_height := by
    intro table member component row
    rw [ExecutionSpanLegacy.all_main_tables_eq_selected (trace := trace) table member component]
    exact Nat.lt_of_lt_of_le row.isLt room

/-- Count-independent accepted replay data stays definitionally the SAME
data. This internal equality premise is discharged by source expansion below,
never added to the root's execution interface or replaced by a safe-swap oracle. -/
private def readSoundInputs_recount_of_flatten
    {n : Nat} (trace : AcceptedZiskTrace n) (count : Nat)
    (room : count ≤ trace.mainTable.table.length)
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (oldRows newRows : Nat → List (MemoryBusEntry FGL))
    (present : MutableMemPresent trace.witness)
    (inputs : BootSegmentReadSoundInputs trace memInit oldRows present)
    (flatten_eq : (List.range count).flatMap newRows =
      (List.range n).flatMap oldRows) :
    BootSegmentReadSoundInputs (recountWithinMain trace count room)
      memInit newRows present where
  initialMemory_eq := inputs.initialMemory_eq
  order := by
    change MemoryBusRowsReplaySafePermutation
      (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
        (trace.memReplayBridge present)).rows ((List.range count).flatMap newRows)
    rw [flatten_eq]
    exact inputs.order

/-- Construct the unchanged read-input record using the PROVED complete
source-expansion equality. There is no caller permutation/equality premise. -/
def recountReadSoundInputs
    {n : Nat} {sourceWords : Fin n → BitVec 32}
    (trace : AcceptedZiskTrace n)
    (lowering : ∀ i, SuccessfulRowLowering (sourceWords i))
    (room : sourceEnd lowering ≤ trace.mainTable.table.length)
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : Nat → List (MemoryBusEntry FGL))
    (present : MutableMemPresent trace.witness)
    (inputs : BootSegmentReadSoundInputs trace memInit rowsOf present) :
    BootSegmentReadSoundInputs (recountWithinMain trace (sourceEnd lowering) room)
      memInit (sourcePhysicalRowsOf lowering rowsOf) present :=
  readSoundInputs_recount_of_flatten trace (sourceEnd lowering) room memInit rowsOf
    (sourcePhysicalRowsOf lowering rowsOf) present inputs
    (sourcePhysicalRowsOf_flatten lowering rowsOf)

/-- The existing OLD raw/decode/alignment domain itself supplies successful
source widths, physical recount room, exact old starts, and transported initial
memory/ordered-replay inputs. No source success, placement, list-equality or
read-value promise is added. The empty old execution is included. This proves
these TWO read-input fields, not the complete seven-field seed or root cutover. -/
theorem old_raw_readSoundInputs_to_physical
    {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : RawProgramBinding.ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (aligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i))))
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : Nat → List (MemoryBusEntry FGL))
    (present : MutableMemPresent trace.witness)
    (inputs : BootSegmentReadSoundInputs trace memInit rowsOf present) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        ∃ room : sourceEnd lowering ≤ trace.mainTable.table.length,
          (∀ i, sourceStart lowering i = i.val) ∧
          Nonempty (BootSegmentReadSoundInputs
            (recountWithinMain trace (sourceEnd lowering) room)
            memInit (sourcePhysicalRowsOf lowering rowsOf) present) := by
  obtain ⟨selected, lowering, widths, starts, ends⟩ :=
    RawDecodeRowLowering.old_raw_source_widths_and_placement trace steps start addr rawProgram
      binding rawDecodes aligned
  have room : sourceEnd lowering ≤ trace.mainTable.table.length := by
    by_cases hn : 0 < n
    · let last : Fin n := ⟨n - 1, by omega⟩
      have final : last.val + 1 = n := by dsimp [last]; omega
      rw [ends last final]
      exact Nat.le_of_lt (ExecutionSpanLegacy.producer_has_successor last (steps last)
        (rowDecode_of_programDecode trace last
          (programDecode_of_rawProgramDecode trace last (steps last) start addr
            rawProgram binding (rawDecodes last))))
    · have hn0 : n = 0 := by omega
      subst n
      simp [sourceEnd, rowPrefix]
  refine ⟨selected, lowering, room, starts, ⟨?_⟩⟩
  exact recountReadSoundInputs trace lowering room memInit rowsOf present inputs


/-- Genuine successful nonfinal two-row JALR followed by the genuine one-row
ADDI has THREE physical slots in order. Payloads here test positions only;
this does not assert that JALR/NOP emits arbitrary mutable memory events. -/
theorem nonfinal_jalr_physical_spine_slots {α : Type u}
    (rows : Fin 2 → List α) :
    sourcePhysicalSlots nonfinalJalrLowering rows = [[], rows 0, rows 1] := by
  have first : (nonfinalJalrLowering (0 : Fin 2)).width = 2 := sourceJalrTwo_width
  have second : (nonfinalJalrLowering (1 : Fin 2)).width = 1 := sourceAddiOne_width
  change sourceSpanSlots nonfinalJalrLowering rows (0 : Fin 2) ++
    (sourceSpanSlots nonfinalJalrLowering rows (1 : Fin 2) ++ []) = _
  simp [sourceSpanSlots, first, second]

end ZiskFv.Compliance.SerializedExecutionRows
