import ZiskFv.AirsClean.Mem.PhysicalSource.Domain
import Std.Data.HashMap.Lemmas

/-! Concrete mathematical SourceObject images for nonvacuity of the internal
physical constructor in BOTH native storage modes. The original native trace
and fixed buffers are allocated once, with a retained shared suffix; no list
of four million logical rows or full decoded field trace is constructed.
This is NOT a witness of all Mem AIR equations, native execution/materialization,
compiled-id/PIL authentication, or the missing stage2 auxiliary world. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.Constructibility

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Stage1.SourceColumns

private def mapEntry (name : String) (stage dim position id : Nat) : PolMap :=
  { name := name, stage := stage, dim := dim, imPol := false,
    stagePos := position, stageId := id, lengths := #[], commitId := 0,
    expId := 0, polsMapId := id }

/-- Complete stage1/stage2 dimension roster; no compiled r.id claim is made. -/
def cmMap : Array PolMap := Array.ofFn fun index : Fin 16 =>
  if before : index.val < 13 then
    mapEntry (nativeKey ⟨index.val, before⟩).1 1 1 index.val index.val
  else
    mapEntry (if index.val = 13 then "gsum" else "im_cluster")
      2 3 (3 * (index.val - 13)) (index.val - 13)

private def airName (index : Nat) : String :=
  match index with
  | 0 => "Mem.segment_id" | 1 => "Mem.is_first_segment" | 2 => "Mem.is_last_segment"
  | 3 => "Mem.previous_segment_value[0]" | 4 => "Mem.previous_segment_value[1]"
  | 5 => "Mem.previous_segment_step" | 6 => "Mem.previous_segment_addr"
  | 7 => "Mem.segment_last_value[0]" | 8 => "Mem.segment_last_value[1]"
  | 9 => "Mem.segment_last_step" | 10 => "Mem.segment_last_addr"
  | 11 => "Mem.distance_base[0]" | 12 => "Mem.distance_base[1]"
  | 13 => "Mem.distance_end[0]" | 14 => "Mem.distance_end[1]"
  | other => "Mem.im_direct[" ++ toString (other - 15) ++ "]"

def airMap : Array PolMap := Array.ofFn fun index : Fin 21 =>
  if index.val < 15 then mapEntry (airName index.val) 1 1 index.val index.val
  else mapEntry (airName index.val) 2 3 (3 * (index.val - 15)) (index.val - 15)

def setup : NativeSetup :=
  { profile := ⟨false, true, false⟩, airgroupId := 0, airId := 14,
    nBits := 22, nBitsExt := 22, nStages := 2, nConstants := 2, nPublics := 0,
    cmPolsMap := cmMap,
    constPolsMap := #[mapEntry "Mem.SEGMENT_L1" 0 1 0 0, mapEntry "__L1__" 0 1 1 1],
    airValuesMap := airMap,
    airgroupValuesMap := #[mapEntry "Zisk.gsum_result" 2 3 0 0],
    proofValuesMap := #[], publicsMap := #[],
    challengesMap := #[mapEntry "std_alpha" 2 3 0 0, mapEntry "std_gamma" 2 3 3 1],
    customCommitsMap := #[], customCommits := #[], openingPoints := #[-1, 0, 1],
    mapSectionsN := ({} : Std.HashMap String Nat).insert "cm1" 13 |>.insert "cm2" 9,
    mapOffsets := ({} : Std.HashMap (String × Bool) Nat).insert ("cm1", false) 0
      |>.insert ("cm2", false) (physicalRows * 13) }

def traceBuffer (packed : Bool) : Array UInt64 :=
  Array.replicate (physicalRows * (if packed then 4 else 13) + 5) 0

/-- Both distinct fixed columns have their own physical first-row pulse. -/
def fixedBuffer : Array FGL := Array.ofFn fun index : Fin (2 * physicalRows) =>
  if index.val < 2 then 1 else 0

def airBuffer : Array FGL := Array.ofFn fun index : Fin 33 =>
  if index.val < 15 then 0 else (index.val : FGL)

def slot (packed : Bool) : Instance FGL :=
  { metadata := ⟨0, 14, physicalRows, if packed then 4 else 13, true, packed, 0⟩,
    trace := traceBuffer packed, auxTrace := #[], customCommitsFixed := #[],
    airgroupValues := #[7, 11, 13], airvalues := airBuffer,
    challenges := #[], evals := #[], fixed := fixedBuffer }

def source (packed : Bool) : SourceObject FGL :=
  { globals := ⟨#[], #[], #[0, 0, 0, 1, 0, 0], #[]⟩,
    registry := ⟨#[⟨0, 14, false, true, 1, 1⟩], 0, #[0], #[0], #[], #[(0, 0)], #[true]⟩,
    slots := #[slot packed],
    setupRepository := ({} : Std.HashMap (Nat × Nat) NativeSetup).insert (0, 14) setup }

def occurrence (packed : Bool) : ResolvedOccurrence (source packed) :=
  ⟨⟨0, by change 0 < 1; decide⟩, by change 0 < 1; decide⟩

theorem actual_slot (packed : Bool) : (occurrence packed).slotData = slot packed := rfl

theorem slot_fixed (packed : Bool) : (slot packed).fixed = fixedBuffer := rfl

theorem traceBuffer_size (packed : Bool) :
    (traceBuffer packed).size = physicalRows * (if packed then 4 else 13) + 5 := by
  simp only [traceBuffer, Array.size_replicate]

theorem fixedBuffer_size : fixedBuffer.size = 2 * physicalRows := by
  simp only [fixedBuffer, Array.size_ofFn]

theorem fixedBuffer_pulse (row : Fin physicalRows) :
    fixedBuffer[2 * row.val + 1]? = some (FixedScan.pulse row.val) := by
  have bound : 2 * row.val + 1 < 2 * physicalRows := by omega
  have first : (2 * row.val + 1 < 2) ↔ row.val = 0 := by omega
  simp [fixedBuffer, bound, first, FixedScan.pulse]

theorem fixedBuffer_scan : FixedScan.check fixedBuffer = true :=
  (FixedScan.check_iff fixedBuffer).mpr fixedBuffer_pulse

theorem original_native_coverage (packed : Bool) :
    physicalRows * (slot packed).metadata.nColsTrace + 5 = (slot packed).trace.size := by
  simp [slot, traceBuffer]

theorem exact_setup_selected (packed : Bool) :
    (occurrence packed).setup? = some setup := by
  simp [occurrence, ResolvedOccurrence.setup?, SourceObject.setupAt?,
    SourceObject.registryEntry, ResolvedOccurrence.registryEntry, source]

theorem exact_cm1 : setup.mapSectionsN["cm1"]? = some 13 := by
  simp [setup, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem exact_group (packed : Bool) :
    NativeValuesLayout.groupWords? .mem ((occurrence packed).params false) =
      some #v[7, 11, 13] := by
  rw [NativeValuesLayout.group_reads_actual_buffer]
  rfl

theorem exact_directs (packed : Bool) :
    directBatch? (occurrence packed) =
      some #v[#v[15, 16, 17], #v[18, 19, 20], #v[21, 22, 23],
        #v[24, 25, 26], #v[27, 28, 29], #v[30, 31, 32]] := by
  simp [directBatch?, NativeValuesLayout.mem_inverse_reads_actual_buffer,
    occurrence, ResolvedOccurrence.params, paramsOf, ResolvedOccurrence.slotData,
    ResolvedOccurrence.globalSlot, source, slot, airBuffer]

/-- A genuine computed constructor succeeds on full original source buffers in
both storage modes. No free builder count, SourceValid/profile-success premise
or native-world/AIR-validity assertion is used. -/
theorem constructor_nonvacuous (packed : Bool) :
    (fromResolved? (occurrence packed)).isSome = true := by
  unfold fromResolved?
  split
  · rename_i absent
    simp [exact_setup_selected] at absent
  · rename_i selectedSetup selected
    have equal := Option.some.inj (selected.symm.trans (exact_setup_selected packed))
    subst selectedSetup
    split
    · rename_i absent
      simp [exact_cm1] at absent
    · rename_i selectedCm1 selected
      have equal := Option.some.inj (selected.symm.trans exact_cm1)
      subst selectedCm1
      split_ifs with checked
      · split
        · rename_i absent
          simp [exact_group] at absent
        · split
          · rename_i absent
            simp [exact_directs] at absent
          · rfl
      · apply False.elim
        apply checked
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, ?_, ?_⟩
        · change 0 < (if packed then 4 else 13)
          cases packed <;> decide
        · rw [actual_slot]
          simp only [slot, traceBuffer_size]
          change physicalRows * (if packed then 4 else 13) ≤
            physicalRows * (if packed then 4 else 13) + 5
          omega
        · rw [actual_slot]
          simp only [slot, fixedBuffer_size]
          change 2 * physicalRows ≤ 2 * physicalRows
          rfl
        · rw [actual_slot]
          rw [slot_fixed, fixedBuffer_scan]

end ZiskFv.AirsClean.Mem.PhysicalSource.Constructibility
