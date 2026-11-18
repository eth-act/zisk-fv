import Source458DomainComparison.AcceptedTransport
import ZiskFv.Compliance.AcceptedZiskTrace.MemSegmentRanges
import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence

/-!
# Replay preservation on the actual old-to-new accepted construction

The old selected source is never normalized or replaced by different rows.
The historical initial-memory expression below is exactly the pre-#458
first/continuation selector: zero preload of the actual active rows, optionally
seeded with the previous segment's carried entry (a015aaa7,
Balance/TimelineEvidence.lean:2143-2271). Numeric scalar equations are not used
to obtain the replay consequence. It follows from the corrected production
segment-only theorem and the same accepted constraints/balance/range evidence.
-/

namespace ZiskFv.AirsClean.FullEnsemble.MemDomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean

noncomputable section

@[simp] theorem retargetTable_activeMemReplayRows (table : Table FGL) :
    activeMemReplayRowsOfTable (retargetTable table) = activeMemReplayRowsOfTable table := by
  simp only [activeMemReplayRowsOfTable, retargetTable_table, retargetTable_environment]

@[simp] theorem retargetTable_memReplayRows (table : Table FGL) :
    memReplayRowsOfTable (retargetTable table) = memReplayRowsOfTable table := by
  simp only [memReplayRowsOfTable, retargetTable_table, retargetTable_environment]

@[simp] theorem retargetTable_memTableRowAtOrZero (table : Table FGL) (row : Nat) :
    memTableRowAtOrZero (retargetTable table) row = memTableRowAtOrZero table row := by
  simp only [memTableRowAtOrZero, retargetTable_table, retargetTable_environment]

/-- All primary fields and even the unchanged uninterpreted ghost storage
are projected from the identical original effective rows and shared data. -/
@[simp] theorem retargetTable_memOfTableData (table : Table FGL) :
    memOfTableData (retargetTable table) = memOfTableData table := by
  simp only [memOfTableData, memOfTable, retargetTable_data,
    retargetTable_memTableRowAtOrZero]

@[simp] theorem retargetTable_memSegmentOfTableData (table : Table FGL) :
    memSegmentOfTableData (retargetTable table) = memSegmentOfTableData table := by
  simp only [memSegmentOfTableData, retargetTable_data, retargetTable_fixedAt]

/-- The production segment-only constructor exposes the same literal
first/continuation initial-memory expression as the original constructor. -/
theorem acceptedReplay_initialMemory
    {p : Nat} {program : ZiskInstructionRom.Program p}
    {witness : NewWitness p program}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (bridge : FullWitnessMemReplayBridge witness rows) :
    (acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge bridge).initialMemory =
      if bridge.segment.is_first_segment = 1 then
        ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable bridge.table)
      else previousSegmentInitialMemoryOfRows bridge.segment
        (activeMemReplayRowsOfTable bridge.table) := by
  unfold acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
  unfold acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts
  unfold acceptedMemoryReplayEvidence_of_segmentSelector_memTableGeneratedRowsBridge
  by_cases first : bridge.segment.is_first_segment = 1
  · simp only [dif_pos first, if_pos first,
      acceptedMemoryReplayEvidence_of_firstSegment_memTableGeneratedRowsBridge]
  · simp only [dif_neg first, if_neg first,
      acceptedMemoryReplayEvidence_of_previousSegmentInitialMemory_memTableGeneratedRowsBridge_segmentRangeFacts]

end
end ZiskFv.AirsClean.FullEnsemble.MemDomainComparison

namespace ZiskFv.Compliance.MemDomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.FullEnsemble.MemDomainComparison

variable {n : Nat}

noncomputable section

theorem toCurrent_memReplayRows (trace : Legacy457.AcceptedZiskTrace n)
    (currentGuard : MutableMemPresent (toCurrent trace).witness)
    (oldGuard : Legacy457.MutableMemPresent trace.witness) :
    (toCurrent trace).memReplayRows currentGuard = trace.memReplayRows oldGuard := by
  unfold AcceptedZiskTrace.memReplayRows Legacy457.AcceptedZiskTrace.memReplayRows
  rw [toCurrent_memReplayTable trace currentGuard oldGuard,
    retargetTable_activeMemReplayRows]

/-- Literal old initial-memory projection, with the actual historical selected
source and its existing first-segment selector. This carries no proof input. -/
def historicalInitialMemory (trace : Legacy457.AcceptedZiskTrace n)
    (guard : Legacy457.MutableMemPresent trace.witness) : Std.ExtHashMap Nat (BitVec 8) :=
  let table := trace.memReplayTable guard
  let segment := memSegmentOfTableData table
  if segment.is_first_segment = 1 then
    ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows (activeMemReplayRowsOfTable table)
  else previousSegmentInitialMemoryOfRows segment (activeMemReplayRowsOfTable table)

/-- Use the real corrected accepted bridge. Its generated segment facts,
row/segment ranges, fixed-column facts and nonempty evidence are derived from
the transported old trace, not supplied as new caller certificates. -/
def replayEvidence (trace : Legacy457.AcceptedZiskTrace n)
    (guard : Legacy457.MutableMemPresent trace.witness) :
    ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryReplayEvidence :=
  acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
    ((toCurrent trace).memReplayBridge (eraseLegacyMem_memPresent trace.witness guard))

theorem replayEvidence_rows (trace : Legacy457.AcceptedZiskTrace n)
    (guard : Legacy457.MutableMemPresent trace.witness) :
    (replayEvidence trace guard).rows = trace.memReplayRows guard := by
  unfold replayEvidence
  rw [acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge_rows]
  exact toCurrent_memReplayRows trace _ guard

theorem replayEvidence_initialMemory (trace : Legacy457.AcceptedZiskTrace n)
    (guard : Legacy457.MutableMemPresent trace.witness) :
    (replayEvidence trace guard).initialMemory = historicalInitialMemory trace guard := by
  unfold replayEvidence
  rw [acceptedReplay_initialMemory]
  change (if (memSegmentOfTableData ((toCurrent trace).memReplayTable
      (eraseLegacyMem_memPresent trace.witness guard))).is_first_segment = 1 then
    ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows
      (activeMemReplayRowsOfTable ((toCurrent trace).memReplayTable
        (eraseLegacyMem_memPresent trace.witness guard)))
    else previousSegmentInitialMemoryOfRows
      (memSegmentOfTableData ((toCurrent trace).memReplayTable
        (eraseLegacyMem_memPresent trace.witness guard)))
      (activeMemReplayRowsOfTable ((toCurrent trace).memReplayTable
        (eraseLegacyMem_memPresent trace.witness guard)))) = _
  rw [toCurrent_memReplayTable trace _ guard,
    retargetTable_memSegmentOfTableData, retargetTable_activeMemReplayRows] <;> rfl

/-- Exact prefix-read consequence on the original rows and original seed.
The only argument is the original trace's objective mutable-Mem presence
proof. In particular no prefixReadSound or replacement range/order promise
is supplied, and no scalar permutation arithmetic is reconstructed. -/
theorem historical_prefixReadSound (trace : Legacy457.AcceptedZiskTrace n)
    (guard : Legacy457.MutableMemPresent trace.witness) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      (historicalInitialMemory trace guard) (trace.memReplayRows guard) := by
  have sound := (replayEvidence trace guard).prefixReadSound
  simpa only [replayEvidence_rows, replayEvidence_initialMemory] using sound

end
end ZiskFv.Compliance.MemDomainComparison
