import ZiskFv.Compliance.TraceLevelExport.CanonicalSyntaxBoundary
import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterPlatformProjection
import ZiskFv.Compliance.TraceLevelExport.RecountExecutionData

/-!
# Checked source cuts in the original physical prefix

The caller's Accepted trace and initial state do not change. The local
source-end view retains exactly the same witness, program, and Main table;
it is used only to instantiate existing physical-fold theorems. Every source
head remains in the ORIGINAL prefix, whose register and ordered mutable folds
are proved identical. An old final-width-two endpoint may be n+1: the terminal
physical row is retained, never masked to n or assigned a fictitious RV step.
-/

namespace ZiskFv.Compliance.CanonicalSyntaxBoundary.CheckedSyntax

open Goldilocks
open CanonicalExecutionRows CanonicalSourceParser SerializedExecutionRows RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

variable {n rawLength : Nat} {trace : AcceptedZiskTrace n}
variable {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
variable {rawProgram : Fin rawLength → BitVec 32}
variable (checked : CheckedSyntax trace start addr rawProgram)

/-- The actual source-head map is injective, not a supplied owner relation. -/
theorem index_injective : Function.Injective checked.index := by
  intro i j same
  have owners := congrArg checked.owner same
  simpa only [checked.owner_at_index] using owners

theorem count_le_physical : checked.count ≤ n := by
  have bound := Fintype.card_le_of_injective checked.index checked.index_injective
  simpa only [Fintype.card_fin] using bound

/-- Preserve the genuinely empty domain without choosing a dummy instruction. -/
theorem count_zero_iff_physical_zero : checked.count = 0 ↔ n = 0 := by
  constructor
  · intro empty
    by_contra nonempty
    have positive : 0 < n := by omega
    have impossible := (checked.owner ⟨0, positive⟩).isLt
    omega
  · intro empty
    have bound := checked.count_le_physical
    omega

/-- Coverage and actual source widths permit at most one terminal row beyond
n. In particular no equal-endpoint condition silently excludes old final2. -/
theorem endpoint_le_succ : sourceEnd checked.lowering ≤ n + 1 := by
  by_contra beyond
  have inside : n + 1 < sourceEnd checked.lowering := by omega
  obtain ⟨i, interval, _⟩ := source_prefix_exact checked.lowering (n + 1) inside
  have head := checked.headWithin i
  have width := (checked.lowering i).count
  change (checked.lowering i).width = 1 ∨ (checked.lowering i).width = 2 at width
  omega

theorem endpoint_eq_or_succ : sourceEnd checked.lowering = n ∨
    sourceEnd checked.lowering = n + 1 := by
  have lower := checked.covered
  have upper := checked.endpoint_le_succ
  omega

@[simp] theorem index_zero_val (positive : 0 < checked.count) :
    (checked.index ⟨0, positive⟩).val = 0 := by
  exact prefix_zero (sourceWidth checked.lowering)

/-- This is a LOCAL same-witness view of the computed source endpoint, not a
replacement Accepted input, root endpoint parameter, or stronger validator. -/
noncomputable def physicalTrace : AcceptedZiskTrace (sourceEnd checked.lowering) :=
  recountWithinMain trace (sourceEnd checked.lowering) checked.room

@[simp] theorem physicalIndex_eq_start (i : Fin checked.count) :
    recountIndex checked.covered (checked.index i) = physicalStart checked.lowering i :=
  Fin.ext rfl

private def reindexStep {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) : ZiskStep t j := same ▸ step

private def reindexRaw {q length : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i)
    (positions : Fin length → Fin t.programLength) (addresses : Fin length → FGL)
    (words : Fin length → BitVec 32)
    (raw : RawProgramDecode t i step positions addresses words) :
    RawProgramDecode t j (reindexStep same step) positions addresses words := by
  cases same
  exact raw

private theorem instruction_reindex {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) :
    sailInstructionOf j (reindexStep same step) = sailInstructionOf i step := by
  cases same
  rfl

/-- Only the real architectural steps are copied; auxiliary rows have no step. -/
noncomputable def physicalSteps (i : Fin checked.count) :
    ZiskStep checked.physicalTrace (physicalStart checked.lowering i) :=
  reindexStep (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))

noncomputable def physicalRawDecodes (i : Fin checked.count) :
    RawProgramDecode checked.physicalTrace (physicalStart checked.lowering i)
      (checked.physicalSteps i) start addr rawProgram :=
  reindexRaw (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))
    start addr rawProgram
    (recountRawProgramDecode trace checked.room checked.covered (checked.index i)
      (checked.steps i) start addr rawProgram (checked.rawDecodes i))

noncomputable def physicalBinding (binding : ProgramRowsBinding trace start addr rawProgram) :
    ProgramRowsBinding checked.physicalTrace start addr rawProgram := binding

theorem physicalAtPc (i : Fin checked.count) :
    (mainOfTable checked.physicalTrace.program checked.physicalTrace.mainTable).pc
      (physicalStart checked.lowering i).val = addr (checked.selected i) :=
  checked.atPc i

/-- Exact instruction erasure, with all original decoded operands preserved. -/
theorem physicalInstruction (i : Fin checked.count) :
    sailInstructionOf (physicalStart checked.lowering i) (checked.physicalSteps i) =
      sailInstructionOf (checked.index i) (checked.steps i) :=
  (instruction_reindex (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))).trans
      (recountSailInstruction trace checked.room checked.covered (checked.index i) (checked.steps i))

/-- Architectural states agree at EVERY bounded cut, including the final
state and the empty execution. No prior StepSound or state oracle is used. -/
theorem mappedStates_eq (init : State) (j : Nat) (h : j ≤ checked.count) :
    mappedSailStates checked.lowering checked.physicalSteps init j h =
      checked.states init j h := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [mappedSailStates, CheckedSyntax.states]
    rw [checked.physicalInstruction, ih (by omega)]

/-- Pull back only the ORIGINAL physical prefix. Ownership is the actual
source-prefix unique owner, never an additional caller hypothesis. -/
theorem mappedTrace_recountIndex (init : State) (r : Fin n) :
    mappedSailTrace checked.lowering checked.physicalSteps init (recountIndex checked.covered r) =
      checked.ownerTrace init r := by
  change mappedSailStates checked.lowering checked.physicalSteps init
      (checked.owner r).val _ = checked.states init (checked.owner r).val _
  exact checked.mappedStates_eq init (checked.owner r).val (Nat.le_of_lt (checked.owner r).isLt)

/-- The original register prefix keeps EVERY physical C request. This is
pure physical-fold identity, not a premise equating Sail and physical state. -/
theorem physicalRegFile_prefix_eq (cut : Nat) (bound : cut ≤ n) :
    actualPhysicalRegFile checked.physicalTrace cut (bound.trans checked.covered) =
      actualPhysicalRegFile trace cut bound := by
  induction cut with
  | zero => simp only [actualPhysicalRegFile_zero]
  | succ cut ih =>
    have before : cut < n := by omega
    let row : Fin n := ⟨cut, before⟩
    change actualPhysicalRegFile checked.physicalTrace (row.val + 1) _ =
      actualPhysicalRegFile trace (row.val + 1) _
    have copiedSucc := actualPhysicalRegFile_succ checked.physicalTrace
      (recountIndex checked.covered row)
    change actualPhysicalRegFile checked.physicalTrace (row.val + 1) _ = _ at copiedSucc
    dsimp only [recountIndex] at copiedSucc
    rw [copiedSucc, actualPhysicalRegFile_succ trace row]
    rw [ih (Nat.le_of_lt before)]
    unfold actualCRegisterAction actualCRegisterWriteAt mainCMemInteractionAt mainRowWithRomAt
    dsimp only [physicalTrace, recountWithinMain, AcceptedZiskTrace.mainTable]

/-- Exact ORDERED mutable slots before every original physical cut, including
empty auxiliary slots and duplicate interactions. Nothing is quotiented away. -/
theorem physicalMutable_prefix_eq (cut : Nat) (bound : cut ≤ n) :
    (actualMainMutablePhysicalSlots checked.physicalTrace).take cut =
      (actualMainMutablePhysicalSlots trace).take cut := by
  apply List.ext_getElem
  · simp only [List.length_take, actualMainMutablePhysicalSlots, List.length_map,
      List.length_finRange]
    have enlarged := checked.covered
    omega
  · intro p hp hq
    simp only [List.getElem_take, actualMainMutablePhysicalSlots, List.getElem_map,
      List.getElem_finRange]
    unfold physicalMainMutableReplayRowsAt mainMutableReplayRowsAt
    dsimp only [physicalTrace, recountWithinMain, AcceptedZiskTrace.mainTable,
      mainTypedMemRoster]
    rfl

private theorem memoryRows_reindex {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) :
    memoryRowsOfStep t j (reindexStep same step) = memoryRowsOfStep t i step := by
  cases same
  rfl

/-- Real architectural memory rows are unchanged by the local source-end view. -/
theorem physicalMemoryRows (i : Fin checked.count) :
    memoryRowsOfStep checked.physicalTrace (physicalStart checked.lowering i)
        (checked.physicalSteps i) =
      memoryRowsOfStep trace (checked.index i) (checked.steps i) := by
  have reindexed := memoryRows_reindex (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))
  apply reindexed.trans
  cases checked.steps i <;> rfl

/-- A source-terminal slot outside the old prefix is retained explicitly.
It is mutable-neutral by actual source/producer facts, not by deleting that
physical row or assigning it an auxiliary instruction. -/
theorem physicalMutable_outside_original
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (row : Fin (sourceEnd checked.lowering)) (outside : n ≤ row.val) :
    physicalMainMutableReplayRowsAt checked.physicalTrace row = [] := by
  let i := physicalOwner checked.lowering row
  have interval := physicalOwner_spec checked.lowering row
  have head := checked.headWithin i
  have count := (checked.lowering i).count
  change (checked.lowering i).width = 1 ∨ (checked.lowering i).width = 2 at count
  have terminalIndex : row = physicalTerminal checked.lowering i := by
    apply Fin.ext
    simp only [physicalTerminal_val]
    change sourceStart checked.lowering i ≤ row.val ∧
      row.val < sourceStart checked.lowering i + (checked.lowering i).width at interval
    omega
  let decoded := rowDecode_of_programDecode checked.physicalTrace
    (physicalStart checked.lowering i)
    (programDecode_of_rawProgramDecode checked.physicalTrace (physicalStart checked.lowering i)
      (checked.physicalSteps i) start addr rawProgram (checked.physicalBinding binding)
      (checked.physicalRawDecodes i))
  have producer := physicalTerminal_eq_actual_producer rawProgram checked.selected checked.lowering
    checked.physicalTrace start addr (checked.physicalBinding binding) checked.physicalSteps
    checked.physicalRawDecodes checked.physicalAtPc i
  have rowVal := congrArg Fin.val terminalIndex
  have different : stepProducerRow (physicalStart checked.lowering i)
      (checked.physicalSteps i) decoded ≠ (physicalStart checked.lowering i).val := by
    change (physicalTerminal checked.lowering i).val =
      stepProducerRow (physicalStart checked.lowering i) (checked.physicalSteps i) decoded at producer
    simp only [physicalStart_val] at *
    omega
  have emptyRows := memoryRowsOfStep_eq_nil_of_producer_ne_start
    (physicalStart checked.lowering i) (checked.physicalSteps i) decoded different
  have terminal := actual_main_terminal_mutable_projection rawProgram checked.selected
    checked.lowering checked.physicalTrace start addr (checked.physicalBinding binding)
    checked.physicalSteps checked.physicalRawDecodes checked.physicalAtPc i
  change physicalMainMutableReplayRowsAt checked.physicalTrace
    (physicalTerminal checked.lowering i) = _ at terminal
  rw [terminalIndex]
  exact terminal.trans emptyRows

/-- Whole mutable execution rows on the ORIGINAL trace. The possible old
final2 terminal outside n is proved empty only in the mutable projection;
its actual register write and RAW requests are not removed. -/
theorem originalMutable_flatten
    (binding : ProgramRowsBinding trace start addr rawProgram) :
    (actualMainMutablePhysicalSlots trace).flatten =
      (List.finRange checked.count).flatMap
        (fun i => memoryRowsOfStep trace (checked.index i) (checked.steps i)) := by
  let slots := actualMainMutablePhysicalSlots checked.physicalTrace
  have length : slots.length = sourceEnd checked.lowering := by
    simp only [slots, actualMainMutablePhysicalSlots, List.length_map, List.length_finRange]
  have after : ∀ d : Nat, n + d ≤ sourceEnd checked.lowering →
      (slots.take (n + d)).flatten = (slots.take n).flatten := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.add_zero]
    | succ d ih =>
      intro bounded
      have before : n + d < sourceEnd checked.lowering := by omega
      have inside : n + d < slots.length := by omega
      have atSlot : slots[n + d]'inside = [] := by
        simpa only [slots, actualMainMutablePhysicalSlots, List.getElem_map,
          List.getElem_finRange] using
          checked.physicalMutable_outside_original binding ⟨n + d, before⟩
            (by change n ≤ n + d; omega)
      have atOption : slots[n + d]? = some [] := by
        rw [List.getElem?_eq_getElem inside, atSlot]
      simp only [Nat.add_succ, List.take_add_one, atOption, Option.toList_some,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact ih (by omega)
  have whole := after (sourceEnd checked.lowering - n) (by have h := checked.covered; omega)
  have endpoint : n + (sourceEnd checked.lowering - n) = sourceEnd checked.lowering := by
    have h := checked.covered
    omega
  rw [endpoint, List.take_of_length_le length.le] at whole
  calc
    (actualMainMutablePhysicalSlots trace).flatten = (slots.take n).flatten := by
      have originalLength : (actualMainMutablePhysicalSlots trace).length = n := by
        simp only [actualMainMutablePhysicalSlots, List.length_map, List.length_finRange]
      simpa only [List.take_of_length_le originalLength.le] using
        congrArg List.flatten (checked.physicalMutable_prefix_eq n (Nat.le_refl n)).symm
    _ = slots.flatten := whole.symm
    _ = (List.finRange checked.count).flatMap
        (fun i => memoryRowsOfStep trace (checked.index i) (checked.steps i)) := by
      rw [actual_main_mutable_flatten rawProgram checked.selected checked.lowering
        checked.physicalTrace start addr (checked.physicalBinding binding) checked.physicalSteps
        checked.physicalRawDecodes checked.physicalAtPc]
      simp_rw [checked.physicalMemoryRows]

/-- The exact source-head mutable prefix, still phrased on the caller's
ORIGINAL trace, not just a claimed permutation of selected memory events. -/
theorem originalMutable_source_prefix
    (binding : ProgramRowsBinding trace start addr rawProgram) (i : Fin checked.count) :
    ((actualMainMutablePhysicalSlots trace).take (sourceStart checked.lowering i)).flatten =
      ((List.finRange checked.count).take i.val).flatMap
        (fun j => memoryRowsOfStep trace (checked.index j) (checked.steps j)) := by
  rw [← checked.physicalMutable_prefix_eq _ (Nat.le_of_lt (checked.headWithin i))]
  change ((actualMainMutablePhysicalSlots checked.physicalTrace).take
    (rowPrefix (sourceWidth checked.lowering) i.val)).flatten = _
  rw [actual_main_mutable_prefix_flatten rawProgram checked.selected checked.lowering
    checked.physicalTrace start addr (checked.physicalBinding binding) checked.physicalSteps
    checked.physicalRawDecodes checked.physicalAtPc i.val (Nat.le_of_lt i.isLt)]
  simp_rw [checked.physicalMemoryRows]

end ZiskFv.Compliance.CanonicalSyntaxBoundary.CheckedSyntax
