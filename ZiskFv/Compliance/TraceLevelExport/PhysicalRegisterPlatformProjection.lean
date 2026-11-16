import ZiskFv.Compliance.TraceLevelExport.ActualMainMutableProjection
import ZiskFv.Compliance.TraceLevelExport.MappedRegisterReadLanes

/-!
# Computed actual physical platform rows

The finite spine below is the mutable projection of all six actual Main
channels. Its unbounded tail is the caller's original tail. Source widths and
the real producer theorem derive placement at source starts; auxiliary rows
are never assigned architectural steps, and their register reads are retained
in the underlying Main roster.

Only the original narrow-store preserved-byte primitives and objective
execution-row presence implication are consumed by the final lane constructor.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.ZiskCircuit.MemTrace

/-- Read an actual finite physical slot, retaining the original tail outside
that finite spine rather than inventing a default row. -/
noncomputable def actualPhysicalMemoryRowsOf {n : Nat} (trace : AcceptedZiskTrace n)
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) :
    Nat → List (Interaction.MemoryBusEntry FGL) :=
  let slots := actualMainMutablePhysicalSlots trace
  fun p => if hp : p < slots.length then slots[p] else tail p

@[simp] theorem actualPhysicalMemoryRowsOf_at {n : Nat} (trace : AcceptedZiskTrace n)
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) (row : Fin n) :
    actualPhysicalMemoryRowsOf trace tail row.val = physicalMainMutableReplayRowsAt trace row := by
  have inside : row.val < (actualMainMutablePhysicalSlots trace).length := by
    simpa [actualMainMutablePhysicalSlots] using row.isLt
  simp [actualPhysicalMemoryRowsOf, inside, actualMainMutablePhysicalSlots]

/-- The original row-family tail is preserved verbatim. -/
theorem actualPhysicalMemoryRowsOf_tail {n : Nat} (trace : AcceptedZiskTrace n)
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) (p : Nat) (outside : n ≤ p) :
    actualPhysicalMemoryRowsOf trace tail p = tail p := by
  have notInside : ¬p < (actualMainMutablePhysicalSlots trace).length := by
    simpa [actualMainMutablePhysicalSlots] using (Nat.not_lt.mpr outside)
  simp only [actualPhysicalMemoryRowsOf, dif_neg notInside]

/-- Exact ordered finite slots, before flattening or replay. -/
theorem actualPhysicalMemoryRowsOf_ordered_prefix {n : Nat} (trace : AcceptedZiskTrace n)
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) (cut : Nat) (bound : cut ≤ n) :
    (List.range cut).map (actualPhysicalMemoryRowsOf trace tail) =
      (actualMainMutablePhysicalSlots trace).take cut := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take,
      actualMainMutablePhysicalSlots, List.length_map, List.length_finRange]
    omega
  · intro p hp hq
    have before : p < cut := by simpa using hp
    have inside : p < (actualMainMutablePhysicalSlots trace).length := by
      simp only [actualMainMutablePhysicalSlots, List.length_map, List.length_finRange]
      omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_take,
      actualPhysicalMemoryRowsOf, dif_pos inside]

/-- The exact ordered replay prefix of the computed Nat-indexed family. -/
theorem actualPhysicalMemoryRowsOf_prefix {n : Nat} (trace : AcceptedZiskTrace n)
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) (cut : Nat) (bound : cut ≤ n) :
    (List.range cut).flatMap (actualPhysicalMemoryRowsOf trace tail) =
      ((actualMainMutablePhysicalSlots trace).take cut).flatten := by
  rw [List.flatMap_def, actualPhysicalMemoryRowsOf_ordered_prefix trace tail cut bound]

/-- The whole finite execution is exactly the actual physical flattening. -/
theorem actualPhysicalMemoryRowsOf_flatten {n : Nat} (trace : AcceptedZiskTrace n)
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) :
    (List.range n).flatMap (actualPhysicalMemoryRowsOf trace tail) =
      (actualMainMutablePhysicalSlots trace).flatten := by
  rw [actualPhysicalMemoryRowsOf_prefix trace tail n (Nat.le_refl n),
    List.take_of_length_le (by simp [actualMainMutablePhysicalSlots])]

theorem memoryRowsOfStep_eq_nil_of_producer_ne_start
    {n : Nat} {trace : AcceptedZiskTrace n} (i : Fin n) (step : ZiskStep trace i)
    (decoded : RowDecode trace i step) (different : stepProducerRow i step decoded ≠ i.val) :
    memoryRowsOfStep trace i step = [] := by
  cases step <;> simp_all [stepProducerRow, memoryRowsOfStep]

section Source

variable {m rawLength : Nat}
variable (rawProgram : Fin rawLength → BitVec 32) (selected : Fin m → Fin rawLength)
variable (L : ∀ i, SuccessfulRowLowering (rawProgram (selected i)))
variable (trace : AcceptedZiskTrace (sourceEnd L))
variable (start : Fin rawLength → Fin trace.programLength) (addr : Fin rawLength → FGL)
variable (binding : ProgramRowsBinding trace start addr rawProgram)
variable (steps : ∀ i, ZiskStep trace (physicalStart L i))
variable (rawDecodes : ∀ i, RawProgramDecode trace (physicalStart L i) (steps i)
  start addr rawProgram)

local notation "D" => (fun i => rowDecode_of_programDecode trace (physicalStart L i)
  (programDecode_of_rawProgramDecode trace (physicalStart L i) (steps i)
    start addr rawProgram binding (rawDecodes i)))

variable (atPc : ∀ i, (mainOfTable trace.program trace.mainTable).pc
  (physicalStart L i).val = addr (selected i))

include binding rawDecodes atPc

/-- Source-current-start structural rows are derived, not supplied as a
placement certificate. A width-two source start is genuinely mutable-neutral;
its real producer proves that its architectural memory-row list is also empty. -/
theorem actualPhysicalMemoryRowsOf_at_source_start
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) (i : Fin m) :
    actualPhysicalMemoryRowsOf trace tail (physicalStart L i).val =
      memoryRowsOfStep trace (physicalStart L i) (steps i) := by
  rw [actualPhysicalMemoryRowsOf_at]
  rcases (L i).count with one | two
  · change (L i).width = 1 at one
    have same : physicalTerminal L i = physicalStart L i := by
      apply Fin.ext
      simp only [physicalTerminal_val, physicalStart_val, one]
      omega
    have terminal := actual_main_terminal_mutable_projection rawProgram selected L trace
      start addr binding steps rawDecodes atPc i
    change physicalMainMutableReplayRowsAt trace (physicalTerminal L i) = _ at terminal
    simpa only [same] using terminal
  · change (L i).width = 2 at two
    have interior := actual_main_interior_mutable_projection rawProgram selected L trace
      start addr binding atPc i (physicalStart L i) (by
        simp only [physicalStart_val, two]
        omega)
    have producer := physicalTerminal_eq_actual_producer rawProgram selected L trace
      start addr binding steps rawDecodes atPc i
    have different : stepProducerRow (physicalStart L i) (steps i) (D i) ≠
        (physicalStart L i).val := by
      simp only [physicalTerminal_val, physicalStart_val, two] at producer ⊢
      omega
    rw [interior, memoryRowsOfStep_eq_nil_of_producer_ne_start
      (physicalStart L i) (steps i) (D i) different]

/-- Ordered source-cut replay rows, including every empty auxiliary slot in
its underlying physical prefix. -/
theorem actualPhysicalMemoryRowsOf_source_prefix
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) (j : Nat) (bound : j ≤ m) :
    (List.range (rowPrefix (sourceWidth L) j)).flatMap
        (actualPhysicalMemoryRowsOf trace tail) =
      ((List.finRange m).take j).flatMap
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
  rw [actualPhysicalMemoryRowsOf_prefix trace tail _ (prefix_mono (sourceWidth L) bound)]
  exact actual_main_mutable_prefix_flatten rawProgram selected L trace start addr binding
    steps rawDecodes atPc j bound

/-- Whole ordered execution-row equality, not merely a permutation. -/
theorem actualPhysicalMemoryRowsOf_source_flatten
    (tail : Nat → List (Interaction.MemoryBusEntry FGL)) :
    (List.range (sourceEnd L)).flatMap (actualPhysicalMemoryRowsOf trace tail) =
      (List.finRange m).flatMap
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) := by
  rw [actualPhysicalMemoryRowsOf_flatten]
  exact actual_main_mutable_flatten rawProgram selected L trace start addr binding
    steps rawDecodes atPc

/-- Transport the original objective presence implication through the computed
whole ordered flattening. Per-load presence is left to the existing consumer. -/
theorem actualPhysicalMemoryRowsOf_memPresent_of_executionRows_nonempty
    (tail : Nat → List (Interaction.MemoryBusEntry FGL))
    (memPresent_of_executionRows_nonempty :
      (List.finRange m).flatMap
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) ≠ [] →
          MutableMemPresent trace.witness) :
    (List.range (sourceEnd L)).flatMap (actualPhysicalMemoryRowsOf trace tail) ≠ [] →
      MutableMemPresent trace.witness := by
  rw [actualPhysicalMemoryRowsOf_source_flatten rawProgram selected L trace start addr
    binding steps rawDecodes atPc tail]
  exact memPresent_of_executionRows_nonempty

/-- Derive every real source placement. The only store premises are the
original literal preserved-byte primitives at the actual physical replay
prefix; no structural equality, success/layout certificate, or placement
predicate is assumed. -/
theorem actualPhysicalMemoryRowsOf_placement
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (tail : Nat → List (Interaction.MemoryBusEntry FGL))
    (sbPreserved : ∀ i config, steps i = .sb config →
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows memInit
          ((List.range (physicalStart L i).val).flatMap (actualPhysicalMemoryRowsOf trace tail)))
        (busSt trace (physicalStart L i) (Pilot.execRowOf trace (physicalStart L i))).e2 1)
    (shPreserved : ∀ i config, steps i = .sh config →
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows memInit
          ((List.range (physicalStart L i).val).flatMap (actualPhysicalMemoryRowsOf trace tail)))
        (busSt trace (physicalStart L i) (Pilot.execRowOf trace (physicalStart L i))).e2 2)
    (swPreserved : ∀ i config, steps i = .sw config →
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows memInit
          ((List.range (physicalStart L i).val).flatMap (actualPhysicalMemoryRowsOf trace tail)))
        (busSt trace (physicalStart L i) (Pilot.execRowOf trace (physicalStart L i))).e2 4)
    (i : Fin m) :
    MemoryOpPlacement trace (actualPhysicalMemoryRowsOf trace tail) memInit
      (physicalStart L i) (steps i) := by
  have structural := actualPhysicalMemoryRowsOf_at_source_start rawProgram selected L trace
    start addr binding steps rawDecodes atPc tail i
  cases stepEq : steps i <;>
    simp only [stepEq, MemoryOpPlacement, memoryRowsOfStep] at structural ⊢
  all_goals first
  | exact structural
  | exact ⟨structural, sbPreserved i _ stepEq⟩
  | exact ⟨structural, shPreserved i _ stepEq⟩
  | exact ⟨structural, swPreserved i _ stepEq⟩

/-- Fill the existing four-lane consumer with actual computed physical rows
and derived real-source placements. Earlier real StepSounds, inputs, defect
facts and the original register boot assumption are unchanged. No complete
boot seed, Sail state, or architectural step is fabricated at auxiliary rows. -/
theorem actualPhysicalMemoryRowsOf_laneBridge_at_source_start
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (cut : Fin m)
    (sounds : ∀ i : Fin m, i.val < cut.val →
      StepSound trace (mappedSailTrace L steps init) (physicalStart L i) (steps i) (D i))
    (inputs : ∀ i : Fin m, i.val < cut.val →
      InputsAgreeCore trace (mappedSailTrace L steps init) (physicalStart L i) (steps i))
    (outside : ∀ i : Fin m, i.val < cut.val →
      RowOutsideDefectRegion trace (physicalStart L i) (steps i))
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (tail : Nat → List (Interaction.MemoryBusEntry FGL))
    (sbPreserved : ∀ i config, steps i = .sb config →
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows memInit
          ((List.range (physicalStart L i).val).flatMap (actualPhysicalMemoryRowsOf trace tail)))
        (busSt trace (physicalStart L i) (Pilot.execRowOf trace (physicalStart L i))).e2 1)
    (shPreserved : ∀ i config, steps i = .sh config →
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows memInit
          ((List.range (physicalStart L i).val).flatMap (actualPhysicalMemoryRowsOf trace tail)))
        (busSt trace (physicalStart L i) (Pilot.execRowOf trace (physicalStart L i))).e2 2)
    (swPreserved : ∀ i config, steps i = .sw config →
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows memInit
          ((List.range (physicalStart L i).val).flatMap (actualPhysicalMemoryRowsOf trace tail)))
        (busSt trace (physicalStart L i) (Pilot.execRowOf trace (physicalStart L i))).e2 4)
    (memPresent_of_executionRows_nonempty :
      (List.finRange m).flatMap
        (fun i => memoryRowsOfStep trace (physicalStart L i) (steps i)) ≠ [] →
          MutableMemPresent trace.witness) :
    LaneBridge trace (mappedSailTrace L steps init (physicalStart L cut))
      (physicalStart L cut).val := by
  apply laneBridge_at_source_start rawProgram selected L trace start addr binding steps
    rawDecodes atPc init regBoot cut sounds inputs outside memInit
    (actualPhysicalMemoryRowsOf trace tail)
  · exact actualPhysicalMemoryRowsOf_memPresent_of_executionRows_nonempty rawProgram selected L
      trace start addr binding steps rawDecodes atPc tail memPresent_of_executionRows_nonempty
  · intro i _before
    exact actualPhysicalMemoryRowsOf_placement rawProgram selected L trace start addr binding
      steps rawDecodes atPc memInit tail sbPreserved shPreserved swPreserved i

end Source
end ZiskFv.Compliance.SerializedExecutionRows
