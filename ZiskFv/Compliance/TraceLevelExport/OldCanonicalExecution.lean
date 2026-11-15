import ZiskFv.Compliance.TraceLevelExport.RecountExecutionData
import ZiskFv.Compliance.TraceLevelExport.OldCanonicalSailTransport
import ZiskFv.Soundness

/-!
# Concrete old execution to source-canonical execution

All index, instruction and channel equalities below are DERIVED from actual
same-witness data reconstruction and the old source-start theorem. None is a
new caller promise on the public root. The final comparison consumes precisely
the old supported root domain, including the empty execution.

This does not construct a seven-field seed over fictitious auxiliary ZiskSteps
or assert that old starts=i on the extended nonfinal-JALR domain.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

private def reindexStep {q : Nat} {trace : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep trace i) : ZiskStep trace j := same ▸ step

private def reindexDecode {q : Nat} {trace : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep trace i) (decoded : RowDecode trace i step) :
    RowDecode trace j (reindexStep same step) := by
  cases same
  exact decoded

private theorem reindexInstruction {q : Nat} {trace : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep trace i) :
    sailInstructionOf j (reindexStep same step) = sailInstructionOf i step := by
  cases same
  rfl

private theorem reindexOutput {q : Nat} {trace : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep trace i) (decoded : RowDecode trace i step) :
    stepChannelOutput j (reindexStep same step) (reindexDecode same step decoded) =
      stepChannelOutput i step decoded := by
  cases same
  rfl

private def reindexRaw {q rawLength : Nat} {trace : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (raw : RawProgramDecode trace i step start addr rawProgram) :
    RawProgramDecode trace j (reindexStep same step) start addr rawProgram := by
  cases same
  exact raw

private theorem reindexProducer {q : Nat} {trace : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep trace i) (decoded : RowDecode trace i step) :
    stepProducerRow j (reindexStep same step) (reindexDecode same step decoded) =
      stepProducerRow i step decoded := by
  cases same
  rfl

private theorem recountProducer {n q : Nat} (trace : AcceptedZiskTrace n)
    (room : q ≤ trace.mainTable.table.length) (enlarge : n ≤ q)
    (i : Fin n) (step : ZiskStep trace i) (decoded : RowDecode trace i step) :
    stepProducerRow (recountIndex enlarge i) (recountStep trace room enlarge i step)
        (recountRowDecode trace room enlarge i step decoded) =
      stepProducerRow i step decoded := by
  cases step <;> rfl

/-- Provider choice does not change the actual channel output. The only
decode-dependent datum is JALR's real producer, which is compared explicitly. -/
theorem channelOutput_eq_of_producer_eq {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (step : ZiskStep trace i) (left right : RowDecode trace i step)
    (producer : stepProducerRow i step left = stepProducerRow i step right) :
    stepChannelOutput i step left = stepChannelOutput i step right := by
  cases step with
  | jalr c =>
      change left.rows.finish.val = right.rows.finish.val at producer
      have finish : left.rows.finish = right.rows.finish := Fin.ext producer
      simp only [stepChannelOutput, finish]
  | _ => rfl

section Recount

variable {n : Nat} {words : Fin n → BitVec 32}
variable (trace : AcceptedZiskTrace n)
variable (L : ∀ i, SuccessfulRowLowering (words i))
variable (room : sourceEnd L ≤ trace.mainTable.table.length)
variable (starts : ∀ i, sourceStart L i = i.val)
variable (steps : ∀ i : Fin n, ZiskStep trace i)

/-- This equality is available ONLY on the old supported placement domain. -/
theorem oldCanonicalIndexEq (i : Fin n) :
    recountIndex (architecturalCount_le_sourceEnd L) i = physicalStart L i :=
  Fin.ext (starts i).symm

/-- Real architectural steps are reindexed; auxiliary rows receive NO step. -/
def oldCanonicalSteps (i : Fin n) :
    ZiskStep (recountWithinMain trace (sourceEnd L) room) (physicalStart L i) :=
  reindexStep (oldCanonicalIndexEq L starts i)
    (recountStep trace room (architecturalCount_le_sourceEnd L) i (steps i))

def oldCanonicalDecoded
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i)) (i : Fin n) :
    RowDecode (recountWithinMain trace (sourceEnd L) room) (physicalStart L i)
      (oldCanonicalSteps trace L room starts steps i) :=
  reindexDecode (oldCanonicalIndexEq L starts i)
    (recountStep trace room (architecturalCount_le_sourceEnd L) i (steps i))
    (recountRowDecode trace room (architecturalCount_le_sourceEnd L) i (steps i) (decoded i))

theorem oldCanonicalInstruction (i : Fin n) :
    sailInstructionOf (physicalStart L i) (oldCanonicalSteps trace L room starts steps i) =
      sailInstructionOf i (steps i) := by
  unfold oldCanonicalSteps
  rw [reindexInstruction]
  exact recountSailInstruction trace room (architecturalCount_le_sourceEnd L) i (steps i)

theorem oldCanonicalOutput
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i)) (i : Fin n) :
    stepChannelOutput (physicalStart L i) (oldCanonicalSteps trace L room starts steps i)
        (oldCanonicalDecoded trace L room starts steps decoded i) =
      stepChannelOutput i (steps i) (decoded i) := by
  unfold oldCanonicalSteps oldCanonicalDecoded
  rw [reindexOutput]
  exact recountChannelOutput trace room (architecturalCount_le_sourceEnd L) i
    (steps i) (decoded i)

/-- The WHOLE Sail state agrees, including every register, memory byte and
platform cell, through the actual final architectural post-state. -/
theorem oldCanonicalStates
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (j : Nat) (hj : j ≤ n) :
    mappedSailStates L (oldCanonicalSteps trace L room starts steps) init j hj =
      chainedSailStates steps init j :=
  mappedSailStates_eq_chainedSailStates L steps
    (oldCanonicalSteps trace L room starts steps) init
    (oldCanonicalInstruction trace L room starts steps) j hj

def oldCanonicalRawDecoded {rawLength : Nat}
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (raw : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram) (i : Fin n) :
    RawProgramDecode (recountWithinMain trace (sourceEnd L) room) (physicalStart L i)
      (oldCanonicalSteps trace L room starts steps i) start addr rawProgram :=
  reindexRaw (oldCanonicalIndexEq L starts i)
    (recountStep trace room (architecturalCount_le_sourceEnd L) i (steps i))
    start addr rawProgram
    (recountRawProgramDecode trace room (architecturalCount_le_sourceEnd L) i
      (steps i) start addr rawProgram (raw i))

theorem oldCanonicalSound
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i))
    (sound : ∀ i : Fin n,
      StepSound trace (chainedSailTrace steps init) i (steps i) (decoded i)) :
    ∀ i : Fin n,
      StepSound (recountWithinMain trace (sourceEnd L) room)
        (mappedSailTrace L (oldCanonicalSteps trace L room starts steps) init)
        (physicalStart L i) (oldCanonicalSteps trace L room starts steps i)
        (oldCanonicalDecoded trace L room starts steps decoded i) :=
  mappedStepSound_of_old L steps (oldCanonicalSteps trace L room starts steps) init
    decoded (oldCanonicalDecoded trace L room starts steps decoded)
    (oldCanonicalInstruction trace L room starts steps)
    (oldCanonicalOutput trace L room starts steps decoded) sound


theorem oldCanonicalProducer
    (decoded : ∀ i : Fin n, RowDecode trace i (steps i)) (i : Fin n) :
    stepProducerRow (physicalStart L i) (oldCanonicalSteps trace L room starts steps i)
        (oldCanonicalDecoded trace L room starts steps decoded i) =
      stepProducerRow i (steps i) (decoded i) := by
  unfold oldCanonicalSteps oldCanonicalDecoded
  rw [reindexProducer]
  exact recountProducer trace room (architecturalCount_le_sourceEnd L) i (steps i) (decoded i)

end Recount

/-- ENTIRE OLD-root-domain comparison, not a list of newly assumed instruction,
state, channel, placement or parsing equalities. All are constructed in the
proof. The original seed remains a premise; no independent memory-induction
elimination or extended nonfinal-JALR root theorem is claimed. -/
theorem old_root_canonical_comparison
    (n rawLength : Nat) (trace : AcceptedZiskTrace n)
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (steps : ∀ i : Fin n, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (core : ∀ i, InputsAgreeCore trace (chainedSailTrace steps init) i (steps i))
    (pcBoot : ∀ (_ : 0 < n), ((mainOfTable trace.program trace.mainTable).pc 0).val =
      (init.regs.get? Register.PC).elim 0 BitVec.toNat)
    (aligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i))))
    (bootSeed : BootSegmentMemorySeed trace (chainedSailTrace steps init) steps)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (avoid : ∀ i, RowOutsideDefectRegion trace i (steps i)) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        ∃ room : sourceEnd lowering ≤ trace.mainTable.table.length,
          ∃ starts : ∀ i, sourceStart lowering i = i.val,
            (∀ i, addr (selected i) = (mainOfTable trace.program trace.mainTable).pc i.val) ∧
            (∀ (j : Nat) (hj : j ≤ n),
              mappedSailStates lowering (oldCanonicalSteps trace lowering room starts steps)
                init j hj = chainedSailStates steps init j) ∧
            (∀ i : Fin n,
              StepSound (recountWithinMain trace (sourceEnd lowering) room)
                (mappedSailTrace lowering (oldCanonicalSteps trace lowering room starts steps) init)
                (physicalStart lowering i) (oldCanonicalSteps trace lowering room starts steps i)
                (oldCanonicalDecoded trace lowering room starts steps
                  (fun j => rowDecode_of_programDecode trace j
                    (programDecode_of_rawProgramDecode trace j (steps j) start addr rawProgram
                      binding (rawDecodes j))) i)) ∧
            Nonempty (∀ i : Fin n,
              RawProgramDecode (recountWithinMain trace (sourceEnd lowering) room)
                (physicalStart lowering i) (oldCanonicalSteps trace lowering room starts steps i)
                start addr rawProgram) ∧
            (∀ present : MutableMemPresent trace.witness,
              Nonempty (BootSegmentReadSoundInputs
                (recountWithinMain trace (sourceEnd lowering) room)
                bootSeed.memInit (sourcePhysicalRowsOf lowering bootSeed.rowsOf) present)) := by
  obtain ⟨selected, lowering, widths, starts, ends⟩ :=
    RawDecodeRowLowering.old_raw_source_widths_and_placement trace steps start addr rawProgram
      binding rawDecodes aligned
  let decoded := fun i => rowDecode_of_programDecode trace i
    (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
      binding (rawDecodes i))
  have room : sourceEnd lowering ≤ trace.mainTable.table.length := by
    by_cases hn : 0 < n
    · let last : Fin n := ⟨n - 1, by omega⟩
      have final : last.val + 1 = n := by dsimp [last]; omega
      rw [ends last final]
      exact Nat.le_of_lt (ExecutionSpanLegacy.producer_has_successor last (steps last)
        (decoded last))
    · have hn0 : n = 0 := by omega
      subst n
      simp [sourceEnd, rowPrefix]
  have actualOldSound : ∀ i : Fin n,
      StepSound trace (chainedSailTrace steps init) i (steps i) (decoded i) :=
    root_soundness n rawLength trace init steps start addr rawProgram binding rawDecodes
      core pcBoot aligned bootSeed regBoot avoid
  refine ⟨selected, lowering, room, starts, (fun i => (widths i).1), ?_, ?_, ?_, ?_⟩
  · exact oldCanonicalStates trace lowering room starts steps init
  · exact oldCanonicalSound trace lowering room starts steps init decoded actualOldSound
  · exact ⟨oldCanonicalRawDecoded trace lowering room starts steps start addr rawProgram rawDecodes⟩
  · intro present
    exact ⟨recountReadSoundInputs trace lowering room bootSeed.memInit bootSeed.rowsOf
      present (bootSeed.readSoundInputs present)⟩

end ZiskFv.Compliance.SerializedExecutionRows
