import ZiskFv.Compliance.TraceLevelExport.CheckedPhysicalSourceCuts
import ZiskFv.Compliance.TraceLevelExport.SourceHeadRegisterPcPlatform

/-!
# Actual original-prefix register invariant at real source heads

This is the register component of an INTERNAL induction hypothesis. Strictly
prior real soundness is transported through exact instruction/output equality,
not assumed as a new Root premise or fabricated for auxiliary physical rows.
The current load read-byte obligation is NOT solved by this projection.
-/

namespace ZiskFv.Compliance.CanonicalSyntaxBoundary.SourceHeadActualRegisterPrefix

open Goldilocks
open CanonicalExecutionRows SerializedExecutionRows RawProgramBinding

variable {n rawLength : Nat} {trace : AcceptedZiskTrace n}
variable {start : Fin rawLength → Fin trace.programLength} {addr : Fin rawLength → FGL}
variable {rawProgram : Fin rawLength → BitVec 32}
variable (checked : CheckedSyntax trace start addr rawProgram)
variable (binding : ProgramRowsBinding trace start addr rawProgram)

private def moveStep {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) : ZiskStep t j := same ▸ step

private def moveDecoded {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) (decoded : RowDecode t i step) :
    RowDecode t j (moveStep same step) := by
  cases same
  exact decoded

private theorem movedProducer {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) (decoded : RowDecode t i step) :
    stepProducerRow j (moveStep same step) (moveDecoded same step decoded) =
      stepProducerRow i step decoded := by
  cases same
  rfl

private theorem movedOutput {q : Nat} {t : AcceptedZiskTrace q} {i j : Fin q}
    (same : i = j) (step : ZiskStep t i) (decoded : RowDecode t i step) :
    stepChannelOutput j (moveStep same step) (moveDecoded same step decoded) =
      stepChannelOutput i step decoded := by
  cases same
  rfl

private theorem recountedProducer {q : Nat} (t : AcceptedZiskTrace n)
    (room : q ≤ t.mainTable.table.length) (enlarge : n ≤ q) (i : Fin n)
    (step : ZiskStep t i) (decoded : RowDecode t i step) :
    stepProducerRow (recountIndex enlarge i) (recountStep t room enlarge i step)
        (recountRowDecode t room enlarge i step decoded) = stepProducerRow i step decoded := by
  cases step <;> rfl

/-- Factory-selected data retain the actual source-selected providers. -/
noncomputable def physicalDecoded (i : Fin checked.count) :
    RowDecode checked.physicalTrace (physicalStart checked.lowering i) (checked.physicalSteps i) :=
  rowDecode_of_programDecode checked.physicalTrace (physicalStart checked.lowering i)
    (programDecode_of_rawProgramDecode checked.physicalTrace (physicalStart checked.lowering i)
      (checked.physicalSteps i) start addr rawProgram (checked.physicalBinding binding)
      (checked.physicalRawDecodes i))

private noncomputable def copiedDecoded (i : Fin checked.count) :
    RowDecode checked.physicalTrace (physicalStart checked.lowering i) (checked.physicalSteps i) :=
  moveDecoded (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))
    (recountRowDecode trace checked.room checked.covered (checked.index i) (checked.steps i)
      (checked.decoded binding i))

private theorem copiedProducer (i : Fin checked.count) :
    stepProducerRow (physicalStart checked.lowering i) (checked.physicalSteps i)
        (copiedDecoded checked binding i) =
      stepProducerRow (checked.index i) (checked.steps i) (checked.decoded binding i) :=
  (movedProducer (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))
    (recountRowDecode trace checked.room checked.covered (checked.index i) (checked.steps i)
      (checked.decoded binding i))).trans
    (recountedProducer trace checked.room checked.covered (checked.index i)
      (checked.steps i) (checked.decoded binding i))

private theorem copiedOutput (i : Fin checked.count) :
    stepChannelOutput (physicalStart checked.lowering i) (checked.physicalSteps i)
        (copiedDecoded checked binding i) =
      stepChannelOutput (checked.index i) (checked.steps i) (checked.decoded binding i) :=
  (movedOutput (checked.physicalIndex_eq_start i)
    (recountStep trace checked.room checked.covered (checked.index i) (checked.steps i))
    (recountRowDecode trace checked.room checked.covered (checked.index i) (checked.steps i)
      (checked.decoded binding i))).trans
    (recountChannelOutput trace checked.room checked.covered (checked.index i)
      (checked.steps i) (checked.decoded binding i))

/-- Source-successful producer equality removes any dependence on different
proof/program-decode factory choices. No output equality is caller supplied. -/
theorem physicalOutput (i : Fin checked.count) :
    stepChannelOutput (physicalStart checked.lowering i) (checked.physicalSteps i)
        (physicalDecoded checked binding i) =
      stepChannelOutput (checked.index i) (checked.steps i) (checked.decoded binding i) := by
  have original := SourceHeadRegisterPcPlatform.producer_stop checked binding i
  have actual := mapped_producer_successor_eq_source_stop rawProgram checked.selected
    checked.lowering checked.physicalTrace start addr (checked.physicalBinding binding)
    checked.physicalSteps checked.physicalRawDecodes checked.physicalAtPc i
  have copied := copiedProducer checked binding i
  have same : stepProducerRow (physicalStart checked.lowering i) (checked.physicalSteps i)
      (physicalDecoded checked binding i) =
      stepProducerRow (physicalStart checked.lowering i) (checked.physicalSteps i)
        (copiedDecoded checked binding i) := by
    change stepProducerRow (physicalStart checked.lowering i) (checked.physicalSteps i)
      (physicalDecoded checked binding i) + 1 =
        (physicalStart checked.lowering i).val + (checked.lowering i).width at actual
    simp only [physicalStart_val] at actual
    omega
  exact (channelOutput_eq_of_producer_eq (physicalStart checked.lowering i)
    (checked.physicalSteps i) _ _ same).trans (copiedOutput checked binding i)

theorem physicalState (init : State) (i : Fin checked.count) :
    mappedSailTrace checked.lowering checked.physicalSteps init (physicalStart checked.lowering i) =
      checked.ownerTrace init (checked.index i) := by
  have state := checked.mappedTrace_recountIndex init (checked.index i)
  rw [checked.physicalIndex_eq_start i] at state
  exact state

/-- Transport one recursively established real step, never a physical auxiliary.
This is an equality transport lemma, not a soundness-discharge premise. -/
theorem physical_sound_of_original (init : State) (i : Fin checked.count)
    (sound : StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
      (checked.decoded binding i)) :
    StepSound checked.physicalTrace (mappedSailTrace checked.lowering checked.physicalSteps init)
      (physicalStart checked.lowering i) (checked.physicalSteps i)
      (physicalDecoded checked binding i) := by
  apply (stepSound_iff (physicalStart checked.lowering i) (checked.physicalSteps i)
    (physicalDecoded checked binding i)).mpr
  unfold sailStepResult
  rw [checked.physicalInstruction, physicalState checked init i, physicalOutput checked binding i]
  exact (stepSound_iff (checked.index i) (checked.steps i) (checked.decoded binding i)).mp sound

/-- Register component at EVERY architectural cut from the actual bounded
induction hypothesis, including the final n+1 physical cut when present. -/
theorem register_prefix_of_previous_sounds (init : State)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (j : Nat) (bound : j ≤ checked.count)
    (sounds : ∀ i : Fin checked.count, i.val < j →
      StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
        (checked.decoded binding i)) :
    ∀ k : Fin 32, k ≠ 0 →
      (checked.states init j bound).regs.get? (reg_of_fin k) =
        some (cast (by rw [register_type_reg_of_fin_equiv])
          (actualPhysicalRegFile checked.physicalTrace (rowPrefix (sourceWidth checked.lowering) j)
            (prefix_mono (sourceWidth checked.lowering) bound) k)) := by
  have copied : ∀ i : Fin checked.count, i.val < j →
      StepSound checked.physicalTrace (mappedSailTrace checked.lowering checked.physicalSteps init)
        (physicalStart checked.lowering i) (checked.physicalSteps i)
        (physicalDecoded checked binding i) :=
    fun i before => physical_sound_of_original checked binding init i (sounds i before)
  have cells := mappedRegAgree_actualPhysical_prefix rawProgram checked.selected checked.lowering
    checked.physicalTrace start addr (checked.physicalBinding binding) checked.physicalSteps
    checked.physicalRawDecodes checked.physicalAtPc init regBoot j bound copied
  rw [checked.mappedStates_eq init j bound] at cells
  exact cells

/-- At a real head the invariant is about the ORIGINAL physical fold. Its cut
is before n, derived from syntax, not an extra register-agreement hypothesis. -/
theorem register_at_head_of_previous_sounds (init : State)
    (regBoot : ∀ k : Fin 32, k ≠ 0 → init.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)))
    (cut : Fin checked.count)
    (sounds : ∀ i : Fin checked.count, i.val < cut.val →
      StepSound trace (checked.ownerTrace init) (checked.index i) (checked.steps i)
        (checked.decoded binding i)) :
    ∀ k : Fin 32, k ≠ 0 →
      (checked.ownerTrace init (checked.index cut)).regs.get? (reg_of_fin k) =
        some (cast (by rw [register_type_reg_of_fin_equiv])
          (actualPhysicalRegFile trace (sourceStart checked.lowering cut)
            (Nat.le_of_lt (checked.headWithin cut)) k)) := by
  rw [CheckedSyntax.state_at_index]
  have cells := register_prefix_of_previous_sounds checked binding init regBoot cut.val
    (Nat.le_of_lt cut.isLt) sounds
  have sameFold := checked.physicalRegFile_prefix_eq
    (sourceStart checked.lowering cut) (Nat.le_of_lt (checked.headWithin cut))
  change actualPhysicalRegFile checked.physicalTrace
    (rowPrefix (sourceWidth checked.lowering) cut.val) _ = _ at sameFold
  rw [sameFold] at cells
  exact cells

end ZiskFv.Compliance.CanonicalSyntaxBoundary.SourceHeadActualRegisterPrefix
