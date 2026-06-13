import ZiskFv.ZiskCircuit.MemTimeline.Construction

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf)
open ZiskFv.EquivCore.Promises
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.ZiskCircuit.MemTimeline

private def selectedReadEntry : MemoryBusEntry FGL where
  multiplicity := -1
  as := 2
  ptr := 0
  value_0 := 0
  value_1 := 0
  timestamp := 1

private def initialReplayMemory : Std.ExtHashMap ℕ (BitVec 8) :=
  Std.ExtHashMap.insert
    (Std.ExtHashMap.insert
      (Std.ExtHashMap.insert
        (Std.ExtHashMap.insert
          (Std.ExtHashMap.insert
            (Std.ExtHashMap.insert
              (Std.ExtHashMap.insert
                (Std.ExtHashMap.insert
                  (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).mem
                  selectedReadEntry.ptr.toNat (byteAt selectedReadEntry 0))
                (selectedReadEntry.ptr.toNat + 1) (byteAt selectedReadEntry 1))
              (selectedReadEntry.ptr.toNat + 2) (byteAt selectedReadEntry 2))
            (selectedReadEntry.ptr.toNat + 3) (byteAt selectedReadEntry 3))
          (selectedReadEntry.ptr.toNat + 4) (byteAt selectedReadEntry 4))
        (selectedReadEntry.ptr.toNat + 5) (byteAt selectedReadEntry 5))
      (selectedReadEntry.ptr.toNat + 6) (byteAt selectedReadEntry 6))
    (selectedReadEntry.ptr.toNat + 7) (byteAt selectedReadEntry 7)

private def witnessState : PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    mem := initialReplayMemory }

private theorem initialAgreement :
    ReplayMemoryAgreement witnessState initialReplayMemory := by
  intro addr
  rfl

private theorem selectedReadReplayAgreement :
    ReadEventReplayAgreement initialReplayMemory (eventOfEntry selectedReadEntry) := by
  unfold ReadEventReplayAgreement eventOfEntry initialReplayMemory selectedReadEntry
  simp [Std.ExtHashMap.getElem_insert, Std.ExtHashMap.getElem_insert_self,
    MemEvent.byteAt, byteAt, byteOf]

private theorem prefixReadSound :
    MemoryBusRowsPrefixReadSound initialReplayMemory [selectedReadEntry] := by
  intro priorRows row laterRows h_rows _h_as _h_mult
  cases priorRows with
  | nil =>
      simp at h_rows
      rcases h_rows with ⟨h_row, _h_laterRows⟩
      subst row
      exact selectedReadReplayAgreement
  | cons _priorHead priorTail =>
      cases priorTail <;> simp at h_rows

private def generatedReplayFacts :
    ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts witnessState [selectedReadEntry] :=
  { initialMemory := initialReplayMemory
    prefixReadSound := prefixReadSound
    initialAgreement := initialAgreement }

private theorem witnessPrefixAlignment :
    MemoryPrefixStateAlignment witnessState witnessState [] := by
  rfl

private def constructedTimelineWitness :
    MemoryTimelineEvidence witnessState selectedReadEntry :=
  memoryTimelineEvidence_of_generated_replay_facts
    generatedReplayFacts [] [] rfl
    (by simp [memoryBusTraceEventOfRow, selectedReadEntry])
    witnessPrefixAlignment

private theorem load_byte_agreement_of_constructed_timeline_witness :
    LoadByteAgreement witnessState selectedReadEntry :=
  loadByteAgreement_of_memory_timeline_evidence
    witnessState selectedReadEntry constructedTimelineWitness

#print axioms load_byte_agreement_of_constructed_timeline_witness

end ZiskFv.TrustConsistency
