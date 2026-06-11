import ZiskFv.EquivCore.Promises.Load

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.ZiskCircuit.MemTrace

private def priorWriteEntry : MemoryBusEntry FGL where
  multiplicity := 1
  as := 2
  ptr := 0
  value_0 := 1
  value_1 := 0
  timestamp := 5

private def selectedReadEntry : MemoryBusEntry FGL where
  multiplicity := -1
  as := 2
  ptr := 8
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

private theorem witnessPrefixReadSound :
    MemoryBusRowsPrefixReadSound initialReplayMemory [priorWriteEntry, selectedReadEntry] := by
  intro priorRows row laterRows h_rows _h_as h_mult
  cases priorRows with
  | nil =>
      simp at h_rows
      rcases h_rows with ⟨h_row, h_laterRows⟩
      subst row
      have h_not_read : ¬priorWriteEntry.multiplicity = (-1 : FGL) := by
        native_decide
      exact False.elim (h_not_read h_mult)
  | cons priorHead priorTail =>
      cases priorTail with
      | nil =>
          simp at h_rows
          rcases h_rows with ⟨h_priorHead, h_row, h_laterRows⟩
          subst priorHead
          subst row
          subst laterRows
          unfold ReadEventReplayAgreement replayMemoryAfterBusRows
            replayMemoryAfterBusRow replayStoreEvent replayStoreByte
            initialReplayMemory priorWriteEntry selectedReadEntry
          native_decide
      | cons _priorNext _priorRest =>
          simp at h_rows

private theorem witnessStateBytesAtPrefix :
    ReplayMemoryAgreementOnBytes witnessState
      (replayMemoryAfterBusRows initialReplayMemory [priorWriteEntry])
      selectedReadEntry.ptr.toNat := by
  intro i hi
  interval_cases i
  all_goals
    unfold replayMemoryAfterBusRows replayMemoryAfterBusRow replayStoreEvent replayStoreByte
      initialReplayMemory witnessState priorWriteEntry selectedReadEntry
    native_decide

private theorem oldWholeStateBoundaryWouldReplayLaterWrite :
    witnessState.mem[priorWriteEntry.ptr.toNat]? ≠
      (stateAfterMemoryBusRows witnessState [priorWriteEntry]).mem[priorWriteEntry.ptr.toNat]? := by
  native_decide

private def accepted_replay_witness : AcceptedMemoryReplayEvidence :=
  { rows := [priorWriteEntry, selectedReadEntry]
    initialMemory := initialReplayMemory
    prefixReadSound := witnessPrefixReadSound }

private def memory_timeline_witness :
    MemoryTimelineEvidence witnessState selectedReadEntry :=
  { acceptedReplay := accepted_replay_witness
    priorRows := [priorWriteEntry]
    laterRows := []
    traceSplit := rfl
    selectedRead := by
      simp [memoryBusTraceEventOfRow, selectedReadEntry]
    stateBytesAtPrefix := witnessStateBytesAtPrefix }

private theorem load_byte_agreement_of_timeline_witness :
    LoadByteAgreement witnessState selectedReadEntry :=
  loadByteAgreement_of_memory_timeline_evidence
    witnessState selectedReadEntry memory_timeline_witness

#print axioms load_byte_agreement_of_timeline_witness

end ZiskFv.TrustConsistency
