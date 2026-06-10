import ZiskFv.EquivCore.Promises.Load

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.ZiskCircuit.MemTrace

private def witnessEntry : MemoryBusEntry FGL where
  multiplicity := -1
  as := 2
  ptr := 0
  value_0 := 0
  value_1 := 0
  timestamp := 0

private def witnessMem : Std.ExtHashMap ℕ (BitVec 8) :=
  Std.ExtHashMap.insert
    (Std.ExtHashMap.insert
      (Std.ExtHashMap.insert
        (Std.ExtHashMap.insert
          (Std.ExtHashMap.insert
            (Std.ExtHashMap.insert
              (Std.ExtHashMap.insert
                (Std.ExtHashMap.insert
                  (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).mem
                  witnessEntry.ptr.toNat (byteAt witnessEntry 0))
                (witnessEntry.ptr.toNat + 1) (byteAt witnessEntry 1))
              (witnessEntry.ptr.toNat + 2) (byteAt witnessEntry 2))
            (witnessEntry.ptr.toNat + 3) (byteAt witnessEntry 3))
          (witnessEntry.ptr.toNat + 4) (byteAt witnessEntry 4))
        (witnessEntry.ptr.toNat + 5) (byteAt witnessEntry 5))
      (witnessEntry.ptr.toNat + 6) (byteAt witnessEntry 6))
    (witnessEntry.ptr.toNat + 7) (byteAt witnessEntry 7)

private def witnessState : PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    mem := witnessMem }

private theorem witnessPrefixReadSound :
    MemoryBusRowsPrefixReadSound witnessMem [witnessEntry] := by
  intro priorRows row laterRows h_rows _h_as _h_mult
  cases priorRows with
  | nil =>
      simp at h_rows
      rcases h_rows with ⟨h_row, h_laterRows⟩
      subst row
      subst laterRows
      unfold ReadEventReplayAgreement replayMemoryAfterBusRows witnessMem witnessEntry
      native_decide
  | cons _head _tail =>
      simp at h_rows

private theorem witnessInitialAgreement :
    ReplayMemoryAgreement witnessState witnessMem := by
  intro _addr
  rfl

private def accepted_replay_witness : AcceptedMemoryReplayEvidence :=
  { rows := [witnessEntry]
    initialMemory := witnessMem
    prefixReadSound := witnessPrefixReadSound }

private def memory_timeline_witness :
    MemoryTimelineEvidence witnessState witnessEntry :=
  { initialState := witnessState
    acceptedReplay := accepted_replay_witness
    priorRows := []
    laterRows := []
    traceSplit := rfl
    selectedRead := by
      simp [memoryBusTraceEventOfRow, witnessEntry]
    initialAgreement := witnessInitialAgreement
    stateAtPrefix := rfl }

private theorem load_byte_agreement_of_timeline_witness :
    LoadByteAgreement witnessState witnessEntry :=
  loadByteAgreement_of_memory_timeline_evidence
    witnessState witnessEntry memory_timeline_witness

#print axioms load_byte_agreement_of_timeline_witness

end ZiskFv.TrustConsistency
