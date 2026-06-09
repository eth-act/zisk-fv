import ZiskFv.EquivCore.Promises.Load

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)

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

private theorem load_byte_agreement_witness :
    LoadByteAgreement witnessState witnessEntry := by
  unfold LoadByteAgreement witnessState witnessMem witnessEntry
  native_decide

#print axioms load_byte_agreement_witness

end ZiskFv.TrustConsistency
