import ZiskFv.AirsClean.BinaryTableRequests

/-!
Full canonical source completion, independently of acceptance transport.
The source dimensions are the production Binary PIL 335–336 and Extension
PIL 204–205 dimensions used by `sourceFixedColumns`; the physical locations
are `Extraction.PackedVirtualTables.source125` and `source124`, respectively.
All rows, including zero-multiplicity rows, remain in the ordered streams.
The remaining global obligation is the interaction-list length bound, not
per-message cancellation. No old/new accepted-domain implication is asserted.
-/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat Extraction.PackedVirtualTables
open ZiskFv.AirsClean
open PackedVirtualTableSources
open ZiskFv.Channels.BinaryTable (BinaryTableChannel)
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableChannel)

 theorem binary_full_length (raw : Witness FGL) (data : ProverData FGL) :
    (binaryProviderTable raw data).table.length = BinaryTable.tableSize := by
  rw [binaryProviderTable_materialized, List.length_ofFn]

 theorem extension_full_length (raw : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable raw data).table.length = BinaryExtensionTable.tableSize := by
  rw [extensionProviderTable_materialized, List.length_ofFn]

 theorem binary_full_get (raw : Witness FGL) (data : ProverData FGL)
    (i : Fin BinaryTable.tableSize) :
    (binaryProviderTable raw data).table[i.val]'(by
      rw [binary_full_length]; exact i.isLt) =
      (toElements (binaryRow raw i)).toArray := by
  simp [binaryProviderTable_materialized]

 theorem extension_full_get (raw : Witness FGL) (data : ProverData FGL)
    (i : Fin BinaryExtensionTable.tableSize) :
    (extensionProviderTable raw data).table[i.val]'(by
      rw [extension_full_length]; exact i.isLt) =
      (toElements (extensionRow raw i)).toArray := by
  simp [extensionProviderTable_materialized]

/-- The actual component has no adjacent-row predicates beyond its row-local
lookup. These are its real transition fields, not replacement validators. -/
theorem binary_full_checks (raw : Witness FGL) (data : ProverData FGL) :
    (binaryProviderTable raw data).Constraints ∧
    (binaryProviderTable raw data).TransitionConstraints ∧
    (binaryProviderTable raw data).CyclicSuccessorTransitionConstraints :=
  ⟨binaryProviderTable_constraints raw data, (fun _ => True.intro),
    (fun _ => True.intro)⟩

theorem extension_full_checks (raw : Witness FGL) (data : ProverData FGL) :
    (extensionProviderTable raw data).Constraints ∧
    (extensionProviderTable raw data).TransitionConstraints ∧
    (extensionProviderTable raw data).CyclicSuccessorTransitionConstraints :=
  ⟨extensionProviderTable_constraints raw data, (fun _ => True.intro),
    (fun _ => True.intro)⟩

/-- Arbitrary raw values, including zero, survive source reification unchanged. -/
theorem binary_raw_multiplicity (raw : Witness FGL) (i : Fin BinaryTable.tableSize) :
    (binaryRow raw i).multiplicity = raw (source125.location (binaryIndex i)) := rfl

theorem extension_raw_multiplicity (raw : Witness FGL)
    (i : Fin BinaryExtensionTable.tableSize) :
    (extensionRow raw i).multiplicity = raw (source124.location (extensionIndex i)) := rfl

theorem requests_preserve_unrelated (base : Witness FGL)
    (bs : List (Fin BinaryTable.tableSize))
    (es : List (Fin BinaryExtensionTable.tableSize)) (location : Location)
    (h : sourceAt location = none) :
    physicalOfRequests base bs es location = base location := by
  simp [physicalOfRequests, physicalOfLogical, h]

/-- Both full tables use the same physical witness and exactly the original
ordered count-based producer streams, with no positive-count filter. -/
theorem requests_actual_streams (base : Witness FGL) (data : ProverData FGL)
    (bs : List (Fin BinaryTable.tableSize))
    (es : List (Fin BinaryExtensionTable.tableSize)) :
    (binaryProviderTable (physicalOfRequests base bs es) data).interactionsWith
        BinaryTableChannel.toRaw = countedSourceInteractions BinaryTableChannel
          (fun i : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex i.val) bs ∧
    (extensionProviderTable (physicalOfRequests base bs es) data).interactionsWith
        BinaryExtensionTableChannel.toRaw = countedSourceInteractions BinaryExtensionTableChannel
          (fun i : Fin BinaryExtensionTable.tableSize => BinaryExtensionTable.rowOfIndex i.val) es := by
  constructor
  · rw [binaryProviderTable_interactionsWith, binaryInteractions_physicalOfRequests]
  · rw [extensionProviderTable_interactionsWith, extensionInteractions_physicalOfRequests]

section Requests
variable {Message : TypeMap} [ProvableType Message]

theorem requests_balance_sum {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n)) (message : Array FGL) :
    balanceOf (countedSourceInteractions channel row requests ++
      consumedSourceRequests channel row requests) message = 0 := by
  rw [balanceOf_append, countedSourceInteractions_balanceOf,
    consumedSourceRequests_balanceOf, add_neg_cancel]

/-- An unused source index is still present, with exactly zero multiplicity. -/
theorem requests_binary_zero (base : Witness FGL)
    (bs : List (Fin BinaryTable.tableSize))
    (es : List (Fin BinaryExtensionTable.tableSize))
    (i : Fin BinaryTable.tableSize) (unused : i ∉ bs) :
    (binaryRow (physicalOfRequests base bs es) i).multiplicity = 0 := by
  rw [binaryRow_requests_multiplicity, List.count_eq_zero.mpr unused]
  rfl

theorem requests_extension_zero (base : Witness FGL)
    (bs : List (Fin BinaryTable.tableSize))
    (es : List (Fin BinaryExtensionTable.tableSize))
    (i : Fin BinaryExtensionTable.tableSize) (unused : i ∉ es) :
    (extensionRow (physicalOfRequests base bs es) i).multiplicity = 0 := by
  rw [extensionRow_requests_multiplicity, List.count_eq_zero.mpr unused]
  rfl

/-- Exact formula: fixed rows count even if their multiplicity is zero. -/
theorem requests_length {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n)) :
    (countedSourceInteractions channel row requests ++
      consumedSourceRequests channel row requests).length = n + requests.length := by
  simp [countedSourceInteractions, consumedSourceRequests]

 theorem requests_balanced {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n))
    (length_bound : n + requests.length < ringChar FGL) :
    BalancedInteractions (countedSourceInteractions channel row requests ++
      consumedSourceRequests channel row requests) :=
  countedSourceRequests_balanced channel row requests length_bound
end Requests

/-- Static membership supplies source indices for every request, in its original
order. This does not assume semantic correctness implies table membership. -/
theorem binary_static_requests (messages : List (ZiskFv.Channels.BinaryTable.BinaryTableMessage FGL))
    (valid : ∀ message ∈ messages, BinaryTable.binaryTable.Spec message) :
    ∃ indices : List (Fin BinaryTable.tableSize),
      indices.map (fun i => BinaryTable.rowOfIndex i.val) = messages := by
  induction messages with
  | nil => exact ⟨[], rfl⟩
  | cons message rest ih =>
    obtain ⟨i, hi⟩ := valid message (by simp)
    obtain ⟨indices, hind⟩ := ih (fun m hm => valid m (by simp [hm]))
    exact ⟨i :: indices, by simp [hi, hind]⟩

theorem extension_static_requests
    (messages : List (ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage FGL))
    (valid : ∀ message ∈ messages, BinaryExtensionTable.binaryExtensionTable.Spec message) :
    ∃ indices : List (Fin BinaryExtensionTable.tableSize),
      indices.map (fun i => BinaryExtensionTable.rowOfIndex i.val) = messages := by
  induction messages with
  | nil => exact ⟨[], rfl⟩
  | cons message rest ih =>
    obtain ⟨i, hi⟩ := valid message (by simp)
    obtain ⟨indices, hind⟩ := ih (fun m hm => valid m (by simp [hm]))
    exact ⟨i :: indices, by simp [hi, hind]⟩

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
