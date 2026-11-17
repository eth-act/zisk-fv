import ZiskFv.AirsClean.PackedVirtualTableSources
import Clean.Air.Balance

/-!
# Constructible packed multiplicities for actual source-index requests

Request indices identify exact source rows, not opcode approximations or
message deduplication. Repeated indices are counted; distinct source indices
with the same payload are not accidentally counted twice. The algebraic
balance theorem has no semantic or channel-guarantee premise.
-/

namespace ZiskFv.AirsClean.PackedVirtualTableSources

open Goldilocks Air.Flat
open Extraction.PackedVirtualTables

private theorem balanceOf_sum (interactions : List (Interaction FGL)) (message : Array FGL) :
    balanceOf interactions message =
      (interactions.map fun interaction =>
        if interaction.msg = message then interaction.mult else 0).sum := by
  induction interactions with
  | nil => rfl
  | cons interaction rest ih =>
    rw [balanceOf_cons, List.map_cons, List.sum_cons, ih]

variable {Message : TypeMap} [ProvableType Message]

def countedSourceInteractions {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n)) : List (Interaction FGL) :=
  List.ofFn fun index => channel.pushedIfValue (requests.count index : FGL) (row index)

/-- `emitted (-1)` has `assumeGuarantees=false`, just like this value form;
    no channel membership assertion is built into these consumer messages. -/
def consumedSourceRequests {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n)) : List (Interaction FGL) :=
  requests.map fun index => channel.pushedIfValue (-1) (row index)

private theorem count_weight_sum {n : Nat} (requests : List (Fin n)) (f : Fin n → FGL) :
    (∑ index : Fin n, (requests.count index : FGL) * f index) =
      (requests.map f).sum := by
  rw [Finset.sum_list_map_count]
  have heq : (∑ index ∈ requests.toFinset, requests.count index • f index) =
      ∑ index : Fin n, requests.count index • f index := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro index _ hnot
    have hnot' : index ∉ requests := by simpa only [List.mem_toFinset] using hnot
    simp only [List.count_eq_zero.mpr hnot', zero_nsmul]
  simpa only [nsmul_eq_mul] using heq.symm

theorem countedSourceInteractions_balanceOf {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n)) (message : Array FGL) :
    balanceOf (countedSourceInteractions channel row requests) message =
      (requests.map fun index =>
        if (toElements (row index)).toArray = message then (1 : FGL) else 0).sum := by
  rw [balanceOf_sum]
  simp only [countedSourceInteractions, List.map_ofFn, List.sum_ofFn,
    Channel.pushedIfValue, Function.comp_apply]
  calc
    (∑ index : Fin n, if (toElements (row index)).toArray = message then
        (requests.count index : FGL) else 0) =
      ∑ index : Fin n, (requests.count index : FGL) *
        (if (toElements (row index)).toArray = message then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro index _
      split <;> simp_all
    _ = _ := count_weight_sum requests _

theorem consumedSourceRequests_balanceOf {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n)) (message : Array FGL) :
    balanceOf (consumedSourceRequests channel row requests) message =
      -(requests.map fun index =>
        if (toElements (row index)).toArray = message then (1 : FGL) else 0).sum := by
  induction requests with
  | nil => simp [consumedSourceRequests, balanceOf]
  | cons index rest ih =>
    change balanceOf (channel.pushedIfValue (-1) (row index) ::
      consumedSourceRequests channel row rest) message = _
    rw [balanceOf_cons, ih]
    by_cases h : (toElements (row index)).toArray = message <;>
      simp [Channel.pushedIfValue, h, neg_add, add_comm]

/-- Per-message balance of a real full-domain source multiplicity witness and
    its negative requests. The separate count bound is stated explicitly. -/
theorem countedSourceRequests_balanced {n : Nat} (channel : Channel FGL Message)
    (row : Fin n → Message FGL) (requests : List (Fin n))
    (hcount : n + requests.length < ringChar FGL) :
    BalancedInteractions (countedSourceInteractions channel row requests ++
      consumedSourceRequests channel row requests) := by
  refine ⟨Or.inl ?_, ?_⟩
  · simpa only [countedSourceInteractions, consumedSourceRequests,
      List.length_append, List.length_ofFn, List.length_map] using hcount
  · intro message
    rw [balanceOf_append, countedSourceInteractions_balanceOf,
      consumedSourceRequests_balanceOf, add_neg_cancel]

/-- Construct both Binary-family sources in the same actual physical witness.
    The input lists are the source indices for the consumer routes (all eight
    per row); no source payload or map equality is supplied as a premise. -/
def physicalOfRequests (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize)) : Witness FGL :=
  physicalOfLogical base
    { bus88 := project base source88
      bus124 := fun index => ((extensionRequests.map extensionIndex).count index : FGL)
      bus125 := fun index => ((binaryRequests.map binaryIndex).count index : FGL)
      bus330 := project base source330
      bus331 := project base source331 }

private theorem binaryIndex_injective : Function.Injective binaryIndex := by
  intro left right h
  apply Fin.ext
  exact congrArg Fin.val h

private theorem extensionIndex_injective : Function.Injective extensionIndex := by
  intro left right h
  apply Fin.ext
  exact congrArg Fin.val h

theorem binaryRow_requests_multiplicity (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize))
    (index : Fin BinaryTable.tableSize) :
    (binaryRow (physicalOfRequests base binaryRequests extensionRequests) index).multiplicity =
      (binaryRequests.count index : FGL) := by
  simp only [binaryRow, physicalOfRequests, project125_physicalOfLogical,
    List.count_map_of_injective _ _ binaryIndex_injective]

theorem extensionRow_requests_multiplicity (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize))
    (index : Fin BinaryExtensionTable.tableSize) :
    (extensionRow (physicalOfRequests base binaryRequests extensionRequests) index).multiplicity =
      (extensionRequests.count index : FGL) := by
  simp only [extensionRow, physicalOfRequests, project124_physicalOfLogical,
    List.count_map_of_injective _ _ extensionIndex_injective]

open ZiskFv.Channels.BinaryTable (BinaryTableChannel)
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableChannel)

theorem binaryInteractions_physicalOfRequests (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize)) :
    binaryInteractions (physicalOfRequests base binaryRequests extensionRequests) =
      countedSourceInteractions BinaryTableChannel
        (fun index : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex index.val) binaryRequests := by
  apply congrArg (fun f : Fin BinaryTable.tableSize → Interaction FGL => List.ofFn f)
  funext index
  change BinaryTableChannel.pushedIfValue
      (binaryRow (physicalOfRequests base binaryRequests extensionRequests) index).multiplicity
      (BinaryTable.rowOfIndex index.val) = _
  rw [binaryRow_requests_multiplicity]

theorem extensionInteractions_physicalOfRequests (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize)) :
    extensionInteractions (physicalOfRequests base binaryRequests extensionRequests) =
      countedSourceInteractions BinaryExtensionTableChannel
        (fun index : Fin BinaryExtensionTable.tableSize =>
          BinaryExtensionTable.rowOfIndex index.val) extensionRequests := by
  apply congrArg (fun f : Fin BinaryExtensionTable.tableSize → Interaction FGL => List.ofFn f)
  funext index
  change BinaryExtensionTableChannel.pushedIfValue
      (extensionRow (physicalOfRequests base binaryRequests extensionRequests) index).multiplicity
      (BinaryExtensionTable.rowOfIndex index.val) = _
  rw [extensionRow_requests_multiplicity]

/-- A concrete row has exactly eight source-index requests. Its real source
    multiplicity witness and those eight negative messages balance without
    any caller count-bound premise. The other source shares the same raw. -/
theorem binaryEightRequests_balanced (base : Witness FGL)
    (requests : Fin 8 → Fin BinaryTable.tableSize)
    (extensionRequests : List (Fin BinaryExtensionTable.tableSize)) :
    BalancedInteractions
      (binaryInteractions (physicalOfRequests base (List.ofFn requests) extensionRequests) ++
        consumedSourceRequests BinaryTableChannel
          (fun index : Fin BinaryTable.tableSize => BinaryTable.rowOfIndex index.val)
          (List.ofFn requests)) := by
  rw [binaryInteractions_physicalOfRequests]
  apply countedSourceRequests_balanced
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  norm_num [BinaryTable.tableSize]

theorem extensionEightRequests_balanced (base : Witness FGL)
    (binaryRequests : List (Fin BinaryTable.tableSize))
    (requests : Fin 8 → Fin BinaryExtensionTable.tableSize) :
    BalancedInteractions
      (extensionInteractions (physicalOfRequests base binaryRequests (List.ofFn requests)) ++
        consumedSourceRequests BinaryExtensionTableChannel
          (fun index : Fin BinaryExtensionTable.tableSize =>
            BinaryExtensionTable.rowOfIndex index.val)
          (List.ofFn requests)) := by
  rw [extensionInteractions_physicalOfRequests]
  apply countedSourceRequests_balanced
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
  norm_num [BinaryExtensionTable.tableSize,
    BinaryExtensionTable.shiftBlockSize, BinaryExtensionTable.sextBlockSize]

end ZiskFv.AirsClean.PackedVirtualTableSources
