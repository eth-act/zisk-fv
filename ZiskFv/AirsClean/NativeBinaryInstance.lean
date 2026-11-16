import ZiskFv.AirsClean.BinaryNativeRows
import ZiskFv.AirsClean.BinaryPaddingOperations
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.NativeValuesLayout

/-!
INTERNAL source-owned Binary instance. The sole SourceObject resolver selects
ONE real registry occurrence, setup and original slot; no caller row map,
padding/count certificate, decoder callback or per-segment roster is accepted.
The full physical FinN and one disjoint Unit instance site are retained.

Binary c12 is the source assumes_padding_operation(OP_ADD,padding_size), NOT a
normal row tuple. Every row's existing mainWithBinaryTable operations remain;
exactly one compiled negative raw-p zero-ADD contribution is added per instance.

AIR maps from pinned ff0e stark_info.cpp:125–150 contain name/stage in order,
NOT dim/stageId/stagePos. Native AIR addressing uses its stage-dependent prefix
(expressions_info.cpp:525–532); challenges really carry stage/dim/stageId
(stark_info.cpp:103–110) and use 3*r.id (expressions_info.cpp:545–552).
The actual PIL AIR1 inverse and alpha/gamma retain ALL three bounded words.

This does NOT authenticate native compiled r.id/PIL rank/r.dim, source producer,
accepted images, mutable snapshots or the ABI. The raw scalar is NOT proved to
be num_rows-total_inputs. Source-equation fidelity is NOT equation satisfaction,
numeric gsum/balance, finishedOpBus, or completeness of a production source world.
The c13 finalizer and provider/internal-channel balances remain separate.
-/
namespace ZiskFv.AirsClean

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte
open RawSource RawSource.Native
open Mem.Stage2 (Ext3 extensionWords?)

namespace NativeBinaryInstance

variable {source : SourceObject FGL}

/-- The source projection is computed from ONE resolved occurrence. The actual
native layout supplies padding AIR0; AIR1 is a stage2 inverse in the AIR buffer,
never GROUP/aux. Needed extension blocks are read even when padding is zero.
Unsupported or absent metadata/words fails, without fabricated AIR dimensions. -/
def readOperands? (resolved : ResolvedOccurrence source) :
    Option BinaryPaddingOperations.Operands := do
  let setup ← resolved.setup?
  let paddingEntry ← setup.airValuesMap[0]?
  let inverseEntry ← setup.airValuesMap[1]?
  if paddingEntry.stage = 1 ∧ inverseEntry.stage = 2 then
    let padding ← NativeValuesLayout.paddingValue? .binary (resolved.params false)
    let inverse ← extensionWords? (resolved.airValueWords? false 1)
    let alpha ← Mem.Stage2.challenge? resolved 2 0
    let gamma ← Mem.Stage2.challenge? resolved 2 1
    return ⟨padding, inverse, alpha, gamma⟩
  else none

/-- No free native operand/padding packet: the private factory computes this
selection equality from the source reader itself, not a caller certificate. -/
structure Cells (resolved : ResolvedOccurrence source) where
  private mk ::
  operands : BinaryPaddingOperations.Operands
  selected : readOperands? resolved = some operands

def cells? (resolved : ResolvedOccurrence source) : Option (Cells resolved) :=
  match h : readOperands? resolved with
  | none => none
  | some operands => some ⟨operands, h⟩

theorem Cells.constructor_recovers {resolved : ResolvedOccurrence source}
    (view : Cells resolved) : cells? resolved = some view := by
  rcases view with ⟨operands, h⟩
  unfold cells?
  split
  · rename_i missing
    simp [h] at missing
  · rename_i selected hs
    have heq := Option.some.inj (hs.symm.trans h)
    subst selected
    rfl

end NativeBinaryInstance

/-- All data belongs to one real resolved source occurrence. The existing
row-zero decoder owns profile/native-buffer coverage, and Cells owns the actual
partial native AIR/challenge reads. Both are computed by fromResolved?. -/
structure NativeBinaryInstance (source : SourceObject FGL) where
  private mk ::
  resolved : ResolvedOccurrence source
  anchor : NativeTraceCells.Row .binary resolved false 0
  direct : NativeBinaryInstance.Cells resolved

namespace NativeBinaryInstance

variable {source : SourceObject FGL}

def fromResolved? (resolved : ResolvedOccurrence source) : Option (NativeBinaryInstance source) := do
  let anchor ← NativeTraceCells.row? .binary resolved false 0
  let direct ← cells? resolved
  return ⟨resolved, anchor, direct⟩

def at? (source : SourceObject FGL) (index : source.Occurrence) :
    Option (NativeBinaryInstance source) := do
  let resolved ← source.resolve? index.val
  fromResolved? resolved

def key (view : NativeBinaryInstance source) : OccurrenceKey := view.resolved.key

/-- Constructor recovery is internal representation constructibility, NOT
production/Accepted/native-source existence or authenticity. -/
theorem constructor_recovers (view : NativeBinaryInstance source) :
    fromResolved? view.resolved = some view := by
  rcases view with ⟨resolved, anchor, direct⟩
  simp [fromResolved?, anchor.constructor_recovers, direct.constructor_recovers]

abbrev Index := BinaryNativeRows.Index

def nativeAt (view : NativeBinaryInstance source) (index : Index) :
    NativeTraceCells.Row .binary view.resolved false index.val :=
  BinaryNativeRows.nativeAt view.anchor index

theorem native_getter_total (view : NativeBinaryInstance source) (index : Index) :
    NativeTraceCells.row? .binary view.resolved false index.val = some (view.nativeAt index) :=
  BinaryNativeRows.native_getter_total view.anchor index

def logicalRow? (view : NativeBinaryInstance source) (index : Index) :
    Option (Binary.BinaryRow FGL) := BinaryNativeRows.row? view.anchor index

theorem logical_rows_total (view : NativeBinaryInstance source) (index : Index) :
    ∃ row, view.logicalRow? index = some row := BinaryNativeRows.rows_total view.anchor index

theorem all_source_coordinates (view : NativeBinaryInstance source) (index : Index)
    (row : Binary.BinaryRow FGL) (h : view.logicalRow? index = some row) (column : Fin 39) :
    NativeTraceCells.cell? .binary view.resolved false index.val column.val =
      some (BinaryNativeRows.cells row)[column.val] :=
  BinaryNativeRows.all_source_coordinates view.anchor index row h column

/-- COMPLETE existing row operations: every assertion, ordinary OpBus provider
and all eight BinaryTable consumers. No channel or zero tuple is filtered. -/
def compiledRowOperations (row : Binary.BinaryRow FGL) : Operations FGL :=
  (Binary.mainWithBinaryTable (Binary.constVar row)).operations 0

def rowOperations? (view : NativeBinaryInstance source) (index : Index) :
    Option (Operations FGL) := view.logicalRow? index |>.map compiledRowOperations

theorem row_operations_total (view : NativeBinaryInstance source) (index : Index) :
    ∃ operations, view.rowOperations? index = some operations := by
  obtain ⟨row, hr⟩ := view.logical_rows_total index
  exact ⟨compiledRowOperations row, by simp [rowOperations?, hr]⟩

/-- The raw scalar is selected inside this source-owned constructor. It is not
row count, a caller field, or a zero-padding fallback. -/
def instanceOperations (view : NativeBinaryInstance source) : Operations FGL :=
  (BinaryPaddingOperations.circuit (.const view.direct.operands.padding)).operations 0

/-- FullFinN plus one disjoint site; no list/matrix proportional to physical N. -/
def operationsAt? (view : NativeBinaryInstance source) (site : Index ⊕ Unit) :
    Option (Operations FGL) :=
  match site with
  | .inl index => view.rowOperations? index
  | .inr _ => some view.instanceOperations

theorem emissions_total (view : NativeBinaryInstance source) (site : Index ⊕ Unit) :
    ∃ operations, view.operationsAt? site = some operations := by
  cases site with
  | inl index => exact view.row_operations_total index
  | inr value => exact ⟨view.instanceOperations, rfl⟩

theorem unique_instance_site (view : NativeBinaryInstance source) :
    ∃! site : Index ⊕ Unit, site.isRight = true := by
  refine ⟨Sum.inr (), rfl, ?_⟩
  intro site h
  cases site with
  | inl index => simp at h
  | inr value => cases value; rfl

theorem instance_values (view : NativeBinaryInstance source) (env : Environment FGL) :
    view.instanceOperations.interactionValues env =
      [Channels.OperationBus.OpBusChannel.pushedIfValue (-view.direct.operands.padding)
        BinaryPaddingOperations.zeroADD] := by
  rcases BinaryPaddingOperations.source_tuple_and_compiled view.direct.operands.padding env with
    ⟨_, _, _, _, _, _, compiled⟩
  exact compiled

/-- This theorem binds the ACTUAL normal generated c12 AST to the ACTUAL
compiled once-instance interaction using the SAME source-selected values. -/
theorem source_direct_residual_eq_operations (view : NativeBinaryInstance source)
    (env : Environment FGL) :
    BinaryPaddingOperations.actualResidual? view.direct.operands =
      BinaryPaddingOperations.compiledResidual? view.direct.operands view.instanceOperations env :=
  BinaryPaddingOperations.actual_residual_eq_compiled view.direct.operands env

theorem source_direct_all_coefficients (view : NativeBinaryInstance source)
    (env : Environment FGL) (coefficient : Fin 3) :
    (BinaryPaddingOperations.actualResidual? view.direct.operands).map
        (fun residual => Ext3.coeff residual coefficient) =
      (BinaryPaddingOperations.compiledResidual? view.direct.operands view.instanceOperations env).map
        (fun residual => Ext3.coeff residual coefficient) := by
  rw [source_direct_residual_eq_operations]

/-- Registry-sized computed selection ONLY; other AIRs are not deleted from a
source-world balance. Actual segment/source/compiled-id authentication is not
inferred from the roster's internal identity law. -/
def selectedOccurrences (source : SourceObject FGL) : List source.Occurrence :=
  source.occurrences.filter fun index =>
    let entry := source.registryEntry index
    entry.airgroupId == 0 && entry.airId == 22

def roster? (source : SourceObject FGL) : Option (List (NativeBinaryInstance source)) :=
  (selectedOccurrences source).mapM (at? source)

private theorem fromResolved_preserves (resolved : ResolvedOccurrence source)
    (view : NativeBinaryInstance source) (h : fromResolved? resolved = some view) :
    view.resolved = resolved := by
  unfold fromResolved? at h
  cases ha : NativeTraceCells.row? .binary resolved false 0 with
  | none => simp [ha] at h
  | some anchor =>
    cases hd : cells? resolved with
    | none => simp [ha, hd] at h
    | some direct =>
      have heq : (⟨resolved, anchor, direct⟩ : NativeBinaryInstance source) = view := by
        simpa [ha, hd] using h
      cases heq
      rfl

private theorem at_occurrence (source : SourceObject FGL) (index : source.Occurrence)
    (view : NativeBinaryInstance source) (h : at? source index = some view) :
    view.resolved.occurrence = index := by
  unfold at? at h
  cases hr : source.resolve? index.val with
  | none => simp [hr] at h
  | some resolved =>
    have hf : fromResolved? resolved = some view := by simpa [hr] using h
    have hs := fromResolved_preserves resolved view hf
    apply Fin.ext
    change view.resolved.globalSlot = index.val
    rw [hs]
    exact source.resolve_globalSlot index.val resolved hr

/-- Every selected occurrence is preserved in order, with no silent exclusions. -/
private theorem map_occurrences (source : SourceObject FGL)
    (indices : List source.Occurrence) (instances : List (NativeBinaryInstance source))
    (h : indices.mapM (at? source) = some instances) :
    instances.map (fun view => view.resolved.occurrence) = indices := by
  induction indices generalizing instances with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    cases h
    rfl
  | cons index rest ih =>
    rw [List.mapM_cons] at h
    cases hp : at? source index with
    | none => simp [hp] at h
    | some view =>
      cases ht : rest.mapM (at? source) with
      | none => simp [hp, ht] at h
      | some tail =>
        have heq : view :: tail = instances := by simpa [hp, ht] using h
        subst instances
        simp only [List.map_cons]
        exact congrArg₂ List.cons (at_occurrence source index view hp) (ih tail ht)

theorem roster_occurrences (source : SourceObject FGL)
    (instances : List (NativeBinaryInstance source)) (h : roster? source = some instances) :
    instances.map (fun view => view.resolved.occurrence) = selectedOccurrences source :=
  map_occurrences source (selectedOccurrences source) instances h

theorem roster_keys_nodup (source : SourceObject FGL)
    (instances : List (NativeBinaryInstance source)) (h : roster? source = some instances) :
    (instances.map key).Nodup := by
  have hi := roster_occurrences source instances h
  have hk : ((selectedOccurrences source).map source.key).Nodup := by
    apply List.Nodup.map source.key_injective
    exact (List.nodup_ofFn_ofInjective (fun _ _ eq => eq)).filter _
  rw [← hi] at hk
  simpa only [List.map_map, key, ResolvedOccurrence.key, Function.comp_def] using hk

end NativeBinaryInstance
end ZiskFv.AirsClean
