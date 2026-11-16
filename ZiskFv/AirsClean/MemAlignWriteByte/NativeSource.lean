import ZiskFv.AirsClean.NativeTraceCells
import ZiskFv.AirsClean.MemAlignWriteByte.NativeValues

/-! INTERNAL canonical WriteByte physical-row/value join.

Requires the sole owner's actual WriteByte Kind/profile extension; the separate
RuntimeMemWriteByteTraceLayout profile is NOT replaced by another AIR's profile.
No private copy of the native getter, callback, default-zero reader, SourceValid,
independent old-world row, or equality/roster input is introduced.

One canonical SourceObject/ResolvedOccurrence supplies original UInt64 trace
words, actual row profile, padding AIR0, im_direct[3] Ext3 and separate GROUP0
Ext3 words. Native/PIL/serialized-program/ABI/Accepted materialization is still
not a consequence of this typed dataflow constructor. Local constraints must
come from actual local operations, never be asserted by decoder success. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte.NativeSource

open Goldilocks RawSource.Native
open ZiskFv.AirsClean

/-- Sole actual field-STORAGE view: no Boolean/narrow Rust getter cast is
substituted for source polynomial data (e.g. unpacked field2 remains field2). -/
def cells? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) (row : Nat) : Option NativeRow.Cells := do
  let view ← NativeTraceCells.row? .writeByte resolved mode row
  view.values?

/-- Computed output DATA. A caller does not supply an authentication, source
validity, roster or equality certificate to construct this projection. -/
structure Projection where
  cells : NativeRow.Cells
  values : NativeValues.Values

def project? {source : SourceObject FGL} (resolved : ResolvedOccurrence source)
    (mode : Bool) (row : Nat) : Option Projection := do
  let cells ← cells? resolved mode row
  let values ← NativeValues.sourceValues? resolved mode
  return ⟨cells, values⟩

def Projection.localRow (projection : Projection) : MemAlignWriteByteRow FGL :=
  NativeRow.ofCells projection.cells

/-- Source tuple operands are load-bearing in the returned local operations. -/
def Projection.operations? (projection : Projection) (offset : Nat) :
    Option (Operations FGL) :=
  NativeTupleSource.sourceOperations? projection.cells projection.values.padding offset

def Projection.rowInteractions (projection : Projection) : List (Interaction FGL) :=
  NativeRow.interactionValues projection.cells

/-- Once-per-occurrence Direct contribution, NOT a per-physical-row emission.
An actual global once-only roster remains the integration owner's obligation. -/
def Projection.onceDirects (projection : Projection) : List (Interaction FGL) :=
  projection.values.directs

theorem project_same_source {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection) :
    cells? resolved mode row = some projection.cells ∧
      NativeValues.sourceValues? resolved mode = some projection.values := by
  unfold project? at h
  cases hc : cells? resolved mode row with
  | none => simp [hc, bind, pure] at h
  | some cells =>
    cases hv : NativeValues.sourceValues? resolved mode with
    | none => simp [hc, hv, bind, pure] at h
    | some values =>
      have heq : (⟨cells, values⟩ : Projection) = projection := by
        simpa [hc, hv, bind, pure] using h
      subst projection
      exact ⟨rfl, rfl⟩

/-- Registry labels select the real setup/Params occurrence; independent slot
task metadata is not strengthened by a new equality validator. -/
theorem project_registry_identity {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection) :
    resolved.registryEntry.airgroupId = 0 ∧ resolved.registryEntry.airId = 20 := by
  have hv := (project_same_source resolved mode row projection h).2
  have hd := NativeValues.source_values_same_params resolved mode projection.values hv
  exact ⟨hd.1, hd.2.1⟩

/-- Changing physical row does not create a new AIR/GROUP value occurrence.
This data equality does NOT enforce global once-only Direct enumeration. -/
theorem same_occurrence_values {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (firstRow secondRow : Nat)
    (first second : Projection)
    (hf : project? resolved mode firstRow = some first)
    (hs : project? resolved mode secondRow = some second) :
    first.values = second.values :=
  Option.some.inj ((project_same_source resolved mode firstRow first hf).2.symm.trans
    (project_same_source resolved mode secondRow second hs).2)

/-- All fourteen source coordinates are obtained from the same sole getter,
not from separately supplied row/source equalities or an otherMain callback. -/
theorem cells_coordinates {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (cells : NativeRow.Cells) (h : cells? resolved mode row = some cells)
    (column : Fin 14) :
    NativeTraceCells.cell? .writeByte resolved mode row column.val = some cells[column.val] := by
  unfold cells? at h
  cases hv : NativeTraceCells.row? .writeByte resolved mode row with
  | none => simp [hv, bind, pure] at h
  | some view =>
    have hc : view.values? = some cells := by simpa [hv, bind, pure] using h
    exact view.values_coordinates cells hc column

theorem project_coordinates {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection)
    (column : Fin 14) :
    NativeTraceCells.cell? .writeByte resolved mode row column.val =
      some projection.cells[column.val] :=
  cells_coordinates resolved mode row projection.cells (project_same_source resolved mode row projection h).1 column

theorem project_padding_same_slot {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection) :
    resolved.slotData.airvalues[0]? = some projection.values.padding :=
  NativeValues.source_padding_same_slot resolved mode projection.values
    (project_same_source resolved mode row projection h).2

/-- GROUP words are read from the separate source buffer, even when AIR0 is
present, and carry no invented FromTrace transfer or stage2 arithmetic theorem. -/
theorem project_group_same_params {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection) :
    (do return #v[← (resolved.params mode).airgroupValues[0]?,
      ← (resolved.params mode).airgroupValues[1]?,
      ← (resolved.params mode).airgroupValues[2]?]) = some projection.values.groupWords := by
  have hv := (project_same_source resolved mode row projection h).2
  exact NativeValues.decoded_group_actual (resolved.params mode) projection.values
    (NativeValues.source_values_same_params resolved mode projection.values hv).2.2

/-- Each Ext3 uses its actual ordered native AIR prefix, separate from GROUP
and from PIL's logical array index. No guessed 1+i native word address occurs. -/
theorem project_inverse_same_params {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection)
    (index : Fin 3) :
    (do return #v[← (resolved.params mode).airvalues[1 + 3 * index.val]?,
      ← (resolved.params mode).airvalues[(1 + 3 * index.val) + 1]?,
      ← (resolved.params mode).airvalues[(1 + 3 * index.val) + 2]?]) =
      some projection.values.directInverses[index.val] := by
  have hv := (project_same_source resolved mode row projection h).2
  have hd := NativeValues.decoded_values_source (resolved.params mode) projection.values
    (NativeValues.source_values_same_params resolved mode projection.values hv).2.2
  rw [← NativeValues.inverse_reads_actual_buffer index]
  fin_cases index
  · exact hd.2.2.1
  · exact hd.2.2.2.1
  · exact hd.2.2.2.2

theorem project_directs_same_params {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (projection : Projection) (h : project? resolved mode row = some projection) :
    NativeTupleSource.directValues? (resolved.params mode) = some projection.onceDirects := by
  have hv := (project_same_source resolved mode row projection h).2
  exact NativeValues.decoded_directs_actual (resolved.params mode) projection.values
    (NativeValues.source_values_same_params resolved mode projection.values hv).2.2

/-- A constructed finite source row has all actual field coordinates, not an
always-None fallback. No SourceValid or row-count/count-scalar premise is needed. -/
theorem cells_constructible {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (view : NativeTraceCells.Row .writeByte resolved mode row) :
    ∃ cells, cells? resolved mode row = some cells := by
  obtain ⟨cells, hc⟩ := view.values_defined
  refine ⟨cells, ?_⟩
  simp [cells?, view.constructor_recovers, hc]

theorem project_constructible {source : SourceObject FGL}
    (resolved : ResolvedOccurrence source) (mode : Bool) (row : Nat)
    (view : NativeTraceCells.Row .writeByte resolved mode row) (values : NativeValues.Values)
    (hv : NativeValues.sourceValues? resolved mode = some values) :
    ∃ projection, project? resolved mode row = some projection := by
  obtain ⟨cells, hc⟩ := cells_constructible resolved mode row view
  exact ⟨⟨cells, values⟩, by simp [project?, hc, hv]⟩

theorem operations_existing_main (projection : Projection) (offset : Nat) :
    projection.operations? offset = some (NativeRow.operations projection.cells offset) :=
  NativeTupleSource.sourceOperations_eq projection.cells projection.values.padding offset

/-- This implication consumes ACTUAL local operations; projection success is
not presented as native constraints or an Accepted-world soundness promise. -/
theorem local_spec (projection : Projection) (offset : Nat) (ops : Operations FGL)
    (env : Environment FGL) (hops : projection.operations? offset = some ops)
    (hholds : ConstraintsHold.Soundness env ops) : Spec projection.localRow :=
  NativeTupleSource.spec_of_sourceOperations projection.cells projection.values.padding
    offset ops env hops hholds

theorem local_residuals (projection : Projection) (offset : Nat) (ops : Operations FGL)
    (env : Environment FGL) (hops : projection.operations? offset = some ops)
    (hholds : ConstraintsHold.Soundness env ops) : NativeRow.ResidualsHold projection.cells :=
  (NativeRow.residuals_iff_polynomialSpec projection.cells).mpr
    (local_spec projection offset ops env hops hholds).1

/-- The same source-decoded operation list, not a separate interaction oracle,
evaluates to the four expected real row messages. -/
theorem operations_row_interactions (projection : Projection) (offset : Nat)
    (ops : Operations FGL) (env : Environment FGL)
    (hops : projection.operations? offset = some ops) :
    (ops.interactions.map (fun interaction => interaction.eval env)) =
      projection.rowInteractions := by
  rw [operations_existing_main] at hops
  cases Option.some.inj hops
  exact NativeRow.operations_interaction_values projection.cells offset env

/-- Raw field multiplicities remain unrestricted, including zero and -1. -/
theorem once_direct_multiplicities (projection : Projection) :
    projection.onceDirects.map Interaction.mult =
      [projection.values.padding, -projection.values.padding, projection.values.padding] := rfl

/-- Four actual row messages remain distinct from the three once-only Direct
messages, including timestamp0 internal byte/Mem counterpart cases. -/
theorem row_and_direct_counts (projection : Projection) :
    projection.rowInteractions.length = 4 ∧ projection.onceDirects.length = 3 := by
  constructor <;> rfl

end ZiskFv.AirsClean.MemAlignWriteByte.NativeSource
