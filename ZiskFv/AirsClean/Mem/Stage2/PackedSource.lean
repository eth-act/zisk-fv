import ZiskFv.AirsClean.Mem.PhysicalSource.Columns

/-! Internal stage1 correspondence through the sole NativeTraceCells Mem getter.
The actual setup supplies every signed cyclic rotation. Raw UInt64 decoding
precedes the existing Goldilocks conversion, which precedes Ext3.ofBase.
No stage1 cmPolsMap match, storage-mode restriction, read-success/coherence
premise or extra range/height check is required of a CompleteView. Source
stage/column identifiers still do not authenticate compiled PILr operand ids,
native execution, live buffers or ABI materialization. -/
namespace ZiskFv.AirsClean.Mem.Stage2

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open ZiskFv.AirsClean.Mem.PhysicalSource

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- Every finite stage1 column uses the canonical getter at the setup's actual
rotation, including failure of setup, rotation or native cell decoding. -/
theorem witness_stage1_eq_canonical (resolved : ResolvedOccurrence source) (row : Nat)
    (column : Fin 13) (rotation : Int) :
    witness? resolved row 1 column.val rotation = (do
      let setup ← resolved.setup?
      let shifted ← setup.baseRow? row rotation
      return Ext3.ofBase (← ZiskFv.AirsClean.NativeTraceCells.cell?
        .mem resolved false shifted column.val)) := by
  unfold witness?
  rw [if_pos (Or.inl ⟨rfl, column.isLt⟩)]
  rfl

/-- Generic selected-setup equation; the right side remains partial, not an
assumed successful scalar read. There is no stage1 metadata-map lookup. -/
theorem witness_stage1_at (resolved : ResolvedOccurrence source) (setup : NativeSetup)
    (row shifted : Nat) (column : Fin 13) (rotation : Int)
    (selected : resolved.setup? = some setup)
    (shift : setup.baseRow? row rotation = some shifted) :
    witness? resolved row 1 column.val rotation =
      (ZiskFv.AirsClean.NativeTraceCells.cell? .mem resolved false shifted column.val).map
        Ext3.ofBase := by
  rw [witness_stage1_eq_canonical]
  simp only [selected, shift, bind, Option.bind_some]
  cases ZiskFv.AirsClean.NativeTraceCells.cell? .mem resolved false shifted column.val <;> rfl

/-- Raw-first conversion for ANY selected setup and shifted row. The canonical
raw getter itself selects packed bits or unpacked words in the original store;
there is no conversion of a packed storage word before bit extraction. -/
theorem witness_stage1_raw_first (resolved : ResolvedOccurrence source) (setup : NativeSetup)
    (row shifted : Nat) (column : Fin 13) (rotation : Int)
    (selected : resolved.setup? = some setup)
    (shift : setup.baseRow? row rotation = some shifted) :
    witness? resolved row 1 column.val rotation =
      (ZiskFv.AirsClean.NativeTraceCells.rawCell? .mem resolved false shifted column.val).map
        (fun raw => Ext3.ofBase (NativeTraceWords.unpackedField raw)) := by
  rw [witness_stage1_at resolved setup row shifted column rotation selected shift,
    ZiskFv.AirsClean.NativeTraceCells.field_after_raw, Option.map_map]
  rfl

/-- All thirteen columns and arbitrary signed rotations of EVERY computed
CompleteView recover the model scalar, in either native storage mode. -/
theorem witness_stage1_source (view : CompleteView resolved) (row : view.Index)
    (column : Fin 13) (rotation : Int) :
    witness? resolved row.val 1 column.val rotation =
      some (Ext3.ofBase (view.scalar (view.base.rotate row rotation) column)) := by
  rw [witness_stage1_at resolved view.base.setup row.val
    (view.base.rotate row rotation).val column rotation view.base.setupSelected
    (view.base.native_rotation row rotation), view.scalar_source]
  rfl

/-- Explicit simultaneous storage-mode coverage. Neither branch introduces a
new premise for reader success; both instantiate the same canonical theorem. -/
theorem witness_stage1_both_storage_modes (view : CompleteView resolved)
    (row : view.Index) (column : Fin 13) (rotation : Int) :
    (resolved.slotData.metadata.isPacked = true →
      witness? resolved row.val 1 column.val rotation =
        some (Ext3.ofBase (view.scalar (view.base.rotate row rotation) column))) ∧
    (resolved.slotData.metadata.isPacked = false →
      witness? resolved row.val 1 column.val rotation =
        some (Ext3.ofBase (view.scalar (view.base.rotate row rotation) column))) :=
  ⟨fun _ => witness_stage1_source view row column rotation,
   fun _ => witness_stage1_source view row column rotation⟩

/-- The stage2 reader retains precisely its existing setup/map/block path. -/
theorem witness_stage2_eq_metadata (resolved : ResolvedOccurrence source) (row : Nat)
    (column : Fin 3) (rotation : Int) :
    witness? resolved row 2 column.val rotation = (do
      let setup ← resolved.setup?
      let mapId ← witnessMapId? setup 2 column.val
      extensionWords? (resolved.cmWords? false mapId row rotation)) := by
  unfold witness?
  rw [if_pos (Or.inr ⟨rfl, column.isLt⟩)]
  rfl

end ZiskFv.AirsClean.Mem.Stage2
