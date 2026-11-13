import Extraction.RomSource
import ZiskFv.AirsClean.ZiskInstructionRomProvider

/-!
# Actual Rom source projection

The generated source retains typed custom-commit IDs, stages, columns and signed
rotations. Only the actual image cells and stage-1 multiplicity cell are replaced
below; all other source cells retain their ambient interpretation. In particular
there is no default-zero interpreter and no parsing of Debug/opaque expressions.
Public-root authentication of `image` is outside these algebraic projections.
-/
namespace ZiskFv.AirsClean.ZiskInstructionRomSource

open Goldilocks
open ZiskFv.Channels.ZiskRomBus
open ZiskFv.AirsClean.ZiskInstructionRom
open ZiskFv.AirsClean.ZiskInstructionRomProvider
open Extraction.RomSource

/-- Signed cyclic source addressing, including predecessor of physical row zero.
The outer Nat modulus only constructs the bounded index; Int modulus already
implements the physical wrap for negative rows. -/
def physicalIndex {capacity : Nat} (positive : 0 < capacity)
    (row rotation : Int) : Fin capacity :=
  ⟨((row + rotation) % (capacity : Int)).toNat % capacity, Nat.mod_lt _ positive⟩

@[simp] theorem physicalIndex_current {capacity : Nat} (positive : 0 < capacity)
    (index : Fin capacity) : physicalIndex positive (index.val : Int) 0 = index := by
  apply Fin.ext
  simp [physicalIndex, ← Int.natCast_mod, Nat.mod_eq_of_lt index.isLt]

/-- The actual stage-0 custom commitment and stage-1 multiplicity column.
Unrelated source cells remain independent, including the stage-2 lookup
accumulator and challenges; their polynomial argument is not asserted here. -/
def sourceOfImage {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (multiplicities : Fin capacity → FGL)
    (ambient : CommittedSource FGL) : CommittedSource FGL :=
  { ambient with
    custom := fun commit stage column row rotation =>
      if h : commit = 0 ∧ stage = 0 ∧ column < 11 then
        imageValues image ⟨column, h.2.2⟩ (physicalIndex positive row rotation)
      else ambient.custom commit stage column row rotation
    witness := fun stage column row rotation =>
      if stage = 1 ∧ column = 0 then
        multiplicities (physicalIndex positive row rotation)
      else ambient.witness stage column row rotation }

/-- This theorem depends on the actual generated hint projection. Reordering a
source custom column or changing its commitment/stage/rotation breaks it. -/
theorem lookupTuple_sourceOfImage {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (multiplicities : Fin capacity → FGL)
    (ambient : CommittedSource FGL) (index : Fin capacity) :
    Extraction.RomSource.lookupTuple
        (sourceOfImage positive image multiplicities ambient) (index.val : Int) =
      [(image index).line, (image index).a_offset_imm0, (image index).a_imm1,
        (image index).b_offset_imm0, (image index).b_imm1, (image index).ind_width,
        (image index).op, (image index).store_offset, (image index).jmp_offset1,
        (image index).jmp_offset2, (image index).flags] := by
  simp [Extraction.RomSource.lookupTuple, sourceOfImage, imageValues]

/-- Positive-side weight is exactly the unconstrained witness multiplicity. -/
theorem multiplicity_sourceOfImage {capacity : Nat} (positive : 0 < capacity)
    (image : Program capacity) (multiplicities : Fin capacity → FGL)
    (ambient : CommittedSource FGL) (index : Fin capacity) :
    Extraction.RomSource.multiplicity
        (sourceOfImage positive image multiplicities ambient) (index.val : Int) =
      multiplicities index := by
  simp [Extraction.RomSource.multiplicity, sourceOfImage]

/-- Source identifies the actual ROM channel and its provider direction. -/
theorem source_bus_direction (source : CommittedSource FGL) (row : Int) :
    Extraction.RomSource.busId source row = 7890 ∧
      Extraction.RomSource.providerKind source row = 1 := by
  constructor <;> rfl

/-- The generated physical source tuple is the provider's actual materialized
typed message, with no supplied tuple correspondence certificate. -/
theorem source_tuple_eq_materialized_provider {capacity : Nat}
    (positive : 0 < capacity) (image : Program capacity)
    (multiplicities : Fin capacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin capacity) (data : ProverData FGL) (raw : Array FGL) :
    let row := Eval.eval
      (Environment.fromArray ((imageColumns positive image).materialize index.val raw) data)
      (varFromOffset (F := FGL) RomRow 0)
    Extraction.RomSource.lookupTuple
        (sourceOfImage positive image multiplicities ambient) (index.val : Int) =
      [row.message.line, row.message.a_offset_imm0, row.message.a_imm1,
        row.message.b_offset_imm0, row.message.b_imm1, row.message.ind_width,
        row.message.op, row.message.store_offset, row.message.jmp_offset1,
        row.message.jmp_offset2, row.message.flags] := by
  dsimp only
  rw [eval_materialize]
  exact lookupTuple_sourceOfImage positive image multiplicities ambient index

/-- The generated positive-side weight is the actual provider interaction's
weight on the constructible witness, not an independent multiplicity oracle. -/
theorem source_multiplicity_eq_materialized_provider {capacity : Nat}
    (positive : 0 < capacity) (image : Program capacity)
    (multiplicities : Fin capacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin capacity) (data : ProverData FGL) :
    Extraction.RomSource.multiplicity
        (sourceOfImage positive image multiplicities ambient) (index.val : Int) =
      (((ZiskRomBusChannel.emitted
        (varFromOffset (F := FGL) RomRow 0).multiplicity
        (varFromOffset (F := FGL) RomRow 0).message).toRaw).eval
          (Environment.fromArray
            ((imageColumns positive image).materialize index.val #[multiplicities index])
            data)).mult := by
  rw [multiplicity_sourceOfImage, materialized_multiplicity]
  simp

end ZiskFv.AirsClean.ZiskInstructionRomSource
