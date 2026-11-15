import ZiskFv.AirsClean.ZiskInstructionRomImage
import ZiskFv.AirsClean.ZiskInstructionRomProvider
import ZiskFv.AirsClean.Main.RomWiring

/-!
# Actual Rom source projection

Every source image and rotation uses the compiled 4194304-row physical domain,
not the length of an unpadded Program. Typed custom-commit IDs, stages, columns
and signed rotations are retained. Only actual image and multiplicity cells are
replaced; unrelated cells retain their ambient interpretation. Public-root
image authentication and producer/lowering binding remain external boundaries.
-/
namespace ZiskFv.AirsClean.ZiskInstructionRomSource

open Goldilocks
open ZiskFv.Channels.ZiskRomBus
open ZiskFv.AirsClean.ZiskInstructionRom
open ZiskFv.AirsClean.ZiskInstructionRomProvider
open ZiskFv.AirsClean.ZiskInstructionRomImage
open Extraction.RomSource

/-- Exact stage-0 custom commitment and stage-1 multiplicity column on the
actual physical domain. In particular predecessor-of-zero wraps at 4194304,
regardless of the decoded Program's instruction count. -/
def sourceOfImage (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL)
    (ambient : CommittedSource FGL) : CommittedSource FGL :=
  { ambient with
    custom := fun commit stage column row rotation =>
      if h : commit = 0 ∧ stage = 0 ∧ column < 11 then
        imageValues image ⟨column, h.2.2⟩ (physicalIndex row rotation)
      else ambient.custom commit stage column row rotation
    witness := fun stage column row rotation =>
      if stage = 1 ∧ column = 0 then multiplicities (physicalIndex row rotation)
      else ambient.witness stage column row rotation }

/-- Reordering a source custom column or changing commitment/stage/rotation
breaks this theorem against the actual generated hint projection. -/
theorem lookupTuple_sourceOfImage (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin physicalCapacity) :
    Extraction.RomSource.lookupTuple (sourceOfImage image multiplicities ambient)
        (index.val : Int) =
      [(image index).line, (image index).a_offset_imm0, (image index).a_imm1,
        (image index).b_offset_imm0, (image index).b_imm1, (image index).ind_width,
        (image index).op, (image index).store_offset, (image index).jmp_offset1,
        (image index).jmp_offset2, (image index).flags] := by
  simp [Extraction.RomSource.lookupTuple, sourceOfImage, imageValues]

theorem multiplicity_sourceOfImage (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin physicalCapacity) :
    Extraction.RomSource.multiplicity (sourceOfImage image multiplicities ambient)
        (index.val : Int) = multiplicities index := by
  simp [Extraction.RomSource.multiplicity, sourceOfImage]

theorem source_bus_direction (source : CommittedSource FGL) (row : Int) :
    Extraction.RomSource.busId source row = 7890 ∧
      Extraction.RomSource.providerKind source row = 1 := by
  constructor <;> rfl

/-- Actual compiled provider, not an arbitrary-capacity table. -/
def physicalComponent (image : PhysicalImage) : Air.Flat.Component FGL :=
  component physicalCapacity_pos image

def physicalProviderTable (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (data : ProverData FGL) :
    Air.Flat.Table FGL := providerTable physicalCapacity_pos image multiplicities data

/-- Internal total constructor over a final-row padding result. Successful
source/provider share the same intrinsic physical image; no source-history
realization or authentication is asserted by this constructed example. -/
def sourceAndProvider (output : FinalRowsOutput)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL) :
    Option (CommittedSource FGL × Air.Flat.Component FGL) :=
  match output with
  | .capacityViolation => none
  | .image value => some (sourceOfImage value multiplicities ambient, physicalComponent value)

theorem sourceAndProvider_none_iff (output : FinalRowsOutput)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL) :
    sourceAndProvider output multiplicities ambient = none ↔ output = .capacityViolation := by
  cases output <;> simp [sourceAndProvider]

theorem sourceAndProvider_rejected_iff (rows : List (ZiskRomMessage FGL))
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL) :
    sourceAndProvider (constructFromFinalRows rows) multiplicities ambient = none ↔
      physicalCapacity < rows.length := by
  rw [sourceAndProvider_none_iff, constructFromFinalRows_rejected_iff]

def sourceAndProviderOfProgram {length : Nat} (program : Program length)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL) :
    Option (CommittedSource FGL × Air.Flat.Component FGL) :=
  sourceAndProvider (constructFromFinalProgram program) multiplicities ambient

/-- Actual Main constraints derive membership in the original decoded rows;
the order-preserving constructed padding adapter retains that membership.
`adapted` is an Option computation, not a producer-realization certificate. -/
theorem actualMain_member_of_adapter {length : Nat} (program : Program length)
    (image : PhysicalImage) (adapted : programToPhysicalImage program = some image)
    (mainEnv : Environment FGL)
    (holds :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).operations.ConstraintsHold
        mainEnv) :
    (romStaticTable physicalCapacity image).Spec
      (Eval.eval mainEnv (ZiskFv.AirsClean.Main.romMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar)) := by
  have member := ZiskFv.AirsClean.Main.componentRomWiring_lookupMember
    length program mainEnv holds
  obtain ⟨index, h_entry⟩ := member
  rw [h_entry]
  exact program_member_of_adapter program image adapted index

/-- Generated source tuple equals the actual materialized provider message. -/
theorem source_tuple_eq_materialized_provider (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin physicalCapacity) (data : ProverData FGL) (raw : Array FGL) :
    let row := Eval.eval
      (Environment.fromArray
        ((imageColumns physicalCapacity_pos image).materialize index.val raw) data)
      (varFromOffset (F := FGL) RomRow 0)
    Extraction.RomSource.lookupTuple (sourceOfImage image multiplicities ambient)
        (index.val : Int) =
      [row.message.line, row.message.a_offset_imm0, row.message.a_imm1,
        row.message.b_offset_imm0, row.message.b_imm1, row.message.ind_width,
        row.message.op, row.message.store_offset, row.message.jmp_offset1,
        row.message.jmp_offset2, row.message.flags] := by
  dsimp only
  rw [eval_materialize]
  exact lookupTuple_sourceOfImage image multiplicities ambient index

theorem source_multiplicity_eq_materialized_provider (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin physicalCapacity) (data : ProverData FGL) :
    Extraction.RomSource.multiplicity (sourceOfImage image multiplicities ambient)
        (index.val : Int) =
      (((ZiskRomBusChannel.emitted
        (varFromOffset (F := FGL) RomRow 0).multiplicity
        (varFromOffset (F := FGL) RomRow 0).message).toRaw).eval
          (Environment.fromArray
            ((imageColumns physicalCapacity_pos image).materialize index.val
              #[multiplicities index]) data)).mult := by
  rw [multiplicity_sourceOfImage, materialized_multiplicity]
  simp


/-- Independent provider compression; not generated from the debug hint. -/
def compressInstruction (message : ZiskRomMessage FGL) (alpha gamma : FGL) : FGL :=
  let packed := message.flags * alpha + message.jmp_offset2
  let packed := packed * alpha + message.jmp_offset1
  let packed := packed * alpha + message.store_offset
  let packed := packed * alpha + message.op
  let packed := packed * alpha + message.ind_width
  let packed := packed * alpha + message.b_imm1
  let packed := packed * alpha + message.b_offset_imm0
  let packed := packed * alpha + message.a_imm1
  let packed := packed * alpha + message.a_offset_imm0
  let packed := packed * alpha + message.line
  packed * alpha + 7890 + gamma

/-- Actual c0 versus the independently specified provider tuple and weight.
This identity is not a proof of global logUp soundness. -/
theorem polynomial_0_sourceOfImage (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL)
    (index : Fin physicalCapacity) :
    Extraction.RomSource.polynomial_0 (sourceOfImage image multiplicities ambient)
        (index.val : Int) =
      (ambient.witness 2 0 (index.val : Int) 0 -
        ambient.witness 2 0 (index.val : Int) (-1) *
          (1 - ambient.fixed 0 (index.val : Int) 0)) *
        compressInstruction (image index) (ambient.challenge 2 0)
          (ambient.challenge 2 1) - multiplicities index := by
  simp [Extraction.RomSource.polynomial_0, sourceOfImage, imageValues,
    compressInstruction] <;> ring

theorem polynomial_1_sourceOfImage (image : PhysicalImage)
    (multiplicities : Fin physicalCapacity → FGL) (ambient : CommittedSource FGL)
    (row : Int) :
    Extraction.RomSource.polynomial_1 (sourceOfImage image multiplicities ambient) row =
      ambient.fixed 0 row 1 *
        (ambient.airGroupValue 0 - ambient.witness 2 0 row 0) := by
  simp [Extraction.RomSource.polynomial_1, sourceOfImage]

theorem source_physical_capacity : Extraction.RomSource.numRows = 2^22 := by rfl

/-- Shared PublicIO cells 0..3 authenticate commitment 0 externally. Metadata
alone does not prove that a caller-chosen image opens those public values. -/
theorem source_commitment_layout :
    Extraction.RomSource.commitments = [(0, [11], [0, 1, 2, 3])] := by rfl

/-- Independently pin source constraint domains and lookup schema, as well as
the numerical polynomial identities above. This prevents a kind/count-only
production change from passing merely because a polynomial body is unchanged. -/
theorem source_lookup_schema :
    Extraction.RomSource.constraintDomains = ["every_row", "every_row"] ∧
      Extraction.RomSource.piop = "Lookup" ∧
      Extraction.RomSource.slotNames =
        ["line", "a_offset_imm0", "a_imm1", "b_offset_imm0", "b_imm1", "ind_width",
          "op", "store_offset", "jmp_offset1", "jmp_offset2", "flags"] := by
  exact ⟨rfl, rfl, rfl⟩

end ZiskFv.AirsClean.ZiskInstructionRomSource
