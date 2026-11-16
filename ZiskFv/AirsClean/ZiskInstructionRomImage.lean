import Extraction.RomSource
import ZiskFv.AirsClean.ZiskInstructionRom

/-!
# Physical committed ROM image and constructed padding examples

The compiled instance has 4194304 rows. `rom.rs:204-266` sorts ORIGINAL u64
BTreeMap keys before field encoding, copies the resulting final rows, and
zero-pads. The verifier does not enforce sorting by field representatives.
`Program` has lost the original keys: it must not be re-sorted by `line.val`.

The adapter below preserves supplied final-row order and duplicates exactly,
then constructs an explicit zero suffix. It is a constructed example, NOT a
proof of source-history last-write/key-sort realization, source provenance,
ELF lowering, or public-root image authentication. Those boundaries remain
separate. No list copy/sort is needed for the indexed Program adapter.
-/
namespace ZiskFv.AirsClean.ZiskInstructionRomImage

open Goldilocks
open ZiskFv.Channels.ZiskRomBus
open ZiskFv.AirsClean.ZiskInstructionRom

def physicalCapacity : Nat := Extraction.RomSource.numRows

theorem physicalCapacity_eq : physicalCapacity = 2^22 := by rfl

theorem physicalCapacity_pos : 0 < physicalCapacity := by
  change 0 < 4194304
  decide

abbrev PhysicalImage := Program physicalCapacity

/-- The source producer's padding is the all-zero committed tuple. -/
def paddingMessage : ZiskRomMessage FGL :=
  { line := 0, a_offset_imm0 := 0, a_imm1 := 0, b_offset_imm0 := 0,
    b_imm1 := 0, ind_width := 0, op := 0, store_offset := 0,
    jmp_offset1 := 0, jmp_offset2 := 0, flags := 0 }

/-- Preserve the supplied final rows exactly; their ordinals never become PC.
The bound is a constructor invariant, computed by the total constructor. -/
def padProgram {length : Nat} (program : Program length)
    (_bounded : length ≤ physicalCapacity) : PhysicalImage :=
  fun index => if h : index.val < length then program ⟨index.val, h⟩ else paddingMessage

@[simp] theorem padProgram_prefix {length : Nat} (program : Program length)
    (bounded : length ≤ physicalCapacity) (index : Fin length) :
    padProgram program bounded ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩ = program index := by
  simp [padProgram, index.isLt]

@[simp] theorem padProgram_suffix {length : Nat} (program : Program length)
    (bounded : length ≤ physicalCapacity) (index : Fin physicalCapacity)
    (padding : length ≤ index.val) :
    padProgram program bounded index = paddingMessage := by
  simp [padProgram, Nat.not_lt.mpr padding]

/-- Failure is not a zero image and supplies no source/provider. -/
inductive FinalRowsOutput where
  | capacityViolation
  | image (value : PhysicalImage)

def constructFromFinalProgram {length : Nat} (program : Program length) : FinalRowsOutput :=
  if bounded : length ≤ physicalCapacity then .image (padProgram program bounded)
  else .capacityViolation

/-- Source storage copying, AFTER last-write resolution and original-key sort.
This function neither establishes nor repeats those preceding operations. -/
def constructFromFinalRows (rows : List (ZiskRomMessage FGL)) : FinalRowsOutput :=
  constructFromFinalProgram (fun index : Fin rows.length => rows[index.val])

def FinalRowsOutput.image? : FinalRowsOutput → Option PhysicalImage
  | .capacityViolation => none
  | .image value => some value

theorem finalProgram_image_eq {length : Nat} (program : Program length) :
    (constructFromFinalProgram program).image? =
      if bounded : length ≤ physicalCapacity then some (padProgram program bounded) else none := by
  unfold constructFromFinalProgram
  split <;> rfl

@[simp] theorem constructFromFinalProgram_rejected_iff {length : Nat} (program : Program length) :
    constructFromFinalProgram program = .capacityViolation ↔ physicalCapacity < length := by
  unfold constructFromFinalProgram
  split <;> simp_all

/-- Only source capacity is checked here. No invented sorting/collision gate. -/
@[simp] theorem constructFromFinalRows_rejected_iff (rows : List (ZiskRomMessage FGL)) :
    constructFromFinalRows rows = .capacityViolation ↔ physicalCapacity < rows.length := by
  simp [constructFromFinalRows]

/-- Constructed padding example for the old decoded Program type. -/
def programToPhysicalImage {length : Nat} (program : Program length) : Option PhysicalImage :=
  (constructFromFinalProgram program).image?

@[simp] theorem programToPhysicalImage_failure {length : Nat} (program : Program length) :
    programToPhysicalImage program = none ↔ physicalCapacity < length := by
  rw [programToPhysicalImage, finalProgram_image_eq]
  split <;> simp_all

/-- Every provided row survives at the SAME ordinal, retaining its original PC,
all message fields and duplicates. This is not source-history realization. -/
theorem adapter_prefix {length : Nat} (program : Program length)
    (image : PhysicalImage) (accepted : programToPhysicalImage program = some image)
    (index : Fin length) :
    ∃ bounded : length ≤ physicalCapacity,
      image ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩ = program index := by
  unfold programToPhysicalImage at accepted
  rw [finalProgram_image_eq] at accepted
  split at accepted
  next bounded =>
    cases Option.some.inj accepted
    exact ⟨bounded, padProgram_prefix program bounded index⟩
  next => simp at accepted

theorem program_member_of_adapter {length : Nat} (program : Program length)
    (image : PhysicalImage) (accepted : programToPhysicalImage program = some image)
    (index : Fin length) : (romStaticTable physicalCapacity image).Spec (program index) := by
  obtain ⟨bounded, preserved⟩ := adapter_prefix program image accepted index
  exact ⟨⟨index.val, lt_of_lt_of_le index.isLt bounded⟩, preserved.symm⟩

/-- Exact membership: original rows, or zero padding when a suffix exists. -/
theorem padProgram_member_iff {length : Nat} (program : Program length)
    (bounded : length ≤ physicalCapacity) (message : ZiskRomMessage FGL) :
    (romStaticTable physicalCapacity (padProgram program bounded)).Spec message ↔
      (romStaticTable length program).Spec message ∨
        (length < physicalCapacity ∧ message = paddingMessage) := by
  constructor
  · rintro ⟨index, rfl⟩
    by_cases is_prefix : index.val < length
    · left
      exact ⟨⟨index.val, is_prefix⟩, by simp [padProgram, is_prefix]⟩
    · right
      exact ⟨lt_of_le_of_lt (Nat.le_of_not_gt is_prefix) index.isLt,
        by simp [padProgram, is_prefix]⟩
  · rintro (⟨index, rfl⟩ | ⟨unused, rfl⟩)
    · exact ⟨⟨index.val, lt_of_lt_of_le index.isLt bounded⟩,
        (padProgram_prefix program bounded index).symm⟩
    · exact ⟨⟨length, unused⟩, by simp [padProgram]⟩

theorem adapter_member_iff {length : Nat} (program : Program length)
    (image : PhysicalImage) (accepted : programToPhysicalImage program = some image)
    (message : ZiskRomMessage FGL) :
    (romStaticTable physicalCapacity image).Spec message ↔
      (romStaticTable length program).Spec message ∨
        (length < physicalCapacity ∧ message = paddingMessage) := by
  unfold programToPhysicalImage at accepted
  rw [finalProgram_image_eq] at accepted
  split at accepted
  next bounded =>
    cases Option.some.inj accepted
    exact padProgram_member_iff program bounded message
  next => simp at accepted

/-- Signed rotations wrap only in the actual compiled physical domain. -/
def physicalIndex (row rotation : Int) : Fin physicalCapacity :=
  ⟨((row + rotation) % (physicalCapacity : Int)).toNat % physicalCapacity,
    Nat.mod_lt _ physicalCapacity_pos⟩

@[simp] theorem physicalIndex_current (index : Fin physicalCapacity) :
    physicalIndex (index.val : Int) 0 = index := by
  apply Fin.ext
  simp [physicalIndex, ← Int.natCast_mod, Nat.mod_eq_of_lt index.isLt]

theorem physicalIndex_predecessor_zero :
    (physicalIndex 0 (-1)).val = physicalCapacity - 1 := by rfl

theorem physicalIndex_successor_last :
    (physicalIndex ((physicalCapacity - 1 : Nat) : Int) 1).val = 0 := by rfl

theorem physicalIndex_zero : (physicalIndex 0 0).val = 0 := by rfl

/-- Counterexample to treating every old Program as a successful source image. -/
def oversizedProgram : Program (physicalCapacity + 1) :=
  fun index => { paddingMessage with line := (index.val : FGL), flags := 1 }

theorem oversizedProgram_distinct_addresses :
    Function.Injective (fun index => (oversizedProgram index).line) := by
  intro left right same
  have left_small : left.val < GL_prime := by
    have bound := left.isLt
    change left.val < 4194305 at bound
    omega
  have right_small : right.val < GL_prime := by
    have bound := right.isLt
    change right.val < 4194305 at bound
    omega
  apply Fin.ext
  have values := congrArg Fin.val same
  simpa only [oversizedProgram, Fin.val_natCast,
    Nat.mod_eq_of_lt left_small, Nat.mod_eq_of_lt right_small] using values

theorem oversizedProgram_rejected : programToPhysicalImage oversizedProgram = none :=
  (programToPhysicalImage_failure oversizedProgram).mpr (Nat.lt_succ_self _)

theorem oversizedProgram_abstract_member :
    (romStaticTable (physicalCapacity + 1) oversizedProgram).Spec
      (oversizedProgram ⟨0, Nat.zero_lt_succ _⟩) := by
  exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩

end ZiskFv.AirsClean.ZiskInstructionRomImage
