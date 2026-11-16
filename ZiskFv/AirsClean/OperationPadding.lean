import Extraction.BinaryAdd
import Extraction.BinaryExtension
import Extraction.LookupWiring

/-!
# Local source equations for operation padding

`binary_add.pil:28` and `binary_extension.pil:123` call
`assumes_padding_operation` for their own all-zero operation. The Direct
constraint is generated at `std_sum.pil:656`. Its opcode, negative direction,
source padding-size cell and protocol accumulator are fixed independently here.

These are build-only local source welds. The physical witness builder computes
`padding_size = num_rows - total_inputs`, but the row-only Clean components do
not carry that producer metadata or emit the segment Direct adjustment.
Connecting those actual populations/emissions remains necessary before claiming
the padding live-model boundary; no arbitrary count is substituted for it.
-/

namespace ZiskFv.AirsClean.OperationPadding

open Extraction.LookupWiring

/-- The negative operation-bus Direct contribution for an all-zero payload. -/
def Equation {F : Type} [Field F] (opcode paddingSize imDirect alpha gamma : F) : Prop :=
  imDirect * ((opcode * alpha + 5000) + gamma) - (0 - paddingSize) = 0

section Source

variable {C : Type → Type → Sort u} {F : Type} [Field F]
  [Extraction.Circuit F F C] (c : C F F) (row : ℕ)

/-- BinaryAdd c7, exact OP_ADD=10, padding_size AIR value 0, im_direct value 1. -/
theorem binaryAdd_source_iff :
    BinaryAdd.extraction.constraint_7_every_row c row ↔
      Equation 10 (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.exposed c (index := 1))
        (Extraction.Circuit.challenge c (index := 0))
        (Extraction.Circuit.challenge c (index := 1)) := by
  rfl

/-- BinaryExtension c6, exact OP_SEXT_B=39 and its own source cells 0/1. -/
theorem binaryExtension_source_iff :
    BinaryExtension.extraction.constraint_6_every_row c row ↔
      Equation 39 (Extraction.Circuit.exposed c (index := 0))
        (Extraction.Circuit.exposed c (index := 1))
        (Extraction.Circuit.challenge c (index := 0))
        (Extraction.Circuit.challenge c (index := 1)) := by
  rfl

end Source

/-- Preserve all eleven operation slots, including the literal zero tail. -/
theorem binaryAdd_hint_source :
    link_BinaryAdd_7.hints = [hint_BinaryAdd_7_0] ∧
    hint_BinaryAdd_7_0.piop = "Direct" ∧
    hint_BinaryAdd_7_0.proves = false ∧
    hint_BinaryAdd_7_0.busId = .constant "5000" ∧
    hint_BinaryAdd_7_0.multiplicity = .add (.airValue 0) (.constant "0") ∧
    hint_BinaryAdd_7_0.slots.map (·.value) =
      .constant "10" :: List.replicate 10 (.constant "0") := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem binaryExtension_hint_source :
    link_BinaryExtension_6.hints = [hint_BinaryExtension_6_0] ∧
    hint_BinaryExtension_6_0.piop = "Direct" ∧
    hint_BinaryExtension_6_0.proves = false ∧
    hint_BinaryExtension_6_0.busId = .constant "5000" ∧
    hint_BinaryExtension_6_0.multiplicity = .add (.airValue 0) (.constant "0") ∧
    hint_BinaryExtension_6_0.slots.map (·.value) =
      .constant "39" :: List.replicate 10 (.constant "0") := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ZiskFv.AirsClean.OperationPadding
