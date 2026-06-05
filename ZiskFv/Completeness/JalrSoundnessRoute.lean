import ZiskFv.Completeness.SailDecode

/-!
# JALR completeness route to soundness

This checked-in module records the architecture of the JALR completeness slice
without importing the Aeneas-generated production extractor. The generated
workspace exercises concrete lowered JALR rows and the extracted shared JALR
mask constant required by the existing JALR soundness path.
-/

namespace ZiskFv.Completeness.JalrSoundnessRoute

open ZiskFv.Completeness
open ZiskFv.Completeness.SailDecode

abbrev RawInstruction := Rv.RawInstruction

/-- Abstract production-ZisK side of the JALR route. In the generated Aeneas
workspace this route is backed by `extract_transpile_rv64im_raw` row checks and
the extracted shared JALR mask constant. -/
structure Interface where
  ziskJalrSoundnessRoute : RawInstruction → Prop

namespace Interface

/-- Sail accepts the raw word as a JALR instruction, with the encode bridge
making the raw I-type fields available to the checked-in shape theorem. -/
def SailJalrExecutableIn
    (state : SailState) (raw : RawInstruction) : Prop :=
  ∃ imm rs1 rd,
    SailDecodesToIn state raw (instruction.JALR (imm, rs1, rd)) ∧
    SailEncodesToIn state (instruction.JALR (imm, rs1, rd)) raw

/-- Generated production route obligation for all raw words in JALR's full
I-format decode surface. This is a ZisK-side implementation lemma, not the
source of truth for instruction validity. -/
def ShapeRouteComplete
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.ziskJalrSoundnessRoute raw

/-- Sail-to-ZisK JALR route completeness before adding the RV64IM state
assumption. Sail remains the source of valid raw JALR words; the raw I-shape
formula is derived below only to connect into generated ZisK coverage. -/
def SailRouteComplete (iface : Interface) : Prop :=
  ∀ state raw,
    SailJalrExecutableIn state raw →
    iface.ziskJalrSoundnessRoute raw

/-- Sail-to-ZisK JALR route completeness. This is the narrow theorem shape:
Sail is the source of valid JALR raw words, and ZisK must expose the static row
contract required by the existing JALR soundness theorem. -/
def Complete (iface : Interface) : Prop :=
  ∀ state raw,
    Rv64imEnabledSailState state →
    SailJalrExecutableIn state raw →
    iface.ziskJalrSoundnessRoute raw

/-- The raw I-format JALR shape is recovered from the Sail encode/decode
relation. This keeps the public route theorem Sail-first while still reusing
the existing generated ZisK shape coverage. -/
theorem sail_jalr_executable_in_contained_in_shape
    {state : SailState} {raw : RawInstruction}
    (h_sail : SailJalrExecutableIn state raw) :
    Rv64imShapes.JalrRegisterImmediateShape raw := by
  rcases h_sail with ⟨imm, rs1, rd, _h_decode, h_encode⟩
  exact
    sail_encode_rawIType_contained_in_jalr_shape_in
      h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_jalr_eq_rawIType imm rs1 rd) state)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt

theorem sail_route_complete_of_jalr_shape_route
    (iface : Interface)
    (h_route :
      ShapeRouteComplete iface Rv64imShapes.JalrRegisterImmediateShape) :
    SailRouteComplete iface := by
  intro _state raw h_sail
  have h_shape : Rv64imShapes.JalrRegisterImmediateShape raw :=
    sail_jalr_executable_in_contained_in_shape h_sail
  exact h_route raw h_shape

theorem complete_of_sail_route
    (iface : Interface)
    (h_route : SailRouteComplete iface) :
    Complete iface := by
  intro state raw _h_rv64im h_sail
  exact h_route state raw h_sail

theorem complete_of_jalr_shape_route
    (iface : Interface)
    (h_route :
      ShapeRouteComplete iface Rv64imShapes.JalrRegisterImmediateShape) :
    Complete iface :=
  complete_of_sail_route iface
    (sail_route_complete_of_jalr_shape_route iface h_route)

end Interface

end ZiskFv.Completeness.JalrSoundnessRoute
