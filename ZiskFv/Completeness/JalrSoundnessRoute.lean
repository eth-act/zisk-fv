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
I-format decode surface. -/
def ShapeRouteComplete
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.ziskJalrSoundnessRoute raw

/-- Sail-to-ZisK JALR route completeness. This is the narrow theorem shape:
Sail is the source of valid JALR raw words, and ZisK must expose the static row
contract required by the existing JALR soundness theorem. -/
def Complete (iface : Interface) : Prop :=
  ∀ state raw,
    Rv64imEnabledSailState state →
    SailJalrExecutableIn state raw →
    iface.ziskJalrSoundnessRoute raw

theorem complete_of_jalr_shape_route
    (iface : Interface)
    (h_route :
      ShapeRouteComplete iface Rv64imShapes.JalrRegisterImmediateShape) :
    Complete iface := by
  intro state raw _h_rv64im h_sail
  rcases h_sail with ⟨imm, rs1, rd, _h_decode, h_encode⟩
  have h_shape : Rv64imShapes.JalrRegisterImmediateShape raw :=
    sail_encode_rawIType_contained_in_jalr_shape_in
      h_encode
      (sail_encodes_to_in_of_pure
        (sail_encode_jalr_eq_rawIType imm rs1 rd) state)
      (List.mem_range.mpr (regidx_to_fin rd).isLt)
      (List.mem_range.mpr (regidx_to_fin rs1).isLt)
      imm.isLt
  exact h_route raw h_shape

end Interface

end ZiskFv.Completeness.JalrSoundnessRoute
