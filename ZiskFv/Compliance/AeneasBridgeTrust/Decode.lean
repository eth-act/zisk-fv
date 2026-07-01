/-
ZiskFv/Compliance/AeneasBridgeTrust/Decode.lean  (eth-act/zisk-fv#162)

Top-level decode-acceptance theorem: the REAL extracted RV64IM decoder
(`aeneas_extract.extract_rv64im_opcode_supported`, `trust/aeneas/ProductionM2.lean`)
accepts every raw 32-bit word in `SupportedDecodeShape`, and this discharges the
completeness obligation `OutstandingZiskPredicates.decoderAcceptsInShape`
(`ZiskFv/Completeness.lean`).

Kernel-sound: NO `native_decide` / `bv_decide` / `sorry`. The closure of
`zisk_decoder_accepts_supported_shape` is `[propext, Classical.choice, Quot.sound]`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Classify
import ZiskFv.Completeness

open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Completeness ZiskFv.Completeness.Rv64imShapes

namespace ZiskFv.Compliance.Decode

/-- The real ZisK decoder *accepts* `raw`: the extracted RV64IM opcode-support
check (`extract_rv64im_opcode_supported`, applied to the raw word) returns
`ok true`. This is the concrete witness for the abstract
`OutstandingZiskPredicates.decoderAccepts` placeholder. -/
def ziskDecoderAccepts (raw : BitVec 32) : Prop :=
  aeneas_extract.extract_rv64im_opcode_supported (toU32 raw) = ok true

/-- **Headline (eth-act/zisk-fv#162).** Every raw word matching the supported RV64IM
decode shape is accepted by ZisK's real extracted decoder. Stronger than the
completeness obligation: holds with NO `knownDecodeGap` exclusion, because
`SupportedDecodeShape`'s FENCE family is already restricted to the supported subset. -/
theorem zisk_decoder_accepts_supported_shape (raw : BitVec 32)
    (h : SupportedDecodeShape raw) : ziskDecoderAccepts raw := by
  unfold ziskDecoderAccepts
  rcases h with hR | hI | hSh | hS | hB | hUJ | hF
  · obtain ⟨f7, f3, opc, rd, rs1, rs2, hmem, hrd, hrs1, hrs2, rfl⟩ := hR
    exact rtype_family_accepts f7 f3 opc rd rs1 rs2 hmem
      (List.mem_range.mp hrd) (List.mem_range.mp hrs1) (List.mem_range.mp hrs2)
  · obtain ⟨rd, rs1, imm, f3, opc, hrd, hrs1, himm, hmem, rfl⟩ := hI
    exact itype_family_accepts rd rs1 imm f3 opc
      (List.mem_range.mp hrd) (List.mem_range.mp hrs1) himm hmem
  · rcases hSh with hSh64 | hSh32
    · obtain ⟨rd, rs1, shamt, f3, upper, hrd, hrs1, hsh, hfu, rfl⟩ := hSh64
      exact shift64_family_accepts rd rs1 shamt f3 upper
        (List.mem_range.mp hrd) (List.mem_range.mp hrs1) (List.mem_range.mp hsh) hfu
    · obtain ⟨rd, rs1, shamt, f3, upper, hrd, hrs1, hsh, hfu, rfl⟩ := hSh32
      exact shift32_family_accepts rd rs1 shamt f3 upper
        (List.mem_range.mp hrd) (List.mem_range.mp hrs1) (List.mem_range.mp hsh) hfu
  · obtain ⟨rs1, rs2, imm, f3, hrs1, hrs2, himm, hmem, rfl⟩ := hS
    exact stype_family_accepts rs1 rs2 imm f3
      (List.mem_range.mp hrs1) (List.mem_range.mp hrs2) himm hmem
  · obtain ⟨rs1, rs2, imm, f3, hrs1, hrs2, himm, _halign, hmem, rfl⟩ := hB
    exact btype_family_accepts rs1 rs2 imm f3
      (List.mem_range.mp hrs1) (List.mem_range.mp hrs2) himm hmem
  · rcases hUJ with hU | hJ
    · obtain ⟨rd, imm, opc, hrd, _himm, _halign, hmem, rfl⟩ := hU
      exact utype_family_accepts rd imm opc (List.mem_range.mp hrd) hmem
    · obtain ⟨rd, imm, hrd, _himm, _halign, rfl⟩ := hJ
      exact jtype_family_accepts rd imm
  · obtain ⟨pred, succ, hp, hs, rfl⟩ := hF
    exact fence_family_accepts pred succ (List.mem_range.mp hp) (List.mem_range.mp hs)

/-- The real decoder discharges the completeness obligation
`OutstandingZiskPredicates.decoderAcceptsInShape` for any `z` whose abstract
`decoderAccepts` placeholder is instantiated with the real `ziskDecoderAccepts`.
(The `knownDecodeGap` premise is not even needed.) -/
theorem real_decoder_accepts_in_shape (z : OutstandingZiskPredicates)
    (hz : z.decoderAccepts = ziskDecoderAccepts) :
    z.decoderAcceptsInShape := by
  intro raw hshape _
  rw [hz]
  exact zisk_decoder_accepts_supported_shape raw hshape

/-- **Classification headline (eth-act/zisk-fv#162).** Every raw word matching the
supported RV64IM decode shape is *classified* by ZisK's real extracted decoder: the
core decoder `decode_32_core` returns a decoded record `d`, and `d.opcode` is a
genuine supported RV64IM opcode (`is_supported_rv64im d = ok true`).  Strictly
stronger than `zisk_decoder_accepts_supported_shape`, which only states the
opcode-support check returns `ok true` without exposing the decoded record.

The *specific* opcode per shape is pinned by the per-family `*_classifies` lemmas in
`Decode/Classify.lean` (e.g. `rtypeOpcode`/`itypeOpcode`/…); those, composed with the
Sail-executable→`SupportedDecodeShape` containment in
`ZiskFv/Completeness/Rv64im/SailDecode`, are the bytes→opcode step matching the Sail
spec decode.  Kernel-sound: `[propext, Classical.choice, Quot.sound]`. -/
theorem zisk_decoder_classifies_supported_shape (raw : BitVec 32)
    (h : SupportedDecodeShape raw) :
    ∃ d, aeneas_extract.rv64im_decode.decode_32_core (toU32 raw) = ok d ∧
         aeneas_extract.rv64im_decode.DecodedRv64im.is_supported_rv64im d = ok true := by
  -- Step 1: expose the decoded record via the per-family classification lemmas.
  have hrec : ∃ d, aeneas_extract.rv64im_decode.decode_32_core (toU32 raw) = ok d := by
    rcases h with hR | hI | hSh | hS | hB | hUJ | hF
    · obtain ⟨f7, f3, opc, rd, rs1, rs2, hmem, hrd, hrs1, hrs2, rfl⟩ := hR
      obtain ⟨d, hd, _⟩ := rtype_family_classifies f7 f3 opc rd rs1 rs2 hmem
        (List.mem_range.mp hrd) (List.mem_range.mp hrs1) (List.mem_range.mp hrs2)
      exact ⟨d, hd⟩
    · obtain ⟨rd, rs1, imm, f3, opc, hrd, hrs1, himm, hmem, rfl⟩ := hI
      obtain ⟨d, hd, _⟩ := itype_family_classifies rd rs1 imm f3 opc
        (List.mem_range.mp hrd) (List.mem_range.mp hrs1) himm hmem
      exact ⟨d, hd⟩
    · rcases hSh with hSh64 | hSh32
      · obtain ⟨rd, rs1, shamt, f3, upper, hrd, hrs1, hsh, hfu, rfl⟩ := hSh64
        obtain ⟨d, hd, _⟩ := shift64_family_classifies rd rs1 shamt f3 upper
          (List.mem_range.mp hrd) (List.mem_range.mp hrs1) (List.mem_range.mp hsh) hfu
        exact ⟨d, hd⟩
      · obtain ⟨rd, rs1, shamt, f3, upper, hrd, hrs1, hsh, hfu, rfl⟩ := hSh32
        obtain ⟨d, hd, _⟩ := shift32_family_classifies rd rs1 shamt f3 upper
          (List.mem_range.mp hrd) (List.mem_range.mp hrs1) (List.mem_range.mp hsh) hfu
        exact ⟨d, hd⟩
    · obtain ⟨rs1, rs2, imm, f3, hrs1, hrs2, himm, hmem, rfl⟩ := hS
      obtain ⟨d, hd, _⟩ := stype_family_classifies rs1 rs2 imm f3
        (List.mem_range.mp hrs1) (List.mem_range.mp hrs2) himm hmem
      exact ⟨d, hd⟩
    · obtain ⟨rs1, rs2, imm, f3, hrs1, hrs2, himm, _halign, hmem, rfl⟩ := hB
      obtain ⟨d, hd, _⟩ := btype_family_classifies rs1 rs2 imm f3
        (List.mem_range.mp hrs1) (List.mem_range.mp hrs2) himm hmem
      exact ⟨d, hd⟩
    · rcases hUJ with hU | hJ
      · obtain ⟨rd, imm, opc, hrd, _himm, _halign, hmem, rfl⟩ := hU
        obtain ⟨d, hd, _⟩ := utype_family_classifies rd imm opc (List.mem_range.mp hrd) hmem
        exact ⟨d, hd⟩
      · obtain ⟨rd, imm, hrd, _himm, _halign, rfl⟩ := hJ
        obtain ⟨d, hd, _⟩ := jtype_family_classifies rd imm
        exact ⟨d, hd⟩
    · obtain ⟨pred, succ, hp, hs, rfl⟩ := hF
      obtain ⟨d, hd, _⟩ := fence_family_classifies pred succ
        (List.mem_range.mp hp) (List.mem_range.mp hs)
      exact ⟨d, hd⟩
  -- Step 2: the record is a supported opcode, from the acceptance theorem.
  obtain ⟨d, hd⟩ := hrec
  refine ⟨d, hd, ?_⟩
  have hacc := zisk_decoder_accepts_supported_shape raw h
  simp only [ziskDecoderAccepts, aeneas_extract.extract_rv64im_opcode_supported, hd,
    ] at hacc
  exact hacc

end ZiskFv.Compliance.Decode
