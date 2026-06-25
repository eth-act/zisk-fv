import ZiskFv.Completeness.Rv64im.SailDecode

/-!
# Completeness endpoints

Two theorems, with genuinely different status:

* `sail_executable_within_supported_decode_shape` — **PROVEN, unconditional.** A
  Sail-only containment fact: every RV64IM-class word Sail's decoder accepts lands
  in the hand-written `SupportedDecodeShape` enumeration. Says nothing about ZisK.
* `root_completeness` — **CONDITIONAL on the ZisK coverage obligations.** The
  end-to-end acceptance/coverage statement: every Sail-executable RV64IM raw word,
  outside the known decode gaps, clears the production ZisK pipeline and carries
  the soundness-row contract — *given* the per-stage coverage obligations as
  hypotheses. Those obligations are discharged only in the separate Aeneas
  workspace this build cannot import, so it stays conditional until that bridge
  lands.

The abstract `Rv.Interface`-parametrized route under
`ZiskFv/Completeness/Aspirational/` is the intended *eventual* composition
machinery; it is quarantined and not used by either endpoint here. See
`ZiskFv/Completeness/Aspirational/README.md`.
-/

namespace ZiskFv.Completeness

open ZiskFv.Completeness.Rv64imShapes (SupportedDecodeShape)
open ZiskFv.Completeness.SailDecode

/-- **PROVEN (unconditional), Sail-side only.** For an RV64IM-enabled state, every
raw word that round-trips through Sail's real decoder/encoder to one of the eleven
enumerated RV64IM instruction classes has a bit-layout in `SupportedDecodeShape`.

Discharged by evaluating the generated Sail `ext_decode` / `encdec_forwards`, so
the containment is genuine. But note the scope:
* It says **nothing about ZisK** — `SupportedDecodeShape` is a hand-written
  bit-pattern predicate (`Rv64im/Shapes.lean`), not ZisK's decoder. Whether it
  matches ZisK's actual supported set is a separate, unproven claim.
* The domain is self-gated: it only quantifies over words Sail decodes to an
  instruction we already enumerate as RV64IM, in canonical (decode∘encode) form.

This is the Sail→shape coverage bridge — the domain premise consumed by
`root_completeness`, nothing more. -/
theorem sail_executable_within_supported_decode_shape :
    ∀ state raw, Rv64imEnabledSailState state →
      SailRv64imExecutableRawIn state raw → SupportedDecodeShape raw :=
  sail_rv64im_executable_contained_in_supported_decode_in

/-- **CONDITIONAL on the ZisK coverage obligations.** End-to-end RV64IM
acceptance completeness: for an RV64IM-enabled state, every Sail-executable raw
word outside the known decode gaps satisfies the production-ZisK pipeline —
the decoder accepts it, lowering and row materialization and opcode coverage all
succeed, and the soundness-row contract holds.

The Sail half is discharged inline (`sail_executable_within_supported_decode_shape`
turns Sail-executability into `SupportedDecodeShape` membership); the per-stage
ZisK obligations are taken as hypotheses here. They are proved for the real
extracted decoder only in the separate Aeneas workspace this build cannot import,
so this theorem stays conditional on them until that bridge lands. It is an
acceptance/coverage claim — it does NOT assert ZisK executes instructions
correctly (that is the soundness axis). -/
theorem root_completeness
    (state : SailState) (h_state : Rv64imEnabledSailState state)
    (ziskDecoderAccepts ziskLoweringSucceeds : BitVec 32 → Prop)
    (ziskRowMaterializes ziskOpcodeProven : BitVec 32 → Prop)
    (ziskRowSoundnessContract knownDecodeGap : BitVec 32 → Prop)
    (h_decoder_accepts_outside_gaps :
      ∀ raw, SupportedDecodeShape raw → ¬ knownDecodeGap raw → ziskDecoderAccepts raw)
    (h_lowering_total :
      ∀ raw, ziskDecoderAccepts raw → ziskLoweringSucceeds raw)
    (h_row_materialization_total :
      ∀ raw, ziskLoweringSucceeds raw → ziskRowMaterializes raw)
    (h_opcode_coverage_total :
      ∀ raw, ziskDecoderAccepts raw → ziskOpcodeProven raw)
    (h_soundness_contract :
      ∀ raw, SupportedDecodeShape raw → ziskLoweringSucceeds raw →
        ziskRowSoundnessContract raw) :
    ∀ raw, SailRv64imExecutableRawIn state raw → ¬ knownDecodeGap raw →
      (ziskDecoderAccepts raw ∧ ziskLoweringSucceeds raw ∧
        ziskRowMaterializes raw ∧ ziskOpcodeProven raw) ∧
      ziskRowSoundnessContract raw := by
  intro raw h_sail h_not_gap
  have h_shape :=
    sail_executable_within_supported_decode_shape state raw h_state h_sail
  have h_decode := h_decoder_accepts_outside_gaps raw h_shape h_not_gap
  have h_lower := h_lowering_total raw h_decode
  exact
    ⟨⟨h_decode,
        h_lower,
        h_row_materialization_total raw h_lower,
        h_opcode_coverage_total raw h_decode⟩,
      h_soundness_contract raw h_shape h_lower⟩

end ZiskFv.Completeness
