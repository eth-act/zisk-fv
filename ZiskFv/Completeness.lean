import ZiskFv.Completeness.Rv64im.SailDecode

/-!
# Root completeness — three honest endpoints

The completeness goal — "every Sail-executable RV64IM raw word, outside the
known decode gaps, is covered by the production ZisK decode/lower/row/opcode
pipeline" — is split here into the two halves that have genuinely different
status, plus their composition:

* `sail_executable_within_supported_decode_shape` — **PROVEN, unconditional.** A
  Sail-only containment fact: every RV64IM-class word Sail's decoder accepts lands
  in the hand-written `SupportedDecodeShape` enumeration. Says nothing about ZisK.
* `eventual_supported_shape_coverage` — **CONDITIONAL.** The ZisK half: given the
  production-coverage obligations (decoder accepts → lowering → row → opcode,
  plus the soundness-row contract) over `SupportedDecodeShape`, in-domain words
  clear the pipeline. These obligations are proved only in the separate Aeneas
  extraction workspace; here they are hypotheses.
* `eventual_root_completeness` — **CONDITIONAL on the ZisK obligations only.**
  The end-to-end statement, composing the proven Sail half with the ZisK half.
  Named `eventual_` because it stays conditional until the Aeneas coverage
  proofs can be imported into this build; at that point it becomes unconditional.

The older single `root_completeness` is gone: it hid the fact that the Sail half
is actually proven (it took the Sail bridge as a free premise). This split makes
the state legible — one endpoint is green, two wear their conditionality openly.

The abstract `Rv.Interface`-parametrized completeness route under
`ZiskFv/Completeness/Aspirational/` is the intended
*eventual* composition machinery; it is quarantined and not used by any endpoint
here. See `ZiskFv/Completeness/Aspirational/README.md`.
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
`eventual_root_completeness`, nothing more. -/
theorem sail_executable_within_supported_decode_shape :
    ∀ state raw, Rv64imEnabledSailState state →
      SailRv64imExecutableRawIn state raw → SupportedDecodeShape raw :=
  sail_rv64im_executable_contained_in_supported_decode_in

/-- **CONDITIONAL.** The ZisK half of completeness: given the production-ZisK
coverage obligations over `SupportedDecodeShape` — the decoder accepts in-domain
words outside the known gaps, lowering/row/opcode are total along the pipeline,
and the soundness-row contract holds — every in-domain raw word outside the
known decode gaps clears the pipeline and carries the soundness contract.

The obligations are hypotheses here; they are discharged (for the real extracted
decoder) only in the separate Aeneas workspace, which this build cannot import. -/
theorem eventual_supported_shape_coverage
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
    ∀ raw, SupportedDecodeShape raw → ¬ knownDecodeGap raw →
      (ziskDecoderAccepts raw ∧ ziskLoweringSucceeds raw ∧
        ziskRowMaterializes raw ∧ ziskOpcodeProven raw) ∧
      ziskRowSoundnessContract raw := by
  intro raw h_shape h_not_gap
  have h_decode := h_decoder_accepts_outside_gaps raw h_shape h_not_gap
  have h_lower := h_lowering_total raw h_decode
  exact
    ⟨⟨h_decode,
        h_lower,
        h_row_materialization_total raw h_lower,
        h_opcode_coverage_total raw h_decode⟩,
      h_soundness_contract raw h_shape h_lower⟩

/-- **CONDITIONAL on the ZisK obligations only.** End-to-end completeness:
composing the proven Sail half (`sail_executable_within_supported_decode_shape`) with the ZisK half
(`eventual_supported_shape_coverage`), every Sail-executable RV64IM raw word, outside the
known decode gaps, clears the production pipeline and carries the soundness
contract. The Sail bridge is discharged; the only open premises are the ZisK
coverage obligations. When the Aeneas coverage proofs reach this build, this
becomes unconditional. -/
theorem eventual_root_completeness
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
  exact eventual_supported_shape_coverage
    ziskDecoderAccepts ziskLoweringSucceeds ziskRowMaterializes ziskOpcodeProven
    ziskRowSoundnessContract knownDecodeGap
    h_decoder_accepts_outside_gaps h_lowering_total h_row_materialization_total
    h_opcode_coverage_total h_soundness_contract
    raw (sail_executable_within_supported_decode_shape state raw h_state h_sail) h_not_gap

end ZiskFv.Completeness
