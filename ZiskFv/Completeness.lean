import ZiskFv.Completeness.Rv64im.SailDecode

/-!
# Completeness endpoints

The RV64IM acceptance/completeness surface, as two theorems with different status.

* `sail_executable_within_supported_decode_shape` — PROVEN, unconditional. A
  Sail-only fact: every word Sail decodes to an RV64IM instruction has a
  bit-layout in the `SupportedDecodeShape` enumeration. Mentions no ZisK.
* `root_completeness` — CONDITIONAL. The end-to-end acceptance claim, stated over
  abstract ZisK-pipeline predicates the caller (the Aeneas extraction harness)
  must supply. This build cannot import that harness, so the predicates stay
  abstract and the theorem stays conditional on them.

Both are *acceptance/coverage* claims (ZisK does not reject what Sail accepts),
NOT correctness claims (that ZisK matches Sail when it runs) — correctness is the
soundness axis (`ZiskFv.Compliance`).

The abstract `Rv.Interface`-parametrized route under
`ZiskFv/Completeness/Aspirational/` is quarantined and unused by either endpoint
here; see that directory's `README.md`.
-/

namespace ZiskFv.Completeness

open ZiskFv.Completeness.Rv64imShapes (SupportedDecodeShape)
open ZiskFv.Completeness.SailDecode

/-- The Sail-side containment bridge (PROVEN, unconditional).

Every Sail-executable RV64IM word has a bit-layout inside the
`SupportedDecodeShape` enumeration. Proven by evaluating the real generated Sail
decoder/encoder (`LeanRV64D.Functions.ext_decode` / `encdec_forwards`).

Universally quantified over:
* `state` — a Sail machine state. The Sail decoder consults extension state, so
  the claim is made relative to a fixed `state`.
* `raw` — the 32-bit instruction word under consideration.

Premises (the antecedents of the inner implications):
* `Rv64imEnabledSailState state` — `state` is configured for RV64IM: the `M`
  extension is enabled and `Zmmul` is disabled.
* `SailRv64imExecutableRawIn state raw` — `raw` round-trips through Sail in
  `state`: it decodes to some instruction that re-encodes back to `raw`, and that
  instruction is one of the eleven enumerated RV64IM classes.

Conclusion `SupportedDecodeShape raw` — `raw`'s bit-layout matches one of the
seven structural shape families.

Scope caveats: `SupportedDecodeShape` is a hand-written predicate
(`Rv64im/Shapes.lean`), NOT ZisK's decoder — this proves nothing about ZisK; and
the domain is self-gated, ranging only over words that already decode to an
enumerated RV64IM instruction in canonical form. -/
theorem sail_executable_within_supported_decode_shape :
    ∀ state raw, Rv64imEnabledSailState state →
      SailRv64imExecutableRawIn state raw → SupportedDecodeShape raw :=
  sail_rv64im_executable_contained_in_supported_decode_in

/-- End-to-end RV64IM acceptance completeness (CONDITIONAL on the ZisK coverage
obligations).

For a fixed RV64IM-enabled Sail state, every Sail-executable raw word that is not
a known decode gap is shown to clear ZisK's production pipeline (decode → lower →
row → opcode) and to carry the soundness-row contract — *given* the per-stage
coverage obligations below as hypotheses. The Sail half is discharged inline via
`sail_executable_within_supported_decode_shape`.

This is an *acceptance* claim (ZisK accepts and processes the word), NOT a
correctness claim (correctness is the soundness axis). The ZisK predicates are
abstract and supplied by the caller — concretely the Aeneas extraction harness,
which this build cannot import, so the theorem stays conditional.

State parameters:
* `state` — the Sail machine state decoding is evaluated against.
* `h_state` — evidence `state` is RV64IM-configured (`M` enabled, `Zmmul`
  disabled).

ZisK-side predicates (abstract; each a property of a 32-bit raw word, to be
instantiated by the harness):
* `ziskDecoderAccepts` — ZisK's production decoder supports the word.
* `ziskLoweringSucceeds` — lowering assigns the word an internal ZisK opcode.
* `ziskRowMaterializes` — ZisK builds a circuit row for the word. (NB: in the
  current harness this is defined as merely "decoder accepted", not a satisfying
  row — the name is stronger than what backs it.)
* `ziskOpcodeProven` — the word's opcode is in the set proven sound per-opcode.
* `ziskRowSoundnessContract` — the static per-row input the soundness theorems
  consume holds for the word.
* `knownDecodeGap` — the explicitly recorded decode carve-outs (e.g. the FENCE
  subset ZisK rejects); such words are excluded from the conclusion.

Coverage obligations (the conditional content — discharged elsewhere, not here):
* `h_decoder_accepts_outside_gaps` — every in-shape word that is not a known gap
  is accepted by the decoder.
* `h_lowering_total` — every accepted word lowers.
* `h_row_materialization_total` — every lowered word materializes a row.
* `h_opcode_coverage_total` — every accepted word lands in the proven-opcode set.
* `h_soundness_contract` — every in-shape, lowered word satisfies the
  soundness-row contract.

Conclusion: for every `raw` that is Sail-executable in `state` and not a known
decode gap, ZisK accepts it, lowers it, materializes a row, its opcode is proven,
and the soundness-row contract holds. -/
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
