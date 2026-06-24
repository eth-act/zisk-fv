import ZiskFv.Completeness.Rv64im

/-!
# Root completeness

The headline completeness statement of the project, parallel to
`ZiskFv.Soundness` / `ZiskFv.Compliance`.

It is stated directly over the named ZisK-side predicates rather than over an
`Interface` bundle: every premise below is a coverage obligation that the
generated Aeneas extraction harness discharges for the production decoder /
lowering / circuit path.  Given them, every Sail-executable RV64IM raw word
outside the recorded decode gaps is covered by that path and carries the
per-row contract the opcode soundness theorems expect.
-/

namespace ZiskFv.Completeness

open ZiskFv.Completeness.Rv64imShapes (SupportedDecodeShape)

/-- Public RV64IM completeness theorem.

`SupportedDecodeShape` is the RV64IM single-row decode domain (the seven
instruction-shape families, minus the recorded FENCE gap).  The premises are
the production-ZisK coverage obligations, each discharged by the generated
Aeneas harness:

* `sailExecutable` — the Sail model executes this raw word (the spec domain).
* `ziskDecoderAccepts` — the extracted production decoder supports it.
* `ziskLoweringSucceeds` — lowering assigns it an internal opcode.
* `ziskRowMaterializes` — a satisfying circuit row is built.
* `ziskOpcodeProven` — its opcode is in the set proved sound per-opcode.
* `ziskRowSoundnessContract` — the static per-row input the soundness theorems
  consume.
* `knownDecodeGap` — the explicitly recorded decode carve-outs (FENCE).

Conclusion: outside the known decode gaps, every Sail-executable raw word
clears the whole pipeline and carries the soundness contract. -/
theorem root_completeness
    (sailExecutable : BitVec 32 → Prop)
    (ziskDecoderAccepts ziskLoweringSucceeds : BitVec 32 → Prop)
    (ziskRowMaterializes ziskOpcodeProven : BitVec 32 → Prop)
    (ziskRowSoundnessContract : BitVec 32 → Prop)
    (knownDecodeGap : BitVec 32 → Prop)
    (h_sail_within_supported_decode :
      ∀ raw, sailExecutable raw → SupportedDecodeShape raw)
    (h_decoder_accepts_outside_gaps :
      ∀ raw, SupportedDecodeShape raw → sailExecutable raw →
        ¬ knownDecodeGap raw → ziskDecoderAccepts raw)
    (h_lowering_total :
      ∀ raw, ziskDecoderAccepts raw → ziskLoweringSucceeds raw)
    (h_row_materialization_total :
      ∀ raw, ziskLoweringSucceeds raw → ziskRowMaterializes raw)
    (h_opcode_coverage_total :
      ∀ raw, ziskDecoderAccepts raw → ziskOpcodeProven raw)
    (h_soundness_contract :
      ∀ raw, SupportedDecodeShape raw → ziskLoweringSucceeds raw →
        ziskRowSoundnessContract raw) :
    ∀ raw, sailExecutable raw → ¬ knownDecodeGap raw →
      (ziskDecoderAccepts raw ∧ ziskLoweringSucceeds raw ∧
        ziskRowMaterializes raw ∧ ziskOpcodeProven raw) ∧
      ziskRowSoundnessContract raw := by
  intro raw h_sail h_not_decode_gap
  have h_shape := h_sail_within_supported_decode raw h_sail
  have h_decode := h_decoder_accepts_outside_gaps raw h_shape h_sail h_not_decode_gap
  have h_lower := h_lowering_total raw h_decode
  exact
    ⟨⟨h_decode,
        h_lower,
        h_row_materialization_total raw h_lower,
        h_opcode_coverage_total raw h_decode⟩,
      h_soundness_contract raw h_shape h_lower⟩

end ZiskFv.Completeness
