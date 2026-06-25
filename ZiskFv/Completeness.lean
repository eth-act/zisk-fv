import ZiskFv.Completeness.Rv64im.SailDecode

/-!
# Completeness — blueprint

Read top to bottom; the whole point is to make "the eventual theorem" and "what
we currently assume" each a single named object.

* `ZiskSurface` — ZisK's production decode/lower/circuit surface as abstract
  predicates on a raw word. Placeholders for the *real* ZisK predicates, which
  live in the Aeneas-extracted world this build cannot import.
* `ZiskSurface.Covers raw` — what "ZisK fully handles `raw`" means: the whole
  pipeline succeeds and the soundness-row contract holds.
* `EventualCompleteness state z` — **THE GOAL.** Every Sail-executable RV64IM word
  outside the known decode gaps is covered by ZisK. This is what we want
  *unconditionally*.
* `ZiskSurface.CoverageAssumptions z` — **WHAT WE CURRENTLY ASSUME.** One field per
  pipeline stage; each field is a plan item the Aeneas harness must discharge.
* `sail_executable_within_supported_decode_shape` — PROVEN, and the *only* piece
  actually established in this build: Sail-executable words land in
  `SupportedDecodeShape`.
* `root_completeness` — proves `CoverageAssumptions → EventualCompleteness`. The
  ZisK content is carried entirely by the assumptions; the lone proven step is the
  Sail→shape bridge.

So the gap between today and the unconditional theorem is *exactly* the fields of
`CoverageAssumptions`: discharge them (against ZisK's real surface, via the Aeneas
bridge) and `root_completeness` yields `EventualCompleteness` outright.

Everything here is an *acceptance/coverage* claim (ZisK does not reject what Sail
accepts), NOT a correctness claim (correctness is the soundness axis,
`ZiskFv.Compliance`). The abstract `Rv.Interface` route under
`ZiskFv/Completeness/Aspirational/` is quarantined and unused here.
-/

namespace ZiskFv.Completeness

open ZiskFv.Completeness.Rv64imShapes (SupportedDecodeShape)
open ZiskFv.Completeness.SailDecode

/-- The Sail-side containment bridge (PROVEN, unconditional).

Every Sail-executable RV64IM word has a bit-layout inside the
`SupportedDecodeShape` enumeration, proven by evaluating the real generated Sail
decoder/encoder (`LeanRV64D.Functions.ext_decode` / `encdec_forwards`).

* `state` / `raw` — a Sail machine state (the decoder consults extension state)
  and the 32-bit word.
* premise `Rv64imEnabledSailState state` — `state` has `M` enabled, `Zmmul`
  disabled.
* premise `SailRv64imExecutableRawIn state raw` — `raw` round-trips through Sail
  to one of the eleven enumerated RV64IM instruction classes.
* conclusion `SupportedDecodeShape raw` — `raw` matches one of the seven shape
  families.

Caveat: `SupportedDecodeShape` is a hand-written predicate (`Rv64im/Shapes.lean`),
NOT ZisK's decoder — this says nothing about ZisK. -/
theorem sail_executable_within_supported_decode_shape :
    ∀ state raw, Rv64imEnabledSailState state →
      SailRv64imExecutableRawIn state raw → SupportedDecodeShape raw :=
  sail_rv64im_executable_contained_in_supported_decode_in

/-- ZisK's production decode/lower/circuit surface, as abstract predicates on a
raw 32-bit word. Each field is a placeholder for the corresponding *real* ZisK
predicate that the Aeneas extraction would instantiate it with. -/
structure ZiskSurface where
  /-- ZisK's production decoder accepts (supports) the word. -/
  decoderAccepts : BitVec 32 → Prop
  /-- Lowering assigns the word an internal ZisK opcode. -/
  loweringSucceeds : BitVec 32 → Prop
  /-- ZisK builds a satisfying circuit row for the word. -/
  rowMaterializes : BitVec 32 → Prop
  /-- The word's opcode is in the set ZisK has proven sound per-opcode. -/
  opcodeProven : BitVec 32 → Prop
  /-- The static per-row input the soundness theorems consume. -/
  rowSoundnessContract : BitVec 32 → Prop
  /-- Explicitly recorded decode carve-outs (e.g. the FENCE subset ZisK rejects);
  these words are excluded from any coverage claim. -/
  knownDecodeGap : BitVec 32 → Prop

/-- "ZisK fully covers `raw`": the whole pipeline succeeds (decoder accepts →
lowering → row → opcode) and the soundness-row contract holds. -/
def ZiskSurface.Covers (z : ZiskSurface) (raw : BitVec 32) : Prop :=
  (z.decoderAccepts raw ∧ z.loweringSucceeds raw ∧
    z.rowMaterializes raw ∧ z.opcodeProven raw) ∧ z.rowSoundnessContract raw

/-- **THE GOAL.** Every Sail-executable RV64IM word (in an RV64IM-enabled state),
outside ZisK's known decode gaps, is fully covered by ZisK. This is the eventual
*unconditional* completeness theorem; `root_completeness` delivers it once the
`CoverageAssumptions` are discharged. -/
def EventualCompleteness (state : SailState) (z : ZiskSurface) : Prop :=
  ∀ raw, SailRv64imExecutableRawIn state raw → ¬ z.knownDecodeGap raw → z.Covers raw

/-- **WHAT WE CURRENTLY ASSUME.** The per-stage coverage facts about ZisK's real
surface, to be discharged by the Aeneas extraction harness. Each field is one
item on the plan; discharging all of them closes the gap to
`EventualCompleteness`. -/
structure ZiskSurface.CoverageAssumptions (z : ZiskSurface) : Prop where
  /-- PLAN ITEM (the only one touching the Sail-derived shape domain): every
  in-shape word that is not a known gap is accepted by ZisK's decoder. -/
  decoderAcceptsInShape :
    ∀ raw, SupportedDecodeShape raw → ¬ z.knownDecodeGap raw → z.decoderAccepts raw
  /-- PLAN ITEM: every accepted word lowers. -/
  loweringTotal : ∀ raw, z.decoderAccepts raw → z.loweringSucceeds raw
  /-- PLAN ITEM: every lowered word materializes a row. -/
  rowTotal : ∀ raw, z.loweringSucceeds raw → z.rowMaterializes raw
  /-- PLAN ITEM: every accepted word's opcode is proven. -/
  opcodeTotal : ∀ raw, z.decoderAccepts raw → z.opcodeProven raw
  /-- PLAN ITEM: every in-shape, lowered word satisfies the soundness contract. -/
  soundnessContract :
    ∀ raw, SupportedDecodeShape raw → z.loweringSucceeds raw →
      z.rowSoundnessContract raw

/-- Completeness, as `CoverageAssumptions → EventualCompleteness`.

Blueprint reading: GIVEN an RV64IM-enabled Sail `state`, ZisK's (abstract)
surface `z`, and the coverage `assumptions` about it, THEN every Sail-executable
RV64IM word outside the known gaps is covered by ZisK.

The lone step proven outright is the Sail→shape bridge
(`sail_executable_within_supported_decode_shape`); all ZisK content is carried by
`assumptions`. Discharge `assumptions` and this is `EventualCompleteness state z`
unconditionally.

* `state` — the Sail machine state decoding is evaluated against.
* `h_state` — evidence `state` is RV64IM-configured (`M` on, `Zmmul` off).
* `z` — the ZisK surface (the abstract predicates).
* `assumptions` — the per-stage coverage facts about `z` (the plan items). -/
theorem root_completeness
    (state : SailState) (h_state : Rv64imEnabledSailState state)
    (z : ZiskSurface) (assumptions : z.CoverageAssumptions) :
    EventualCompleteness state z := by
  intro raw h_sail h_not_gap
  have h_shape :=
    sail_executable_within_supported_decode_shape state raw h_state h_sail
  have h_decode := assumptions.decoderAcceptsInShape raw h_shape h_not_gap
  have h_lower := assumptions.loweringTotal raw h_decode
  exact
    ⟨⟨h_decode,
        h_lower,
        assumptions.rowTotal raw h_lower,
        assumptions.opcodeTotal raw h_decode⟩,
      assumptions.soundnessContract raw h_shape h_lower⟩

end ZiskFv.Completeness
