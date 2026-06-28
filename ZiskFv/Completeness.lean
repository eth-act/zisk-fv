import ZiskFv.Completeness.Rv64im.SailDecode

/-!
# Completeness — blueprint

Read top to bottom. Two kinds of object: the **ingredients** (bare predicates
about a raw word) and the **relations** between them (closed `Prop`s we assume).

* `OutstandingZiskPredicates` — the ingredients: ZisK's decode / lower / row /
  opcode / soundness-contract / known-gap predicates, each `BitVec 32 → Prop`.
  Placeholders for the *real* ZisK predicates, which live in the Aeneas-extracted
  world this build cannot import.
* `OutstandingZiskPredicates.Covers z raw` — the per-word target: all the success
  ingredients hold at `raw`.
* `EventualCompleteness state z` — **THE GOAL.** Every Sail-executable RV64IM word
  outside the known decode gaps is `Covers`-ed. What we want *unconditionally*.
* The obligation predicates `z.decoderAcceptsInShape`, `z.loweringTotal`,
  `z.rowTotal`, `z.opcodeTotal`, `z.soundnessContract` — the *relations* between
  the ingredients we currently **assume** (the pipeline chains). Each is a
  separate closed `Prop` the Aeneas harness must discharge; together they are the
  whole gap to `EventualCompleteness`.
* `sail_executable_within_supported_decode_shape` — PROVEN, and the *only* piece
  actually established in this build: Sail-executable words land in
  `SupportedDecodeShape`.
* `skeletal_root_completeness` — given `z` and the five obligation predicates,
  proves `EventualCompleteness state z`. The ZisK content is carried entirely by
  the obligations; the lone proven step is the Sail→shape bridge. (Named
  *skeletal* because it is a frame with the real ZisK obligations left as holes.)

## Tracking issues (the plan to make this unconditional)

* eth-act/zisk-fv#111 — connect the real Aeneas-extracted decoder/lowering
  in-build; the decode side of Aeneas trust. Discharges `decoderAcceptsInShape`
  and `loweringTotal`.
* eth-act/zisk-fv#108 — extend the Aeneas extraction to ZisK table data + witness
  builders. Backs `rowTotal` / `opcodeTotal` / `soundnessContract`.
* eth-act/zisk-fv#74 — instantiate the theorem on a real ZisK execution trace
  (end-to-end witness): produces a concrete `OutstandingZiskPredicates` to feed
  here.
* eth-act/zisk-fv#77 — differentially test the Sail-Lean spec against the
  reference emulator; trust in the Sail side the proven bridge rests on.
* eth-act/zisk-fv#75 — eliminate `native_decide` / kernel-only axiom closure; the
  proven Sail→shape bridge currently evaluates via `native_decide`.
* eth-act/zisk-fv#78 — independent re-checking of the proof with an external kernel
  (lean4lean).

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
* premise `IsaExtensionsEnabled state` — `state` has `M` enabled, `Zmmul`
  disabled.
* premise `SailRv64imExecutableRawIn state raw` — `raw` round-trips through Sail
  to one of the eleven enumerated RV64IM instruction classes.
* conclusion `SupportedDecodeShape raw` — `raw` matches one of the seven shape
  families.

The proof evaluates the Sail functions via `native_decide`-style reduction
(eth-act/zisk-fv#75 tracks removing `native_decide`; eth-act/zisk-fv#77 tracks
validating the Sail spec itself against the reference emulator).

Caveat: `SupportedDecodeShape` is a hand-written predicate (`Rv64im/Shapes.lean`),
NOT ZisK's decoder — this says nothing about ZisK. -/
theorem sail_executable_within_supported_decode_shape :
    ∀ state raw, IsaExtensionsEnabled state →
      SailRv64imExecutableRawIn state raw → SupportedDecodeShape raw :=
  sail_rv64im_executable_contained_in_supported_decode_in

/-- The ingredients: ZisK's production decode/lower/circuit surface, as abstract
predicates on a raw 32-bit word. Each field is a placeholder for the corresponding
*real* ZisK predicate the Aeneas extraction would instantiate it with
(eth-act/zisk-fv#111 for decode/lowering, eth-act/zisk-fv#108 for table/witness
data; eth-act/zisk-fv#74 produces a concrete instance from a real trace). -/
structure OutstandingZiskPredicates where
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
def OutstandingZiskPredicates.Covers (z : OutstandingZiskPredicates) (raw : BitVec 32) : Prop :=
  (z.decoderAccepts raw ∧ z.loweringSucceeds raw ∧
    z.rowMaterializes raw ∧ z.opcodeProven raw) ∧ z.rowSoundnessContract raw

/-- **THE GOAL.** Every Sail-executable RV64IM word (in an RV64IM-enabled state),
outside ZisK's known decode gaps, is fully covered by ZisK. This is the eventual
*unconditional* completeness theorem; `skeletal_root_completeness` delivers it
once the obligation predicates below are discharged. A concrete `z` plus
discharged obligations — the end-to-end instantiation tracked in
eth-act/zisk-fv#74 — makes this hold outright. -/
def EventualCompleteness (state : SailState) (z : OutstandingZiskPredicates) : Prop :=
  ∀ raw, SailRv64imExecutableRawIn state raw → ¬ z.knownDecodeGap raw → z.Covers raw

/-! ### Obligation predicates

The relations between the ingredients that `skeletal_root_completeness` assumes —
each a closed `Prop` about a `z`, NOT a per-word ingredient. Discharging all five
(against ZisK's real surface) closes the gap to `EventualCompleteness`. -/

/-- OBLIGATION (the only one touching the Sail-derived shape domain): every
in-shape word that is not a known gap is accepted by ZisK's decoder.
Discharge: eth-act/zisk-fv#162 — `ZiskFv.Compliance.Decode.real_decoder_accepts_in_shape`
proves this in-build for the REAL extracted decoder (`extract_rv64im_opcode_supported`,
instantiating `decoderAccepts := ziskDecoderAccepts`), kernel-soundly. (Tracked under
eth-act/zisk-fv#111, the Aeneas decode/lowering connection.) -/
def OutstandingZiskPredicates.decoderAcceptsInShape (z : OutstandingZiskPredicates) : Prop :=
  ∀ raw, SupportedDecodeShape raw → ¬ z.knownDecodeGap raw → z.decoderAccepts raw

/-- OBLIGATION: every accepted word lowers. Discharge: eth-act/zisk-fv#111. -/
def OutstandingZiskPredicates.loweringTotal (z : OutstandingZiskPredicates) : Prop :=
  ∀ raw, z.decoderAccepts raw → z.loweringSucceeds raw

/-- OBLIGATION: every lowered word materializes a row. Discharge:
eth-act/zisk-fv#108. -/
def OutstandingZiskPredicates.rowTotal (z : OutstandingZiskPredicates) : Prop :=
  ∀ raw, z.loweringSucceeds raw → z.rowMaterializes raw

/-- OBLIGATION: every accepted word's opcode is proven. Discharge:
eth-act/zisk-fv#108. -/
def OutstandingZiskPredicates.opcodeTotal (z : OutstandingZiskPredicates) : Prop :=
  ∀ raw, z.decoderAccepts raw → z.opcodeProven raw

/-- OBLIGATION: every in-shape, lowered word satisfies the soundness contract.
Discharge: eth-act/zisk-fv#108. -/
def OutstandingZiskPredicates.soundnessContract (z : OutstandingZiskPredicates) : Prop :=
  ∀ raw, SupportedDecodeShape raw → z.loweringSucceeds raw → z.rowSoundnessContract raw

/-- Completeness skeleton: the five obligation predicates ⟹ `EventualCompleteness`.

Blueprint reading: GIVEN an RV64IM-enabled Sail `state`, ZisK's (abstract) surface
`z`, and the five obligations about it, THEN every Sail-executable RV64IM word
outside the known gaps is covered by ZisK.

The lone step proven outright is the Sail→shape bridge
(`sail_executable_within_supported_decode_shape`); all ZisK content is carried by
the obligation hypotheses. Discharge them (eth-act/zisk-fv#111 + #108, on a
concrete `z` from #74) and this is `EventualCompleteness state z` unconditionally.

* `state` / `sailIsa` — the Sail machine state and evidence it is RV64IM-configured.
* `z` — the ZisK predicates (the ingredients).
* `decoderAcceptsInShape` … `soundnessContract` — the five obligation hypotheses. -/
theorem skeletal_root_completeness
    (state : SailState) (sailIsa : IsaExtensionsEnabled state)
    (z : OutstandingZiskPredicates)
    (decoderAcceptsInShape : z.decoderAcceptsInShape)
    (loweringTotal : z.loweringTotal)
    (rowTotal : z.rowTotal)
    (opcodeTotal : z.opcodeTotal)
    (soundnessContract : z.soundnessContract) :
    EventualCompleteness state z := by
  intro raw h_sail h_not_gap
  have h_shape :=
    sail_executable_within_supported_decode_shape state raw sailIsa h_sail
  have h_decode := decoderAcceptsInShape raw h_shape h_not_gap
  have h_lower := loweringTotal raw h_decode
  exact
    ⟨⟨h_decode,
        h_lower,
        rowTotal raw h_lower,
        opcodeTotal raw h_decode⟩,
      soundnessContract raw h_shape h_lower⟩

end ZiskFv.Completeness
