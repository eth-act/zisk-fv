# STATUS — decoder-162 (resolve #162)

Stream: #162 — prove the extracted RV64IM decoder accepts/classifies each RV64IM raw
word, in-build and soundly (no `native_decide`/`bv_decide`), discharging completeness
obligation `decoderAcceptsInShape` (`ZiskFv/Completeness.lean:128`).
Branch: decoder-162 (off origin/main @ 400841f9, after #160 merged).
Worktree: /home/cody/zisk-fv/.worktrees/decoder-162
Plan: docs/ai/plan/PLAN_DECODER_162.md   Issue: eth-act/zisk-fv#162

## Make-or-break: RESOLVED ✅ (spike green 2026-06-27)
- Concrete word decode → `ok true` proves by `rfl` (monadic forward reduction works;
  decide/native_decide N/A — `Result Bool` not Decidable, irrelevant).
- Symbolic masking arith (`(rawRType..)&&&127 = ofNat opcode`, `(raw>>>12)&&&7 = funct3`)
  proves SOUND via getLsbD/testBit recipe (NO bv_decide). Detailed in plan + memory.
- Every word in all 7 `SupportedDecodeShape` families hits a non-reserved arm → discharge
  is the stronger `∀ raw, SupportedDecodeShape raw → ziskDecoderAccepts raw` (no gap excl).

## Checklist
- [x] P0 worktree + build symlinks + `lake exe cache get` + in-build aeneas import builds
- [x] P1 make-or-break spike (masking + concrete reduction) — GREEN
- [x] P2 Foundation: `Decode/Masks.lean` (R/I/S/B/U/J field extraction) + `Decode/Leaves.lean` (toU32, signext_ok, leaf specs, bind_supported)
- [x] P3a families R/I/S/B/U/J proven (rtype/itype/stype/btype/utype/jtype _family_accepts), clean axioms
- [~] P3b shift64/shift32/fence families (DELEGATED to background agent a4895cb5063485063; stubbed sorry in Leaves.lean)
- [x] P4 `Decode.lean` — `ziskDecoderAccepts` + `zisk_decoder_accepts_supported_shape` + `real_decoder_accepts_in_shape` (obligation bridge); compiles
- [x] P5a integration prep (no-build text edits, pending full build): ZiskFv.lean imports Decode; Completeness.lean doc pointer; bin/TrustGate/Main.lean check-extraction-closure extended to ZiskFv.Compliance.Decode.*
- [ ] P5b full `lake build` + confirm clean kernel-only axiom closure on headline
- [ ] P6 trust gates (V1 `check-all.sh` + V2 `check-all-semantic.sh`); regenerate baselines if needed
- [ ] P7 PR

## Integration notes (pending agent completion of P3b)
- After agent finishes shift/fence: full `lake build`, `lake exe trust-gate check-extraction-closure`,
  `#print axioms ZiskFv.Compliance.Decode.zisk_decoder_accepts_supported_shape` (expect propext/Classical.choice/Quot.sound),
  V1+V2 gates, then PR.

## Scratch to DELETE before PR
- `ZiskFv/MaskSpike.lean`
- `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/DecodeSpike.lean`
