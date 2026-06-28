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
- [ ] P3b shift family (funct6/funct7 + decode_i_true) + fence family
- [ ] P4 `Decode.lean` — `ziskDecoderAccepts` + `zisk_decoder_accepts_supported_shape` + obligation bridge
- [ ] P5 wire into `Completeness.lean`; confirm clean kernel-only axiom closure
- [ ] P6 trust gates (V1 `check-all.sh` + V2 `check-all-semantic.sh`), full `lake build`
- [ ] P7 PR

## Scratch to DELETE before PR
- `ZiskFv/MaskSpike.lean`
- `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/DecodeSpike.lean`
