# Plan — Resolve #111: discharge `aeneasBridgeTrust` from the real Aeneas extraction

## Context

`OpEnvelope.aeneasBridgeTrust` (`ZiskFv/Compliance/AeneasBridgeTrust/Base.lean:19`) is the
per-arm decode/lowering bridge: for each opcode it states the Main-row facts ZisK's production
lowerer would produce (`op`, `isExternalOp`, `m32`, `setPc`, `storePc`, row-mode, plus dynamic
immediate/lane facts). It is **not an axiom** (project closure = 0 project axioms). The gap: the
decode pins are *asserted*, not *proved from the extraction*. Concretely, the live trace path
(`root_soundness` → `stepStrong_*`) fabricates the `MainExtractedRow` from literals — e.g.
`stepStrong_lui` calls `mainRowProvenance_of_pins m i.val ExtractedConst.opCopyB false false …`
(`TraceLevelExport/StepStrongControlStore.lean:~338-348`) and fills `LuiRowMode := { op_eq := rfl, … }`.
So we prove the circuit computes the right value but **assume** the row decodes to the claimed op.

Goal: replace that fabrication with proof terms about the real extracted lowerer in
`trust/aeneas/ProductionM2.lean`, **in the main `lake build`**, without adding trust.

## Toolchain decision (keep Lean fixed at 4.28.0)

We do **not** bump our Lean. We pin the `aeneas` flake input back to its 4.28-compatible revision
(`a2fcf1923d` — last AeneasVerif/aeneas on the `v4.28.0-rc1` toolchain; the June-19 spike used it and
imported `ProductionM2` into our 4.28 build). The current pin (`ac9f1bc5…`) targets a newer Lean —
that is the only reason "4.30" came up. Reverting the aeneas pin is what lets us import without
touching our toolchain.

## Corrected technical premises (verified this session)

- **`op` pin is trivial.** `ZiskOp.code` (`ProductionM2.lean:~1594-1679`) is a plain match returning
  numeric literals (`CopyB => 1`, `Add => 10`, …) that already equal `ExtractedConst.*`
  (`RowProvenance.lean:~68-114`). So `op`/`isExternalOp` discharge by `rfl`/`simp` — no discriminant
  translation needed.
- **The wall is `store_reg`** (`ProductionM2.lean:~2012`): its `if offset < REGS_IN_MAIN_FROM / > REGS_IN_MAIN_TO`
  branches read `@[global_simps, irreducible]` `Usize` consts whose type is `BitVec System.Platform.numBits`,
  and `numBits = 64` is not `rfl`. This blocks naive `decide`/`rfl`.
- **Static row-mode pins MIGHT dodge the wall** (optimistic): `setPc`/`storePc`/`m32` are
  *branch-invariant* in the lowering chain. BUT the 2026-06-19 spike found the monadic do-block does
  not reduce at all under `decide`/`rfl`/`simp`/`with_unfolding_all rfl` (the `lift(...)` heads never
  become `.ok`), so you cannot even reach `store_reg`'s `if` to split on it. The only *reducing* route
  is `native_decide`. Treat the sound static-pin discharge as UNVERIFIED until the Phase-1 tractability
  test; the real sound route may be the large per-opcode `progress` symbolic execution.
- **Live target is `mainRowProvenance_of_pins`** (`TraceLevelExport/Base.lean:~99`). The
  `OpEnvelope.*OfExtractedShape` builders under `AeneasBridgeTrust/` are the right shape but are
  effectively dead in the live proof (only a doc-comment reference) — useful as a template, not the swap site.

## Trust route: R1 (sound, no `native_decide`) — chosen

`native_decide` is the only route that *reduces* through the irreducible/`numBits` walls, but it injects
`Lean.ofReduceBool` + `Lean.trustCompiler`, which `trust/scripts/check-generated-axiom-allowlist.sh`
forbids (allows only `propext`/`Classical.choice`/`Quot.sound`) and which the #75 campaign already
eliminated. So the plan uses the **sound** route: per-opcode Aeneas `progress`/`scalar_tac` symbolic
execution + a `System.Platform.numBits` 32/64 case-split (`numBits_eq`) + proved `@[reducible]` *mirrors*
of the irreducible consts (Lean won't flip `@[irreducible]`, so prove `mirror = original` instead).
R2 (`native_decide` + allowlist edit + `trusted-base.md` class + baseline regen) is held **only** as a
scoped fallback if value-pins prove intractable — explicit CODEOWNER decision, never the default.

## Phases

### Phase 0 — make-or-break import (infra only, no proofs)
1. Pin `flake.lock` aeneas `ac9f1bc5…` → `a2fcf1923d…`; regenerate `trust/aeneas/ProductionM2.lean`
   under the new pin (stay byte-identical to what the tracked-diff gate expects).
2. Vendor the Aeneas Lean runtime (`backends/lean`) as a path `require`; align its mathlib rev
   (`5352afcc`→`8f9d9cff`) and transitive deps to the main worktree revs. **Edit `lake-manifest.json`
   by hand — never `lake update`.**
3. Add `require aeneas` to `lakefile.toml`; point a lib/glob at the **canonical** `trust/aeneas/`
   (do not copy `ProductionM2.lean`). Add a thin probe module importing `ProductionM2`.
4. Update boundary gates (`check-aeneas-production-boundary.py`, generated-bridge-manifest,
   check-no-checked-in-aeneas-artifacts.sh) to permit (not require) the in-build import (CODEOWNER).

**Success:** `lake build` green with `ProductionM2` imported; ground eval of the LUI lowerer on
`0x123451B7` = `op=1, isExternalOp=false, m32=false, setPc=false, storePc=false`; `#print axioms` on
the probe shows no `sorryAx` on the LUI path.

**Decision tree:** GO → Phase 1. Runtime won't build under 4.28.0 release → minimal 4.28 runtime shim
(only the primitives the lowering path touches; bonus: skips the runtime Slice/String sorries). Truly
blocked → strengthen the out-of-band gate + document non-discharge (do not fake progress).

### Phase 1 — LUI tractability test (R1 make-or-break) + `Extraction.lean` pilot
First **empirically test** whether the static LUI pins discharge soundly via `progress`/`scalar_tac`
(no `native_decide`). DECISION POINT: GO → build the pilot; NO-GO → large per-opcode `progress` effort,
R2-with-CODEOWNER, or honest out-of-band fallback — report to user.
Then create `ZiskFv/Compliance/AeneasBridgeTrust/Extraction.lean`:
1. `@[reducible] def mainExtractedRowOfZiskInst : ZiskInst → MainExtractedRow` (pure projection/cast).
2. op lemmas `(ZiskOp.code .CopyB).toNat = ExtractedConst.opCopyB := by rfl` (+ Add/Sub/…).
3. `luiExtraction_rowMode` — the 5 row-mode pins from `Riscv2ZiskContext.lui`.
4. `mainRowProvenance_of_extraction` — drop-in mirroring `mainRowProvenance_of_pins`.

### Phase 2 — uniform static pins across 63 ops (batch by lowerer shape)
U-type/control → Binary R/I → Mul/DivRem (+m32 for W-ops) → Branches → Loads/Stores. Each op gets a
`*Extraction_rowMode` theorem.

### Phase 3 — value pins (scoped; needs the `numBits` recipe) — DEFERRABLE
`store`/`storeOffset`/`ind_width`/`jmp_offset`: build the const-mirror + `numBits` split + `scalar_tac`
recipe once on SD, generalize. Can move to a follow-up issue without blocking Phases 0-2.

### Wiring swap (final, small)
Replace the `mainRowProvenance_of_pins` fabrication in the live `stepStrong_*` builders with
`mainRowProvenance_of_extraction`. Own small PR after the discharge library lands and builds.

## Out of scope — named residuals (do not silently close)
Dynamic per-arm conjuncts (`h_imm_lo_nat`, lanes, byte-chains); MirrorFidelity for dynamic fields;
RomImageBinding (committed ROM word == raw). State boundaries in PR body + `trust/trusted-base.md`.

## Anti-laundering compliance (CLAUDE.md)
Net change must **reduce** caller-supplied promise; `mainExtractedRowOfZiskInst` `@[reducible]`;
const-mirror lemmas **proved** not `axiom`'d; `*Extraction_rowMode` theorems take only the raw lowering
input + an `ok`-eval hyp, not the pins re-introduced as hypotheses. R1 closure diff: no new axiom names.

## Verification
`nix develop --command lake build`; `trust/scripts/check-all.sh`; `trust/scripts/check-all-semantic.sh`;
`nix run .#aeneas-production-extract-check-tracked`; axiom audit (`lake exe trust-gate` /
`#print axioms`) — `ofReduceBool`/`trustCompiler`/`sorryAx` absent unless R2 chosen + allowlisted.

## Critical files
- `trust/aeneas/ProductionM2.lean` (`ZiskOp.code:~1594`, `op_zisk:~1929`, `store_reg:~2012`, `lui:~2417`, `ZiskInst:~1308`)
- `ZiskFv/Compliance/RowProvenance.lean` (`MainExtractedRow:48`, `ExtractedConst:~68`, `MainRowProvenance:123`) + new `AeneasBridgeTrust/Extraction.lean`
- `ZiskFv/Compliance/TraceLevelExport/Base.lean:~99` + `StepStrong*.lean` (wiring swap)
- `flake.lock`, `lakefile.toml`, `lake-manifest.json`, `scripts/aeneas-production-extract.sh`,
  `trust/scripts/{check-no-checked-in-aeneas-artifacts.sh,check-aeneas-production-boundary.py,check-generated-axiom-allowlist.sh}`
