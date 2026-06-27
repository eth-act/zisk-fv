Stream: #111 — discharge `aeneasBridgeTrust` from the real Aeneas extraction.
Branch: aeneas-bridge-111 (off origin/main @ 6ffb31e5).
Plan: docs/ai/plan/PLAN_AENEAS_BRIDGE_111.md   Issue: eth-act/zisk-fv#111

Goal: replace the *asserted* Main-row decode pins (the `mainRowProvenance_of_pins`
fabrication in the live root_soundness → stepStrong_* path) with proof terms about the
real extracted lowerer in trust/aeneas/ProductionM2.lean, IN the main lake build, without
adding trust. Keep Lean 4.28.0.

Route: keep Lean 4.28.0; pin aeneas back to a2fcf1923d (last v4.28.0-rc1 commit) — import
is GO per spike. Trust R1 (sound, no native_decide); R2 only as CODEOWNER fallback. Scope:
static row-mode pins first; value pins (Phase 3) deferrable; dynamic conjuncts out of scope.

Status: MAKE-OR-BREAK PASSED — R1 is GO. Probe agent secured a SOUND concrete LUI static-pin proof
off the real Riscv2ZiskContext lowerer with axioms = {propext, Classical.choice, Quot.sound} ONLY
(no native_decide/ofReduceBool/trustCompiler/sorryAx). The ~16 numBits/Usize helpers re-prove
soundly via the System.Platform.numBits_eq 32/64 split. A symbolic (arbitrary-input) version is
compiling. No R2/out-of-band fallback needed.

DELIVERED by probe (persisted in docs/ai/aeneas-proof-reference/{LuiPins,WorkingHelpers,AllHelpers}.lean):
- SYMBOLIC `lui_static_pins` (arbitrary input): lui succeeds ⇒ inst has op=1(CopyB)/isExt=false/
  m32=false/setPc=false/storePc=false. Axioms clean. Uses store_reg_pins + bind_eq_ok_imp helpers.
- CONCRETE `lui_pins_concrete`. Axioms clean.
- Sound helpers: setWidth-family via `rcases System.Platform.numBits_eq with h|h <;> rw [h] <;> decide`
  (rw not subst — numBits is a constant); fixed-width facts via `decide`; shift via simp only. VERBATIM
  in the reference files.
- Per-theorem closure isolation CONFIRMED: importing RvCompleteness (full of native_decide lemmas)
  does NOT taint a theorem whose own proof avoids them (collectAxioms is per-theorem).

KNOWN HELPER GAP (Phase 2, register-source/store ops only): the cast/hcast-of-REGS_IN_MAIN_* variants
(one_u64_not_lt_regs_from etc.) do NOT close via numBits_eq because numBits is hidden inside the
`1#usize.bv` OfNat; need a value-level lemma `(1#usize).val = 1`. NOT needed for LUI/immediate ops.

REMAINING WORK (labor, not risk — the hard proof is done + portable):
1. 4.28 aeneas-world rebuild: vendor rc1 aeneas-lean (store 6yfihaq6.../hpw9azi...), patch require
   mathlib → 8f9d9cff + toolchain → v4.28.0; get ProductionM2 to compile on 4.28 (may need
   re-extraction under a2fcf/rc1 if the committed rc2 source is API-incompatible with rc1 aeneas).
   TOOLCHAIN NOTE: the probe's proofs typecheck under v4.30.0-rc2 (the on-disk oleans are rc2); the
   MAIN build is v4.28.0 — rc2 oleans can't be imported, hence the 4.28 rebuild.
2. Extraction.lean (port LuiPins + mainExtractedRowOfZiskInst projection + 33 op-code lemmas).
3. Phase 2 (63 ops per PHASE2_PER_OP_SPEC.md).
4. Wiring swap (extractedRow := production output); RomImageBinding named residual.
5. Boundary gates + verification + PR.

PHASE 0d / integration design (confirmed by reading the gates — LIGHTER than feared):
- MIRROR THE CLEAN PATTERN: populate the 4.28-patched aeneas-lean runtime into gitignored
  build/aeneas-lean (new nix step like clean.nix: cp -rL source + patch mathlib require → our rev +
  lean-toolchain → v4.28.0), then `require aeneas from build/aeneas-lean` in lakefile.toml. Do NOT
  commit the runtime.
- ProductionM2 stays canonical at trust/aeneas/ProductionM2.lean (committed, as now); a lean_lib
  points there OR Extraction.lean imports it.
- check-locality.sh scans ZiskFv/ ONLY → the runtime's native_decide/sorry lemmas don't trip it.
- check-no-checked-in-aeneas-artifacts.sh: build/ is gitignored + runtime has no .llbc/ProductionM* → OK.
- check-aeneas-production-boundary.py is Rust-side (anti-parallel-lowerer) → unaffected by the import.
- check-aeneas-generated-bridge-manifest.py: MAY need updating (the documentary cross-workspace link
  becomes a real in-build import). Review when wiring.
- LUI pilot Extraction.lean fully drafted at docs/ai/aeneas-proof-reference/Extraction.lean.draft.
- Agent ad08fc2c (background) rebuilding aeneas+ProductionM2 on 4.28 = the current gate.

Make-or-break finding (2026-06-26, no rebuild needed):
- Import is GO and CHEAP: committed trust/aeneas/ProductionM2.lean is byte-identical to the
  on-disk extraction; a2fcf1923d validates (transitive charon ed22146b). No charon re-extraction
  needed — only the a2fcf (rc1, 4.28-compat) aeneas-lean runtime to import against
  (/nix/store/hpw9...source/backends/lean).
- R1 is GO (CORRECTED — my earlier "native_decide only" was a grep miss of multi-line `by\n simp`).
  CopybScratch.lean (CopyB == LUI's opcode) proves materialization with SOUND `simp` (no
  native_decide) using THEOREM helpers: one_u64_val_not_lt_regs_from_set_width,
  regs_to_set_width_val_not_lt_one_u64, uscalar64_shift_right_i32_32_ok_true, one_u64_scalar_ne_zero
  (+ i64 variants) — these soundly resolve store_reg's numBits/Usize comparisons + unfold the
  @[irreducible] consts. Helpers are theorems (not axioms). So the sound static-pin discharge EXISTS.
  Background agent a76bcfc817f42e0f0 is RUNNING the proof + #print axioms to confirm closure
  and that a2fcf aeneas-lean builds vs release mathlib.

REFINED VERDICT (2026-06-26): the CopybScratch `simp` proof is NOT actually sound as-is — its helper
lemmas (one_u64_val_not_lt_regs_from_set_width, regs_to_set_width_val_not_lt_one_u64, i32_32_*, …,
~16 of them in ScalarScratch.lean) are each proved BY native_decide, so the closure transitively pulls
ofReduceBool/trustCompiler. The factoring just HID the native trust. BUT these helpers are tiny
concrete finite inequalities (e.g. ¬(1 < setWidth 64 1#numBits)); the real bounded R1 question is
whether they re-prove SOUNDLY via `rcases System.Platform.numBits_eq with h|h <;> simp[h] <;> decide`
(numBits 32/64 split). If yes → R1 GO with bounded effort (re-prove ~16 helpers; reuse the simp
structure). Probe agent directed to test this.

CONFIRMED independently: System.Platform.numBits_eq : numBits=32 ∨ numBits=64 EXISTS in Lean core
(Init/Prelude.lean:2266, present in 4.28-rc1); core uses `cases System.Platform.numBits_eq <;>
simp_all` to resolve USize facts, and the rc1 bv_decide frontend explicitly HINTS this split for
USize goals. So the sound handle is real + idiomatic → R1 helpers very likely re-prove soundly.

In-build gap (precise): mainRowProvenance_of_pins (TraceLevelExport/Base.lean:99) builds
`extractedRow` as a LITERAL from the caller's `opc` (the circuit decode residual), so LuiRowMode's
`extractedRow.op = opCopyB` is rfl-true against a NAMED CONSTANT — never tied to the real Rust
lowerer. #111 = make `extractedRow := mainExtractedRowOfZiskInst (productionLower raw)` and prove the
static pins (op/isExt/m32/setPc/storePc) from ProductionM2. Per-op RowMode structs live in
RowProvenance.lean (LuiRowMode:165, AuipcRowMode, JalRowMode, jalrPins, fencePins) + AeneasBridgeTrust/
family arms. Full load-bearingness also needs RomImageBinding (committed ROM word == raw) — a named
residual, out of scope, must NOT be silently claimed.

Integration surface: main lakefile.toml requires mathlib(v4.28.0)/LeanRV/Clean/repl. #111 adds
`require aeneas` (vendored a2fcf backends/lean, patched to release mathlib) + new
ZiskFv/Compliance/AeneasBridgeTrust/Extraction.lean importing ProductionM2. RISK: aeneas runtime
sorries (Slice/String) must NOT enter root_soundness closure (spike: LUI path is clean) — V2
axiom-closure baseline will catch any sorryAx. The probe (Route B) tests exactly this feasibility.

4.28 REBUILD DONE (2026-06-26) — make-or-break "labor" item #1 COMPLETE.
Fresh probe at /home/cody/zisk-fv/build/aeneas-428-probe (gitignored shared build area):
- Vendored rc1 aeneas-lean (store hpw9azi.../backends/lean), patched its mathlib require
  → 8f9d9cff and lean-toolchain → v4.28.0. Symlinked probe .lake/packages → THIS worktree's
  built v4.28.0 packages (mathlib 8f9d9cff REUSED, not rebuilt). Hand-wrote
  lake-manifest.json (v1.1.0: aeneas path dep + mathlib + 8 transitive deps at the worktree's
  pinned revs). NO `lake update`. `lake build Aeneas` green (rc1 aeneas builds vs release mathlib).
- DECISIVE TEST PASSED: the COMMITTED rc2-extracted trust/aeneas/ProductionM2.lean compiles
  UNCHANGED against the rc1 aeneas runtime under v4.28.0. NO re-extraction needed — rc1↔rc2
  generated-API drift is a non-issue for this surface. ProductionM2.olean (5.7M) built.
- LuiPins ported (import ProductionM2 not the RvCompleteness harness; emptyExtractContext
  vendored locally) typechecks on v4.28.0 with
  #print axioms = [propext, Classical.choice, Quot.sound] for BOTH lui_static_pins (symbolic)
  and lui_pins_concrete. NO sorryAx / ofReduceBool / trustCompiler — the aeneas-runtime
  Slice/String sorries do NOT leak into the LUI closure (per-theorem isolation holds at 4.28).
  Reproducible recipe = the probe dir itself (lakefile.lean + lake-manifest.json + patched
  aeneas-lean/ + LuiPins.lean).

Checklist:
- [x] Setup: worktree, build/ symlinks, lake exe cache get, tracking files.
- [x] Phase 0a: verify flake aeneas/charon structure (transitive charon? current/target pin).
      DONE 2026-06-26 (#158): aeneas was ac9f1bc5 (rc2) + transitive charon a535e914; override to
      a2fcf1923d moves charon → ed22146b (+ charon/rust-overlay 51390d0b → 5177426d).
- [x] Phase 0b: bump flake.lock aeneas ac9f1bc5 → a2fcf1923d; regenerate ProductionM2.
      DONE 2026-06-26 (#158, commit ba7f8647). `nix flake lock --override-input aeneas …a2fcf…`;
      `AENEAS_UPDATE_TRACKED=1 nix run .#aeneas-production-extract` regenerated ProductionM2
      (rc1↔rc2 drift = COSMETIC ONLY: dropped `set_option maxRecDepth 2048` + doc-comment text;
      no def/sig/term changed). VERIFIED: lake build ProductionM2 + Extraction + full lake build
      green; #print axioms lui_static_pins & lui_extracted_rowMode_pins = [propext, Classical.choice,
      Quot.sound]; `nix run .#aeneas-production-extract-check-tracked` PASS (deterministic);
      V1 + V2 trust gates ALL CHECKS PASSED. Plus commit fb2476c0: nix/aeneas-lean.nix +
      populate wiring (build/aeneas-lean from pinned a2fcf, toolchain/mathlib-patched; output
      byte-identical to the working runtime) — CI populate for #158. Commit 54ac429f: cleared a
      pre-existing zero-sorry-gate false positive (bare `sorry` in Extraction.lean comment).
- [x] 4.28 aeneas-world rebuild (labor #1): rc1 aeneas-lean vendored+patched; hand-edit manifest
      (NO lake update); ProductionM2 cross-compat confirmed (no re-extraction); LuiPins green +
      axioms clean on v4.28.0. Persisted in build/aeneas-428-probe.
- [x] Phase 0c (MAIN wiring) DONE (2026-06-26): main lakefile.toml gains `require aeneas`
      (path build/aeneas-lean, gitignored symlink → shared /home/cody/zisk-fv/build/aeneas-lean)
      + `lean_lib ProductionM2` (srcDir trust/aeneas); lake-manifest.json gains the aeneas path
      pkg entry (NO lake update). `lake build ProductionM2` green. New
      ZiskFv/Compliance/AeneasBridgeTrust/Extraction.lean (namespace ZiskFv.Compliance.Extraction)
      ports the sound LUI helpers/store_reg_pins/lui_static_pins verbatim, adds the @[reducible]
      mainExtractedRowOfZiskInst projection (uses Aeneas `.val`, NOT `.toNat`/`.toInt`) + the
      MainExtractedRow bridge lui_extracted_rowMode_pins. `lake build` of the module green;
      #print axioms for lui_static_pins AND lui_extracted_rowMode_pins = [propext, Classical.choice,
      Quot.sound]. CI repro depends on eth-act/zisk-fv#158 (populate provides build/aeneas-lean).
- [ ] Phase 0d: update boundary gates; verify #eval LUI pins + no sorryAx on probe.
- [x] Phase 1: AeneasBridgeTrust/Extraction.lean + LUI pilot (done in Phase 0c).
- [x] Phase 2: uniform static pins across all 63 ops — DONE 2026-06-26 (commit 8433fe47).
      Split Extraction.lean into Extraction/{Helpers,ControlUType,Branch,RegisterOp,Immediate,
      LoadStore,Precompiled}.lean (all namespace ZiskFv.Compliance.Extraction; shared helpers in
      Helpers ONCE: projection + frame/store/op_zisk/bind/i32/numBits). Each of the 63 RV64IM
      opcodes gets <op>_static_pins (facts on zib.i) + <op>_extracted_rowMode_pins (lift onto
      mainExtractedRowOfZiskInst). Opcode->entry mapping follows the REAL dispatcher
      lower_rv64im_single_row_input (NOT the reference files' assumptions): register shifts via
      create_register_op_typed; loads via load_op_typed; stores via store_op_typed; ADDI/XORI/ORI
      via immediate_op_or_x0_copyb_typed; FENCE via nop. Proved 4 NEW entry points the references
      lacked (nop, immediate_op_or_x0_copyb_typed, load_op_typed/store_op_typed +reg_offset). All
      sound: #print axioms = [propext, Classical.choice, Quot.sound] (spot-checked auipc/add/mul/
      div/beq/addi/slli/lb/sb/copyb/sll). Full `lake build` green (9012 jobs); V1 gate ALL PASS.
      Honest side-conditions kept: AUIPC/JAL/JALR store_pc=true needs rd-cast≠0; ADDI/XORI/ORI
      op/ext/m32 need i.rs1≠0. ZiskFv.lean imports the aggregator → in main build. NOT yet wired
      into stepStrong_*/root_soundness.
- [ ] Wiring swap (root_soundness consumes these pins) + verification + residual docs.

Key reference: spike memory
~/.claude/projects/-home-cody-zisk-fv/memory/project_aeneas_discharge_blocked.md
— full reproducible Phase-0 recipe + the R1 NO-GO-via-cheap-tactics warning.

Env note: build/ subdirs symlinked to /home/cody/zisk-fv/build (shared, never committed).
