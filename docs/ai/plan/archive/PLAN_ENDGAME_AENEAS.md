# Plan: ENDGAME AENEAS — discharge `aeneasBridgeTrust` by wiring the extracted transpiler

Status: READY FOR EXECUTION. Base: `origin/main` at `1781edeb` (PR #93, tracked
ProductionM2) or later. Parent metaplan: `docs/ai/plan/ENDGAME_ROADMAP.md`. This
is a sibling/follow-on to P4: its final discharge composes with P4's
`AcceptedTrace`/`mainOfTable`/`ProgramBinding` spine, but its infrastructure (PRs
1–2, 5) is independent and can start now. Reviewer: the plan author — open each PR
per protocol and STOP.

**Read §0 before anything. The user's framing ("get rid of the Aeneas trust
assumption") is not literally achievable, and the plan must not pretend it is.**

---

## §0. What this phase actually does — the honest framing

`aeneasBridgeTrust` is the Rust→circuit row-lowering boundary: per-opcode it
asserts the committed Main AIR row has the shape ZisK's transpiler would produce
(e.g. `.beq ⇒ is_external_op=1 ∧ op=OP_EQ ∧ m32=0 ∧ set_pc=0 ∧ store_pc=0 ∧
jmp_offset2=4`). Today it is a **`Prop` hypothesis** `h_bridge : env.aeneasBridgeTrust`
on the global theorem (`Compliance.lean:97`), **not an axiom** — the project's
project-axiom closure is already 0. So "getting rid of it" means **discharging a
hypothesis**, and the honest question is *where the trust goes*.

**This phase CANNOT eliminate Rust↔Lean trust.** What it does:

1. **Discharge the hypothesis** — import the Aeneas-extracted model of ZisK's
   *real* transpiler (`trust/aeneas/ProductionM2.lean`, the extraction of
   `lower_rv64im_single_row`) into main Lake and PROVE `aeneasBridgeTrust` from it
   (the discharge chain `extractedRow equalities → *OfExtractedShape →
   aeneasBridgeTrust` is already fully built for all 63 arms; see §1). The 63
   hand-asserted per-arm bridge facts become **consequences of a model of the
   actual Rust**.
2. **Reduce + name the residual** — replace the 63 per-arm `aeneasBridgeTrust`
   hypotheses with **one named premise**: "the committed ROM equals the extracted
   transpiler's lowering of the program" (the ROM-population binding). This is a
   genuine, measurable shrink of the caller-burden bridge surface (122 ledger
   lines today) and preserves 0 axioms (it is a premise, not an axiom).
3. **Validate the residual** — add a Rust-side differential test (real ZisK Rust
   lowerer vs `ProductionM2` on an RV64IM corpus), the counterpart to #77's
   Sail-side test, so the Aeneas model is checked against real behavior, not just
   trusted.

**What is newly relied upon (state this plainly; do NOT bury it):**
- **Charon + Aeneas translation faithfulness** — two unverified compilers; a
  *larger, less-reviewable* trust surface than the hand-asserted Lean facts it
  replaces. Mitigated (not removed) by PR 5's differential test.
- **The submodule pin** — `ProductionM2` is extracted from `codygunton/zisk`
  @ `4148c25e` (a fork + "extraction-only patches"), which is **NOT** the same
  commit as `flake.lock`'s `zisk-src @ b632745` (upstream v0.17.0). Nothing
  currently ties the fork to upstream; the patches are undescribed. PR 5 closes
  this.
- **The ROM-population binding** (`program i = transpiler(program i)`) — the
  prover loaded the ROM from the real transpiler. Not provable in Lean (the
  ROM-population Rust is not modeled); it is the irreducible relocated trust,
  carried as the one named premise.

**Honest one-liner for the trust ledger / PR bodies:** *This discharges
`aeneasBridgeTrust` by proving it from an imported Aeneas model of ZisK's real
transpiler, trading 63 hand-asserted Lean row facts for one named ROM-population
premise plus Charon/Aeneas faithfulness and the fork pin — a genuine
auditability/source-coupling win and a measurable caller-burden shrink, validated
by a new Rust-side differential test, but NOT an elimination of Rust↔Lean trust.*

If §0 is not reflected verbatim-in-spirit in the PR bodies, the phase has
overclaimed (the recurring failure mode here).

---

## §1. Verified groundwork (from the Aeneas survey; confirm with `rg`, flag drift)

All citations `origin/main`. The local working tree is behind origin — worktree
from origin/main + `lake exe cache get` first.

**The discharge chain is ALREADY COMPLETE — the only gap is producing a real
`MainRowProvenance`.**
- `OpEnvelope.aeneasBridgeTrust` (`ZiskFv/Compliance/AeneasBridgeTrust.lean:32`):
  per-arm row-shape predicate.
- 63 `OpEnvelope.<op>OfExtractedShape` builders + 63
  `aeneasBridgeTrust_<op>OfExtractedShape` theorems (`AeneasBridgeTrust.lean:483+`)
  prove `aeneasBridgeTrust` PURELY from a `MainRowProvenance` + its `extractedRow`
  field equalities, via the projection lemmas in `RowProvenance.lean` (pins,
  control, RowMode). Complete for all 63 arms.
- `MainRowProvenance` (`RowProvenance.lean:123`) and `MainExtractedRow` (`:48`,
  17 fields) are currently **only ever assumed** — never constructed;
  `MainExtractedRow` is never instantiated with concrete values. `ExtractedConst.*`
  (`:68`) are plain in-Lake Nat literals, NOT imported from ProductionM2.
- `h_bridge : env.aeneasBridgeTrust` is consumed once, as the global theorem's
  binder #4 (`Compliance.lean:97`; `baseline-global-theorem-binders.txt:5`),
  discharged by `exact h_bridge`.

**The source exists and maps cleanly.**
- `trust/aeneas/ProductionM2.lean` (~4967 lines, on main via #93, gitignored
  twin under `build/aeneas-production-extraction/`): Aeneas extraction of ZisK's
  real `lower_rv64im_single_row` transpiler. Terminal:
  `aeneas_extract.extract_<op>_from_inst (i) : Result ZiskInstExtract` (e.g.
  add `:3694`, beq `:4596`) and `extract_transpile_rv64im_raw (raw) : Result
  Rv64imTranspileExtract` (`:3648`). Output `ZiskInstExtract` (`:883`).
- `ZiskInstExtract` maps field-by-field to `MainExtractedRow` modulo
  `U8/U64→Nat` (`.toNat`), `I64→Int` (`.toInt`), `Bool` identity. The 17-field
  alignment is already script-enforced (`scripts/aeneas-production-extract.sh:162`).
- **NOT imported by main Lake** — fenced off by a Lean-toolchain mismatch
  (`flake.nix:50-52`: Aeneas pinned separately, "kept out of the main Lean build
  until the Lean-toolchain mismatch is resolved"). THIS IS THE GATING BLOCKER
  (§4 PR 1).

**The half-built bindings.**
- `romSpec_of_mainWithRomAndMemBus_constraints` (`AirsClean/Main/Circuit.lean:406`,
  axiom-free) proves: committed Main row's ROM tuple = `program i` for some `i`.
  This is the committed-row↔program half — EXISTS.
- The other half, `program i = romMessageOf(transpiler output)`, is the
  ROM-population binding — does NOT exist in Lean; it is the relocated trust
  (§0). `program : Fin n → ZiskRomMessage FGL` is an opaque parameter.
- `Valid_Main` in the canonical theorems is a FREE column bundle; `MainRowProvenance`
  is FREE. Connecting them to the circuit witness (so `row_eq` is proven not
  assumed) is the `Valid_Main ↔ circuit` identification — shared with P4's
  `mainOfTable`/`AcceptedTrace` (compose with P4).

**The existing honest mechanism (from #92 closed / #93 merged — reuse it).**
- Decision encoded by #92→#93: **regenerate-and-diff a checked-in canonical
  `ProductionM2.lean`** (`.#aeneas-production-extract-check-tracked`, CI job
  `proofs.yml:78`), + syntactic gates: `check-aeneas-production-boundary.py` (the
  extraction wrappers delegate to the same `lower_rv64im_single_row` as production
  `convert` — internal-consistency only), `check-aeneas-generated-bridge-manifest`
  (the 63 `*EvidenceMatches` predicate↔extract-fn manifest), `check-no-checked-in-
  aeneas-artifacts.sh` (exactly `ProductionM2.lean` tracked, nothing else).
- The staged harness (`build/.../lean-check/`) `native_decide`-checks the
  `ExtractedConst` constants against real Aeneas output — but OUT OF LEAN, on the
  Aeneas toolchain. The documented next step is exactly this plan: import + prove
  in main Lake.
- `rv64im_completeness` is proven against an ABSTRACT `Rv.Interface`
  (`Completeness/Rv.lean`) — its Aeneas facts are assumed hypotheses, not derived.
  This phase can also instantiate that interface for real (stretch).

**The residual-trust docs.** `trust/trusted-base.md` classes this as the "Aeneas
row-lowering condition" (0/0, "discharge by importing generated Aeneas Lean"),
bucket (b) in `trust/envelope-burden-audit.md`. Extraction faithfulness is already
declared "part of the project premise but outside the Lean axiom ledger."

---

## §2. Design decisions (FIXED — do not relitigate)

1. **Import strategy: minimal-shim first.** `ProductionM2.lean` uses only a small
   Aeneas surface (`Std.U8/U64/I64`, `Result`/`ok`/`fail`, `do`, a few attrs).
   PR 1 tries, in order: (a) vendor a minimal toolchain-compatible `Aeneas.Std`
   shim so ProductionM2 elaborates in main Lake WITHOUT the full Aeneas dep or a
   toolchain bump; (b) if the generated file needs more, regenerate it against the
   project toolchain if Aeneas supports it; (c) toolchain bump (last resort —
   touches Mathlib pin). If none work, FALLBACK to the export/validate-only outcome
   (§4 PR 1 go/no-go). Do not import the full Aeneas library + bump blindly.
2. **The ROM-population binding is ONE named PREMISE, never an axiom.** It composes
   with P4's `ProgramBinding`: refine that premise to "committed ROM =
   `romMessageOf (toMainExtractedRow (extract_<op_i>_from_inst (decode i)))`."
   Preserves 0 axioms. It is the single relocated-trust object; everything else is
   derived.
3. **`aeneasBridgeTrust` is DISCHARGED, not kept.** After PR 4, the global/trace
   theorem no longer takes `h_bridge`; it takes the ROM-population premise (folded
   into ProgramBinding) and derives the 63 arms' bridge facts via the existing
   `*OfExtractedShape` builders fed the constructed `MainRowProvenance`.
4. **Validation is in scope (PR 5).** "Get rid of the assumption" honestly requires
   validating the model, not just relocating trust. PR 5 adds the Rust-side
   differential test + ties the fork pin to upstream v0.17.0. Without PR 5 the
   phase is incomplete.
5. **Reuse the #93 regenerate-and-diff mechanism.** Do not fork a side workspace;
   extend the tracked-artifact + manifest + boundary gates.

---

## §3. Hard invariants + guardrails (every PR; violations fail review)

- ZERO new `axiom`/`sorry`/`opaque`/`partial def`/`unsafe def`/`native_decide`
  in `ZiskFv/`. Global project-axiom closure stays 0. (ProductionM2 itself must
  stay theorem/axiom/sorry-free — the existing extract script already greps for
  this; keep that gate.)
- **No overclaiming.** The §0 honest framing appears in every PR body. Never write
  "eliminates Aeneas trust" or "removes the assumption" unqualified; the verb is
  "discharge the hypothesis + relocate/validate/minimize the residual."
- **The ROM-population binding is a named premise, not an axiom**, and it is the
  ONLY new trust object. If a PR needs a second trust object, STOP (CRITICAL
  REPORTING RULE): name it, justify it against an existing `trust/trusted-base.md`
  class with a citation, get reviewer sign-off before proceeding.
- **CRITICAL REPORTING RULE for the toolchain spike (PR 1):** if ProductionM2
  cannot be made to elaborate in main Lake by any §2.1 route, STOP and report the
  precise blocker; switch to the export/validate-only fallback (keep `h_bridge` as
  a premise, but back it with PR 5's differential test + the manifest) rather than
  faking an import.
- **Anti-laundering metric:** PR 4 MUST shrink the bridge caller-burden — the
  `bridge`/`row_shape` ledger lines (`baseline-caller-burden.txt`,
  `baseline-wrapper-caller-burden.txt`) drop, replaced by the one ROM-population
  premise; the global-theorem-binder baseline shows `h_bridge` gone. Paste the
  diffs. A net-zero PR 4 laundered.
- Reuse, don't duplicate: extend `check-aeneas-production-boundary.py`,
  `check-aeneas-generated-bridge-manifest`, the regenerate-diff CI. Don't edit
  `trust/forbidden-*.txt` / `allowed-axiom-files.txt` without CODEOWNER sign-off
  (importing ProductionM2 may need an `allowed`/boundary update — flag it).
- Worktrees from origin/main; `lake exe cache get` first; green baseline before
  edits. PR protocol: open yourself, first line `Queued for Claude review — do not
  merge.`, sections Summary/Scope/Verification/Notes + §7 self-check, then STOP.
  Sub-agent prompts carry the CLAUDE.md anti-laundering principle verbatim.

## Verification block (run before every PR)
```bash
lake build
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
nix run .#test
nix run .#aeneas-production-extract-check-tracked
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
git diff origin/main -- trust/
```

---

## §4. The PRs (6; toolchain spike front-loaded)

### PR 1 — Toolchain/import SPIKE: can `ProductionM2` elaborate in main Lake? (go/no-go)

The gating blocker. Output is a decision + the minimal import, OR a documented
fallback. This PR is allowed to be mostly investigation + a small landing.

- [ ] Determine the exact Lean-toolchain delta between the project (`lean-toolchain`)
      and Aeneas (the pinned `aeneas` flake input). Document it.
- [ ] Try §2.1 route (a): vendor a minimal `Aeneas.Std` shim (the scalar types +
      `Result` monad + the few attrs ProductionM2 uses) under e.g.
      `ZiskFv/Aeneas/Shim.lean`, and get a 1-function slice of ProductionM2 (e.g.
      `extract_add_from_inst`) to elaborate + reduce in main Lake. If the shim
      suffices, that is the import path.
- [ ] If (a) is insufficient, evaluate (b) regenerate-against-project-toolchain
      and (c) toolchain bump; pick with a written rationale. CRITICAL REPORTING
      RULE: if all fail, STOP — switch to export/validate-only (deliver PR 5's
      differential test + manifest as the honest outcome, keep `h_bridge`).
- [ ] Land the import mechanism (shim + import of ProductionM2 or a slice) behind
      the existing gates; update `check-no-checked-in-aeneas-artifacts.sh` /
      `allowed`/boundary as needed (flag CODEOWNER bits). Confirm the regenerate-
      diff CI still passes.
- [ ] PR body: the toolchain verdict + chosen route + the §0 framing. Verification
      block.

### PR 2 — `toMainExtractedRow` adapter + per-opcode evaluation lemmas

- [ ] `toMainExtractedRow : ZiskInstExtract → MainExtractedRow` (the `.toNat`/
      `.toInt`/`Bool` field map; drop the 6 extra `ZiskInstExtract` fields).
- [ ] Result-monad totality: per opcode, `extract_<op>_from_inst i = .ok r` on the
      in-scope decoded inputs (no `fail`). Concrete-input form by `decide`/`simp`;
      keep `native_decide` OUT (guardrail) — use `decide`/`norm_num`/`simp` on the
      extracted defs.
- [ ] The 63 evaluation lemmas: `(toMainExtractedRow r).<field> = <ExtractedConst
      value>` for each opcode's decode-shape fields — these REPLACE the staged
      harness `native_decide` checks with in-Lean proofs against the imported
      ProductionM2. (E.g. beq: `op=opEq, isExternalOp=true, m32=false, setPc=false,
      storePc=false, jmpOffset2=4`.)
- [ ] Verification block; gates green; open PR.

### PR 3 — The `MainRowProvenance` producer + the ROM-population premise (composes with P4)

- [ ] `romMessageOf : MainExtractedRow → ZiskRomMessage FGL` packing the 11 ROM
      slots incl. `flags = packFlags …`; a lemma that its `flags` matches the
      circuit's `rom_flags` recomposition (`Circuit.lean` packFlags / `main.pil:483`)
      AND `ZiskInst::get_flags()` bit layout (`zisk_inst.rs:289`). Bit-layout
      mismatch silently breaks the join — prove the equality.
- [ ] The ROM-population premise (ONE named binder, §2.2): `RomBindsTranspiler
      program := ∀ i, program i = romMessageOf (toMainExtractedRow
      (extract_<op_i>_from_inst (decode i)))`. Document it as the single relocated
      trust object (§0) in `trust/trusted-base.md` + the bucket audit, citing the
      Rust delegation test (`aeneas_extract.rs` `extraction_starts_match_production_
      convert_for_single_row_opcodes`) and PR 5's differential test.
- [ ] `mkMainRowProvenance`: from `romSpec_of_mainWithRomAndMemBus_constraints`
      (committed row = `program i`) + `RomBindsTranspiler` + `romBoolSpec` (flag
      booleanity), construct `MainRowProvenance m r_main` with `extractedRow :=
      toMainExtractedRow (extract_<op_i>_from_inst …)`, proving all ~26 field
      equalities. Uniform across opcodes.
- [ ] `Valid_Main ↔ circuit` identification: discharge `row_eq` for real. PREFER
      consuming P4's `mainOfTable`/`AcceptedTrace` spine (compose); if P4 not yet
      landed, take `m`/`row_eq` from the circuit witness here and reconcile later.
      Coordinate with the P4 stream to avoid divergence.
- [ ] Verification block; open PR. PR body: the ROM-population premise is THE
      relocated trust; everything else derived.

### PR 4 — Discharge `aeneasBridgeTrust` (the metric-moving PR)

- [ ] Feed the constructed `MainRowProvenance` (PR 3) + the evaluation lemmas
      (PR 2) into the 63 `*OfExtractedShape` builders, proving `aeneasBridgeTrust`
      for each arm from ProductionM2 — no caller-supplied bridge facts.
- [ ] Remove `h_bridge : env.aeneasBridgeTrust` from the global/trace theorem (or
      reduce it to the single `RomBindsTranspiler` premise). Update the dispatchers.
- [ ] Regenerate baselines: `baseline-global-theorem-binders.txt` shows `h_bridge`
      GONE (replaced by the ROM-population premise); `baseline-caller-burden.txt` /
      `baseline-wrapper-caller-burden.txt` `bridge`/`row_shape` lines DROP. Paste
      the diffs — this is the audit evidence of the reduction. Canonical
      `equiv_<OP>` per-opcode counts: confirm net shrink (the 63 bridge hyps gone).
- [ ] Closure print stays 0 axioms. Verification block; open PR.

### PR 5 — Validate the residual: Rust-side differential test + fork↔upstream pin

- [ ] Differential test (the #77 counterpart for the Rust side): run the real ZisK
      Rust lowerer (`Riscv2ZiskContext::convert` / `lower_rv64im_single_row`) and
      the extracted `ProductionM2` on a corpus of RV64IM raw words; compare the
      `ZiskInstExtract` row outputs. Wire as a flake target + scheduled/main-push
      CI (mirror the extract-check job). This validates Aeneas/Charon faithfulness
      on real inputs — the trust PR 4 relocated.
- [ ] Tie the fork pin to upstream: extend `check-aeneas-production-boundary.py`
      (or add a check) so `codygunton/zisk@4148c25` is compared against upstream
      v0.17.0 (`flake.lock` `zisk-src`) — at minimum, diff the "extraction-only
      patches" and assert they touch only `#[cfg(feature="aeneas_extract")]` /
      documented constants, with the diff committed as the audit surface.
- [ ] Document both in `trust/aeneas/README.md`. Verification block; open PR.

### PR 6 — Honest trust-ledger + residual documentation + closeout

- [ ] `trust/trusted-base.md`: update the "Aeneas row-lowering condition" class —
      the per-arm hypotheses are discharged; the residual is now {Charon/Aeneas
      faithfulness (validated by PR 5), the fork pin (checked by PR 5), the
      `RomBindsTranspiler` premise}. State the §0 honest framing verbatim.
- [ ] `trust/envelope-burden-audit.md`: `aeneasBridgeTrust` bucket-(b) entry →
      discharged; the ROM-population premise is the new named bucket-(b) entry.
- [ ] `ENDGAME_ROADMAP.md`: record the Aeneas wiring DONE; note the residual.
      Comment the discharge on the relevant issue(s).
- [ ] (Stretch) instantiate `Rv.Interface` (`Completeness/Rv.lean`) for real from
      ProductionM2, discharging `rv64im_completeness`'s assumed Aeneas facts.
- [ ] Verification block; open PR.

---

## §5. Definition of Done (the reviewer runs these)
- [ ] `ProductionM2` (or its needed slice) is imported by main Lake and elaborates;
      the import is behind the regenerate-diff gate. (Or: documented export/validate
      fallback with PR 5 delivered.)
- [ ] `git grep 'h_bridge' ZiskFv/Compliance.lean` shows it GONE from the global
      theorem (or reduced to `RomBindsTranspiler`); `baseline-global-theorem-binders.txt`
      no longer lists `h_bridge : env.aeneasBridgeTrust`.
- [ ] `baseline-caller-burden.txt` `bridge`/`row_shape` lines net-DROPPED; diff
      pasted in PR 4 body.
- [ ] No new axioms/sorry/native_decide; closure print = 0. The ROM-population
      premise is a binder, not an axiom.
- [ ] A Rust↔ProductionM2 differential test runs in CI; the fork↔upstream patch
      diff is committed/checked.
- [ ] `trust/trusted-base.md` + the bucket audit state the §0 honest residual; no
      PR body claims trust elimination.

## §6. The residual after this phase (for the trust ledger)
Discharged: 63 hand-asserted `aeneasBridgeTrust` row facts → proven from an
imported, differentially-validated Aeneas model of ZisK's real transpiler.
Remaining (named, documented, outside the Lean axiom ledger): (1) Charon+Aeneas
translation faithfulness (validated by the differential test); (2) the
`codygunton/zisk` fork pin = deployed Rust (checked against upstream v0.17.0);
(3) the `RomBindsTranspiler` premise (the prover loaded the ROM from the real
transpiler). Net: 63 opaque hand-asserted facts → 1 named premise + a validated
model. Auditability and source-coupling improve substantially; Rust↔Lean trust is
relocated and validated, not eliminated.

## §7. Anti-laundering / honesty self-check (every PR body)
1. The §0 honest framing is present; no trust-elimination overclaim.
2. The only new trust object is the named `RomBindsTranspiler` premise (a binder,
   not an axiom); it fits the existing extraction-trust class with citation.
3. PR 4 shows the caller-burden bridge surface net-SHRANK + `h_bridge` gone.
4. Closure print = 0; ProductionM2 import added no axiom/sorry/native_decide.
5. The residual (Aeneas faithfulness + pin + ROM-binding) is documented and (PR 5)
   validated, not silently relied upon.

## Log
(append one line per milestone; do not expand the plan body)
