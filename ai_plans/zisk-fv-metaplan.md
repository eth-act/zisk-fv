# ZisK Formal Verification — Metaplan

## Revision 2026-04-20 (post-Phase 0)

Phase 0 executed successfully (see `ai_plans/zisk-fv-phase-0.md` status section). The following facts update assumptions that matter for Phase 1; no existing phase text below is rewritten.

- **Pilout `Constant.value` bytes are big-endian, variable-length, leading-zero-stripped.** The `.proto` does not document this; verified empirically via `BinaryAdd` extraction. Future protobuf consumers must assume the same for `FixedCol` / `PeriodicCol` payload bytes until verified otherwise.
- **`LeanZKCircuit.OpenVM.Circuit` is field-polymorphic.** Phase 1 Task 2 (typeclass/structure analogue) **does not need a new shim over Goldilocks** — the existing typeclass works unchanged. Retain the task as ZisK-specific scaffolding, but don't re-derive the interface.
- **Operand-kind coverage is the critical path, not Plonky3-vs-PIL2 translation.** Priority order for extending `zisk-pil-extract`: `FixedCol`, `Challenge`, `AirValue`, `PeriodicCol`. With those four, every `BinaryAdd` constraint and almost every Main-AIR constraint renders.
- **Constraint-kind fidelity must be added in Phase 1.** The extractor currently flattens `everyRow` / `firstRow` / `lastRow` / `everyFrame` into a single `constraint_N` shape. Phase 1 needs distinct predicates (e.g. `constraint_N_first_row`) so bridging proofs can quantify over the correct domain.
- **Goldilocks primality costs ~386s via `native_decide` (cold).** Acceptable with cached `.olean`s; consider a faster procedure (Pratt/Pocklington certificate) before CI scale-out.
- **`BinaryAdd` witness-column layout (verified):** stage 1 cols 0..9 = `a[0], a[1], b[0], b[1], c_chunks[0..3], cout[0], cout[1]`; stage 2 cols 0..2 = `gsum, im[0], im[1]`. Use the extractor's `-- witness column names:` header as the canonical name-to-index resolver in future Airs/ files.

---

**Goal.** Produce Lean 4 proofs, for every RV64IM opcode, that ZisK's implementation (as extracted from `pil/zisk.pilout`) is equivalent to the official Sail RISC-V specification (via `NethermindEth/sail-riscv-lean`'s `LeanRV64D` module).

**Pattern.** Adapts the five-layer pipeline of `openvm-fv` (Extraction → Airs → Constraints → Spec → Equivalence, with `RV64D/` providing Sail-equivalent pure specs) to ZisK's architecture: PIL2 constraints, Goldilocks field, monolithic Main AIR plus secondary state machines connected via an operation bus.

**Zicclsm** extension is explicitly deferred — not yet stable in ZisK or the Sail-Lean extraction.

---

## Trust model (locked)

Per phase-planning decision:

- **Sail RISC-V spec** is trusted (`LeanRV64D`).
- **PIL2 → Lean extractor** is trusted (does not prove its own soundness against `zisk.pilout`).
- **RISC-V → Zisk transpiler** (`core/src/riscv2zisk_context.rs`, `core/src/elf2rom.rs`) is trusted via an axiomatized Lean contract.
- **Empirical check:** every proven opcode must also pass a **golden-trace test** — a Rust harness runs ZisK on a probe program exercising the opcode, dumps the witness row, and a Lean `#eval` verifies the proven constraints hold on that concrete witness. Catches extractor / transpiler bugs without proving them.
- Trusted base lives in `ZiskFv.Trusted` and is exhaustively documented in `docs/fv/trusted-base.md`.

---

## Phase 0 — Extractor spike  · **CLOSED 2026-04-20**

Status: invariants met. See `ai_plans/zisk-fv-phase-0.md` status section for the post-execution gap inventory (1, 2, 4 fixed; 3, 5, 6 accepted and carried forward).

**Purpose.** Burn down the highest-risk unknown: whether `zisk.pilout` can be translated into Lean in a shape compatible with per-opcode reasoning.

**Tasks.**
1. Inspect `pil/zisk.pilout` format. Decide between: parsing the compiled artifact directly, running Polygon's PIL compiler in-tree, or scraping `pil/*.pil` source via an existing `pil2-proofman` tool.
2. Hand-translate (not automated) the constraints for **one row of the Main AIR for one opcode flag path**, plus its bus-connection to **one** secondary state machine call.
3. Build a minimal Rust binary `tools/zisk-pil-extract` that emits one `.lean` file containing raw constraints in the shape of `openvm-fv/OpenvmFv/Extraction/*.lean`.
4. Prove one trivial lemma about the extracted constraint (e.g. "some column is boolean"). Not semantic — just pipeline-exercising.

**Invariants at close.**
- `tools/zisk-pil-extract zisk.pilout` runs to completion and emits well-typed Lean.
- `lake build` passes on the emitted file plus the trivial lemma.
- `docs/fv/extractor-notes.md` documents: extractor contract, every observed corner case (multi-row constraints, lookup vs permutation, airvals, polynomial expansion strategy), and what the extractor does **not** yet handle.

**Parallelism.** None. Sequential. Every decision is load-bearing for later phases.

**Introspection gate.** If extractor complexity appears to exceed ~2× the OpenVM equivalent, pivot to a hand-curated subset for Phase 1 while the extractor matures in a background track. Capture the decision in the handoff note.

---

## Phase 1 — Vertical slice on one opcode

**Purpose.** Prove RV64 `ADD` end-to-end through the full pipeline. This is the single most de-risking artifact in the plan; every later opcode is a variation on this one.

**Tasks (Track B — ZisK-side, serial).**
1. `ZiskFv.Fundamentals.Goldilocks` — Goldilocks field analogue of `openvm-fv/OpenvmFv/Fundamentals/BabyBear.lean`.
2. `LeanZKCircuit.PIL2.Circuit` (or vendored `ZiskFv.Circuit`) — the typeclass/structure analogue of OpenVM's `Circuit F ExtF C`, specialized to PIL2 column layout + Goldilocks. Start minimal; grow on demand.
3. `ZiskFv.Fundamentals.Transpiler` — axiomatized RV64 → Zisk-instruction contract. For Phase 1, populate the ADD case only; subsequent phases add cases.
4. `ZiskFv.Airs/Main/` — hand-written mirror of the Main AIR with named column accessors for the ADD path. Model secondary-machine calls as bus-entry interactions from `LeanZKCircuit.Interactions`.
5. `ZiskFv.Airs/Binary/` — similarly for the Binary state machine (which services ADD via the operation bus).
6. `ZiskFv.Extraction/` — output of `zisk-pil-extract` on the Main and Binary AIRs, filtered/scoped to what's needed for ADD.
7. `ZiskFv.Constraints/` — simp-reduction lemmas translating extracted numeric constraints into readable propositions over the Airs.
8. `ZiskFv.RV64D/add.lean` — `PureSpec.AddInput → AddOutput` + equivalence to Sail's `execute_instruction (.RTYPE (r2, r1, rd, rop.ADD))`. Widen `openvm-fv`'s `RV32D/add.lean` from `BitVec 32` to `BitVec 64`.
9. `ZiskFv.Spec.Add` — proves the ADD constraint conjunction implies ADD's opcode-level semantic behavior. This is the first **compositional** proof in the codebase (Main + Binary + operation bus).
10. `ZiskFv.Equivalence.Add` — final theorem: `execute_instruction (.RTYPE (r2, r1, rd, rop.ADD)) state = (bus_effect exec_row mem_row state).2`, zero `sorry`.
11. **Golden-trace harness.** `tools/zisk-fv-harness/`: a Rust crate that runs ZisK on a probe program (`examples/fv-probes/add.rs` or a hand-written RISC-V blob), dumps the witness for the relevant Main and Binary rows as JSON, and emits a Lean `#eval`-ready fixture. `cargo test fv_golden_add` + `lake test ZiskFv.GoldenTraces.Add` confirms the proven constraints hold on that real witness.

**Tasks (Track A — Sail-side, parallel, launched as subagent day 1).**
- Port `openvm-fv/OpenvmFv/RV32D/` to `ZiskFv/RV64D/`:
  - Widen `BitVec 32 → BitVec 64`, `U32 → U64`.
  - Port existing opcode pure-specs and their Sail-equivalence proofs.
  - Stub RV64-only opcodes (-W variants, LD, SD, LWU) with `sorry` — to be filled in Phase 3.
- Track A depends only on `LeanRV64D` + Mathlib. Completely independent of Track B.

**Invariants at close.**
- `theorem equiv_ADD` exported with the standard shape, zero `sorry`.
- `cargo test fv_golden_add` passes.
- `lake test ZiskFv.GoldenTraces.Add` passes.
- Full `lake build` green.
- Track A: `ZiskFv/RV64D/` builds; count of remaining `sorry`s documented in the handoff note.

**Parallelism.** Track B: 1–2 subagents, low parallelism. Track A: 1–2 subagents in background.

**Introspection gate.** With ADD proven, per-opcode effort is measurable. Update the Phase 3 throughput estimate. Identify which proof steps are genuine mathematics vs. boilerplate compilable into macros (analogous to openvm-fv's `alu_non_imm_proof`). If compositional Main + Binary reasoning required proof primitives not present in `LeanZKCircuit.Interactions`, log whether to upstream a PR to `leanzkcircuit` or vendor-and-extend.

---

## Phase 2 — Archetype coverage

**Purpose.** Establish one proof template per proof-shape, so Phase 3 can fan out without rediscovering architecture.

**Tasks.** Prove one representative opcode per archetype. Each yields (a) a zero-`sorry` theorem, (b) a golden-trace fixture, (c) a reusable proof macro, (d) `docs/fv/archetype-<name>.md` documenting the macro's call shape and pre/postconditions.

Archetypes (each with its representative opcode):
- **Branch:** `BEQ` — PC-mutating, no register write, no memory.
- **Jump+link:** `JAL` — PC-mutating, register write, no memory.
- **Load:** `LD` — RV64 memory read, register write, sign/zero extension, alignment handling.
- **Store:** `SD` — RV64 memory write, no register write, alignment handling.
- **Arith via Arith SM:** `MUL` — exercises the Arith state machine via the operation bus, distinct from Binary.
- **-W family:** `SLLW` — validates the RV64 sign-extension-of-32-bit-result pattern.

Order: `BEQ` proved first (smallest new archetype); other five may fan out once the macro discipline is clear.

**Invariants at close.**
- All six archetype opcodes: zero `sorry`, exported theorem, golden trace passes.
- Archetype macros exist, are named consistently, and are documented.
- Track A: all 65 pure-specs complete (no `sorry` on that track anywhere).

**Parallelism.** Medium. BEQ first (serial, to validate macro shape). Remaining five: 3–4 subagents in parallel.

**Introspection gate.** Partition all remaining ~60 RV64IM opcodes into archetypes. If any opcode doesn't fit, either add an archetype here or log it as a Phase 4 outlier. Revise the Phase 3 plan before clearing context.

---

## Phase 3 — Parallel sweep

**Purpose.** Cover the long tail. No new architecture.

**Tasks.** For each remaining RV64IM opcode (~60 opcodes):
1. Author `ZiskFv.RV64D/<op>.lean` pure spec (Track A likely already delivered this).
2. Author `ZiskFv.Spec.<Op>` and `ZiskFv.Equivalence.<Op>` by instantiating the appropriate archetype macro with the opcode-specific fields (opcode value, flag name, operand signature).
3. Add a golden-trace fixture.
4. `lake build` green + golden test passes = done.

**Invariants at close.**
- Every RV64IM opcode has an `equiv_<OP>` theorem, zero `sorry`.
- Full golden-trace matrix passes.
- `lake build` green.

**Parallelism.** High. 6–10 subagents in batches, each owning one opcode. Spot-check by you; `lake build` + golden trace is the hard gate.

**Introspection gate.** Log every opcode whose proof did **not** fit its archetype template cleanly. Those are leads for Phase 4 audit — they often indicate a latent constraint bug, a spec ambiguity, or an archetype gap.

---

## Phase 4 — Audit, harden, export

**Purpose.** Convert "lots of green tests" into a defensible verification artifact.

**Tasks.**
1. Verify every opcode theorem has the uniform shape (`execute_instruction` LHS, `bus_effect` RHS). A lint script checks this mechanically.
2. Eliminate opportunistic axioms introduced during earlier phases; those that remain are documented in `docs/fv/trusted-base.md` with rationale (Sail spec, extractor, transpiler contract, golden-trace harness correctness).
3. Close the Phase 3 outliers (opcodes that didn't fit templates cleanly).
4. Expand golden-trace matrix: each opcode run with ≥3 distinct witness fixtures exercising edge cases (max values, overflow boundaries, zero-register writes, unaligned where relevant, sign-boundary inputs).
5. Top-level `ZiskFv.lean` re-exporting every `equiv_<OP>` theorem plus `ZiskFv.Trusted`.
6. Written `REPORT.md` (analogue of openvm-fv's `REPORT.pdf`) documenting assumptions, coverage, caveats, and known limitations.

**Invariants at close.**
- `lake build` green, zero `sorry` anywhere, zero `axiom` outside `ZiskFv.Trusted`.
- `cargo test fv_golden` exercises every opcode with multiple fixtures.
- Lint script passes.
- `REPORT.md` written, reviewed, merged.

**Parallelism.** Low. Integration and audit.

---

## Cross-phase discipline

- **Phase-boundary invariant gate.** Each phase's invariants must be re-runnable from a clean checkout via a single command: `just verify-phase0`, `just verify-phase1`, … If you can't rerun from scratch, the phase isn't done. The `justfile` is authored in Phase 0 and extended each phase.
- **Phase handoff note.** At close of each phase, write `docs/fv/phase-N-handoff.md` (≤500 words) capturing: what shipped, what differed from the metaplan, what we learned, what the next phase should recalibrate. This is the context-clear replacement for in-head working memory.
- **Auto-memory updates.** At phase close, update `~/.claude/projects/-home-cody-zisk/memory/` so the next-phase agent walks in with accurate context (architecture facts, proof patterns discovered, tooling contracts).
- **Sorry budget = 0 at phase boundaries.** Intermediate files may carry `sorry`, but no file imported by the phase's invariant target may have `sorry` when the phase closes.
- **Metaplan revision protocol.** At every introspection gate, ask: is the downstream plan still right? If not, amend this metaplan in place (this file is the single source of truth) with a dated revision note at the top before clearing context.

---

## Known fragility

Most likely breakage points, in order:

1. **Phase 0 discovers that `zisk.pilout` lacks structure for clean per-opcode extraction.** Mitigation: pivot to extracting from ZisK's Rust constraint builders or from `pil/*.pil` source files.
2. **Phase 1 discovers that compositional Main + Binary reasoning requires proof primitives not in `LeanZKCircuit.Interactions`.** Mitigation: upstream a PR to `leanzkcircuit` or vendor-and-extend. Track upstream coordination explicitly.
3. **Phase 2 discovers a seventh archetype** (compressed instructions, CSR reads, precompile dispatch). Mitigation: add an archetype cycle between Phase 2 and Phase 3 rather than shoehorning into existing macros.
4. **Phase 3 throughput stalls** because opcodes share state (same Main AIR) and subagents collide on common lemmas. Mitigation: batch by archetype with a single owner per archetype, serialize the common-lemma edits.

---

## External coordination (non-blocking)

- **Nethermind / OpenLabs** (`leanzkcircuit`, `sail-riscv-lean`): engage early about (a) a PIL2 backend in `leanzkcircuit`, (b) whether they intend to tackle ZisK themselves. Do not block the plan on their answer — vendoring is always the fallback.
- **0xPolygonHermez** (ZisK team): confirm the Rust-side extractor/transpiler contracts we axiomatize match their intent; coordinate on changes that would affect trust-base stability.

---

## Kickoff

Phase 0 is ready to begin. Next step when starting Phase 0: launch a subagent with the Phase 0 task block as its self-contained prompt; reference this metaplan file for context.
