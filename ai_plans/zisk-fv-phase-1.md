# Phase 1 detailed plan — vertical slice on RV64 ADD

**Parent metaplan.** `ai_plans/zisk-fv-metaplan.md` (Phase 1 section).

## Context

Phase 0 proved that pilout → Lean extraction works and produced a trivial
lemma on one `BinaryAdd` constraint. Phase 1 is the first real verification
artifact: `execute_instruction (.RTYPE (r2, r1, rd, rop.ADD)) state = (bus_effect exec_row mem_row state).2`
with zero `sorry`, over Goldilocks, bridging `Zisk::Main` + `Zisk::BinaryAdd`
via the operation bus.

Every later opcode is a variation on this proof. The metaplan calls Phase 1
"the single most de-risking artifact in the plan" — that's why we prove ADD
end-to-end rather than, say, just Main's opcode dispatch.

Pre-execution reconnaissance (captured in `docs/fv/phase-1-recon.md`, to be
written as Task 0) established:

1. **Main AIR** encodes "this row runs opcode X" with an 8-bit `op` literal
   column (`state-machines/main/pil/main.pil:136`) plus an `is_external_op`
   flag that gates the operation-bus hop. ADD's operands live in
   `a[RC]`, `b[RC]`, `c[RC]` (RC=2 limbs for 64-bit) and the row handshake
   with `BinaryAdd` uses the 11-field bus schema from `pil/operations.pil:144`.
2. **`zisk.pilout`'s Main AIR** has 146 constraints; the current extractor
   renders ~30 and skips ~116 on `FixedCol` / `Challenge` / `AirValue`.
   Extending the extractor is Phase 1's first hard gate.
3. **openvm-fv's ADD chain** is a 6-layer stack — Extraction → Airs (with
   `Valid_<Air>` structures via `#define_subair`) → Constraints (simp-lemma
   bridge `constraint_N_of_extraction`) → `RV32D/add` (pure spec + Sail
   equivalence) → `Spec/BaseALU` (circuit-correctness theorem) →
   `Equivalence/BaseALU` (final theorem, composed via the `alu_non_imm_proof`
   macro). We replicate the shape for RV64.
4. **`LeanRV64D`** exists on `main` of `NethermindEth/sail-riscv-lean` but is
   flagged Sail-auto-translated "work-in-progress". Real risk: we may need
   to write lemmas or port fixes upstream. Track A budget accounts for this.
5. **Golden-trace plumbing is free.** ZisK's SDK exposes
   `ProverClient::get_instance_trace(instance_id, first_row, num_rows, offset)`
   returning `Vec<proofman_common::RowInfo>`. We wire it, we don't build it.
   Pattern: `examples/sha-hasher/host/bin/execute.rs` in the ZisK tree.

## Scope (strict)

**In scope — Track B (ZisK-side, serial):**

- Extractor extensions to cover the ADD-relevant subset of Main + BinaryAdd:
  `FixedCol`, `Challenge`, `AirValue` operand kinds, and distinct emissions
  for `firstRow` / `lastRow` / `everyRow` / `everyFrame` constraint kinds
  (the current flattening into `constraint_N` is a Phase 1 blocker per the
  metaplan revision note).
- `ZiskFv.Fundamentals.Goldilocks` extensions: `NatCast`, `NoZeroDivisors`,
  `U64` coercions, inverses required by the ADD proof (likely 1/2^16, 1/2^32
  for carry reasoning — mirroring BabyBear.lean's inverse helpers).
- `ZiskFv.Fundamentals.Transpiler` — axiomatized RV64 → Zisk-instruction
  contract, ADD case populated. The axiom states: an RV64 RTYPE ADD with
  operands (rs2, rs1, rd) transpiles to a Zisk-instruction row with
  `op = 0x0a`, `a = xreg(rs1)`, `b = xreg(rs2)`, `c = xreg(rd)` written back,
  `flag = 0`, `is_external_op = 1`. Cite `core/src/riscv2zisk_context.rs` as
  the implementation the axiom mirrors.
- `ZiskFv.Extraction/` regenerated: `Main.lean`, `BinaryAdd.lean` covering the
  ADD-relevant constraints with the extended extractor.
- `ZiskFv.Airs.Main`, `ZiskFv.Airs.Binary` — hand-written `Valid_Main` and
  `Valid_BinaryAdd` structures with named column accessors, plus the
  named-constraint layer (the openvm-fv `Constraints/` analogue, inlined
  into `Airs/` or kept separate as `ZiskFv.Constraints.*` depending on size).
- `ZiskFv.RV64D.add` — pure spec + Sail equivalence, widening
  `openvm-fv/OpenvmFv/RV32D/add.lean` from `BitVec 32` to `BitVec 64`.
- `ZiskFv.Spec.Add` — ADD constraint-conjunction ⇒ ADD opcode behavior.
  First compositional proof in the codebase (Main + Binary + bus).
- `ZiskFv.Equivalence.Add` — final theorem `equiv_ADD`.
- `tools/zisk-fv-harness/` — Rust crate using `ProverClient` to run a probe
  program, dump the row that exercises ADD, emit a Lean `#eval` fixture.
- `ZiskFv.GoldenTraces.Add` — Lean fixture + `#eval` check that the proven
  constraints hold on the real witness.
- `justfile::verify-phase1` — new target. Runs extractor unit tests, the
  ADD harness, `lake build`, and the golden-trace fixture check.
- `docs/fv/phase-1-recon.md` (Task 0) and `docs/fv/phase-1-handoff.md`.

**In scope — Track A (Sail-side, parallel, subagent-driven):**

- Port `openvm-fv/OpenvmFv/RV32D/` → `ZiskFv/RV64D/`. Widen `BitVec 32`,
  `U32` → `BitVec 64`, `U64`. Port existing opcode pure-specs + Sail-equivalence
  proofs. Stub RV64-only opcodes (`-W` variants, `LD`, `SD`, `LWU`) with
  `sorry` — filled in Phase 3.

**Explicitly out of scope:**

- Any opcode beyond ADD (Phase 2+).
- Proof macros (`alu_non_imm_proof` analogue) — we hand-write ADD first;
  macros are extracted during Phase 2 archetype coverage, not Phase 1.
- Main AIR constraints unrelated to ADD (continuation-mode constraints,
  memory alignment machinery, precompile dispatch).
- `PeriodicCol`, `ProofValue`, `AirGroupValue`, `PublicValue`, `CustomCol`
  operand kinds (no ADD constraint uses them; revisit when needed).
- Non-trivial primality replacement for Goldilocks (stays on `native_decide`;
  ~386s cold is tolerable while Phase 1 is local-dev).

## Execution order

### Track B — serial

**Task 0: Recon doc.** Write `docs/fv/phase-1-recon.md` (≤600 words) capturing
the four reconnaissance findings above with exact file:line citations. This
is the frozen context the rest of the plan references.

**Task 1: Extractor — constraint-kind differentiation.** Today the extractor
emits a single `constraint_N` regardless of `firstRow` / `lastRow` /
`everyRow` / `everyFrame`. Change `render_constraint` in
`tools/zisk-pil-extract/src/main.rs` to emit:
- `constraint_N_every_row` for `EveryRow`
- `constraint_N_first_row` for `FirstRow`
- `constraint_N_last_row` for `LastRow`
- `constraint_N_every_frame_<min>_<max>` for `EveryFrame(offsetMin, offsetMax)`

Update the hand oracle `BinaryAdd.hand.lean` to match (all BinaryAdd
constraints are `EveryRow`; the rename is mechanical). Update `Spike.lean`
to reference the new name. Add a unit test asserting the dispatch.

**Task 2: Extractor — `FixedCol`, `Challenge`, `AirValue`.** Add three
`OperandKind` match arms in `render_operand`:
- `FixedCol { idx, row_offset }` → `Circuit.preprocessed c (column := idx)
  (row := row) (rotation := row_offset)`
- `Challenge { stage, idx }` → `Circuit.challenge c (index := <stage*W + idx>)`
  where `W` is the max challenges per stage (inspect `pilout.num_challenges`;
  the index layout mirrors openvm-fv's `challenge` typeclass member)
- `AirValue { idx }` → a new `Circuit.air_value c (index := idx)` or the
  `exposed` field if repurposed (inspect openvm-fv to confirm — probably
  maps to `LeanZKCircuit.OpenVM.Circuit.exposed`)

For each kind, add `format_basefield`-style unit tests for corner cases and
one golden-file regression that the Main AIR extraction no longer aborts on
the ADD-adjacent constraints.

**Task 3: Extract Main AIR.** Run the extended extractor with
`--air Main --only <ADD-subset-indices>` (the subset is enumerated in the
recon doc). Write the hand oracle `ZiskFv/Extraction/Main.hand.lean` from
the `main.pil` source, matching the extractor's rendering rules (same
protocol as Phase 0's BinaryAdd oracle). Extend `justfile::verify-phase1`
to run the same regenerate-and-diff gate for Main.

**Task 4: Re-extract BinaryAdd with all 9 constraints.** With `Challenge`,
`FixedCol`, `AirValue` support, all 9 BinaryAdd constraints should render.
Regenerate `BinaryAdd.lean`, update the hand oracle correspondingly, confirm
`verify-phase0` (which becomes a subset of `verify-phase1`) still passes.

**Task 5: `ZiskFv.Fundamentals.Goldilocks` extensions.** Port the bits of
openvm-fv's `BabyBear.lean` that ADD's proof actually uses. Expect:
`NatCast FGL`, `NoZeroDivisors FGL` (mirror openvm-fv's
`Fin.noZeroDivisors_of_prime` local instance), `U64`-style coercions for
64-bit lane values, and inverses `inv_2^16` / `inv_2^32` with the
`inv_X_eq_X_{lr,rl}` simp lemma shape. Cite each new lemma against its
BabyBear counterpart.

**Task 6: `ZiskFv.Fundamentals.Transpiler`.** Axiomatize the RV64 ADD
transpilation contract:

```lean
axiom transpile_ADD
    (rs1 rs2 rd : Fin 32) (state : RV64State) :
    ∃ (row : ZiskInstructionRow),
      row.op = 0x0a ∧
      row.a = (state.xreg rs1).toU64 ∧
      row.b = (state.xreg rs2).toU64 ∧
      row.is_external_op = 1 ∧
      row.flag = 0 ∧
      transpile (.RTYPE rs2 rs1 rd rop.ADD) state = some row
```

Cite `/home/cody/zisk/core/src/riscv2zisk_context.rs` for the concrete
encoding this mirrors. Document in `ZiskFv.Trusted` per the metaplan's trust
model.

**Task 7: `Valid_BinaryAdd` structure + named constraints.** Mirror
`openvm-fv/OpenvmFv/Airs/Alu/BaseAluCoreAir.lean` at
`ZiskFv/Airs/Binary/BinaryAdd.lean`:
- Declare a structure `Valid_BinaryAdd F ExtF` with named accessors
  `a_0 a_1 b_0 b_1 c_chunks_0 … c_chunks_3 cout_0 cout_1` plus the
  bus columns (`gsum`, `im_0`, `im_1`).
- Define named-constraint predicates (`boolean_cout_0`, `carry_chain_0`, etc.)
  directly on the structure.
- Prove `constraint_N_of_extraction` iff-lemmas linking each named
  predicate to `BinaryAdd.extraction.constraint_N_every_row`, tagged
  with `BinaryAdd_constraint_and_interaction_simplification`.

This replaces `ZiskFv.Spike.cout_0_boolean` (Phase 0 gap 3 — the "deferred
to Phase 1" wrapper record). Keep `Spike.lean` as a re-export for backward
reference.

**Task 8: `Valid_Main` structure + ADD-relevant named constraints.** Same
pattern as Task 7 but for the Main AIR's ADD subset only. Named predicates
cover: `is_external_op` boolean, `op_eq_0x0a_implies_is_external`,
`a_b_c_wiring`, `flag_is_zero_for_add`, and the bus-entry assumes-operation
constraint. Other Main constraints not in the ADD subset stay as raw
`constraint_N` references from `Extraction/Main.lean`.

**Task 9: `ZiskFv.Airs.OperationBus`.** Model the operation-bus schema
(11 fields per `operations.pil:144`). Define `OperationBusEntry F` with
named fields `op`, `a_0`, `a_1`, `b_0`, `b_1`, `c_0`, `c_1`, `flag`,
`main_step`, `extended_arg`, `extra_args_0`. Mirror openvm-fv's
`ExecutionBusEntry` / `MemoryBusEntry` pattern in
`openvm-fv/OpenvmFv/Fundamentals/Interaction.lean:63-80`. Provide
`opBus_row_Main : Valid_Main → ℕ → List (OperationBusEntry F)` and
`opBus_row_BinaryAdd` as sender/receiver projections.

**Task 10: `ZiskFv.RV64D.add`.** Widen `openvm-fv/OpenvmFv/RV32D/add.lean`:
- `PureSpec.AddInput` gets `r1_val r2_val : BitVec 64` and `PC : BitVec 64`.
- `PureSpec.AddOutput` gets `nextPC : BitVec 64` and
  `rd : Option (regidx × BitVec 64)`.
- `execute_RTYPE_add_pure` as pure function.
- `execute_RTYPE_add_pure_equiv` linking to
  `LeanRV64D.execute_instruction (instruction.RTYPE r2 r1 rd rop.ADD)`
  under `read_xreg` / `write_xreg` preconditions.

Depends on Track A having delivered the `RV64D/` skeleton; if Track A slips,
this task inlines the minimal RV64D bindings (just enough for ADD) and
leaves a TODO for Track A to replace them.

**Task 11: `ZiskFv.Spec.Add`.** The compositional theorem: given
`h_main : ADD-relevant Main constraints hold at row r_main`,
`h_binary : all BinaryAdd constraints hold at row r_binary`, and
`h_bus : Main's operation-bus entry at r_main matches BinaryAdd's
proved-operation entry at r_binary`, the Zisk-instruction row at r_main
computes `execute_RTYPE_add_pure` on the decoded operands.

This is the **first compositional proof** in the codebase — the place where
Phase 1 either succeeds or teaches us that `LeanZKCircuit.Interactions`
lacks a primitive. If a gap appears, choose between (a) upstream a PR, or
(b) vendor-and-extend locally. Log the choice in the handoff note per the
metaplan's external-coordination section.

**Task 12: `ZiskFv.Equivalence.Add`.** The final theorem:

```lean
theorem equiv_ADD
    (rs1 rs2 rd : Fin 32) (state : RV64State)
    (h_constraints : ZiskFv.Spec.add_circuit_holds state rs1 rs2 rd) :
    execute_instruction (.RTYPE rs2 rs1 rd rop.ADD) state
      = (bus_effect exec_row mem_row state).2
```

Proof: `transpile_ADD` + `Spec.Add` + `execute_RTYPE_add_pure_equiv`,
chained via `simp` and `grind` with the simp-attribute sets registered by
Tasks 3, 4, 7, 8.

**Task 13: Golden-trace harness.** `tools/zisk-fv-harness/` — new standalone
crate (same workspace-exclusion treatment as `zisk-pil-extract`). Depends on
`zisk-sdk` (path-dep into `vendor/zisk/` if we add that submodule later;
for Phase 1, add `zisk` as a submodule since we're already depending on it).
A single bin target:

```rust
fn main() -> Result<()> {
    let client = ProverClient::builder().emu().verify_constraints().build()?;
    let elf = ElfBinaryFromFile::new("examples/fv-probes/add.elf", false)?;
    let (pk, _) = client.setup(&elf)?;
    let result = client.execute(&pk, stdin)?;
    let main_rows = client.get_instance_trace(MAIN_INSTANCE_ID, ADD_ROW, 1, None)?;
    let binary_rows = client.get_instance_trace(BINARY_INSTANCE_ID, ADD_ROW, 1, None)?;
    emit_lean_fixture(&main_rows, &binary_rows, "ZiskFv/GoldenTraces/Add.lean")?;
    Ok(())
}
```

Probe program at `examples/fv-probes/add.rs`: a 3-instruction RISC-V blob
(`addi x1, x0, 3; addi x2, x0, 5; add x3, x1, x2`) assembled via `cargo
zisk build --target riscv64ima-zisk-zkvm-elf`.

**Task 14: `ZiskFv.GoldenTraces.Add` fixture + `#eval` check.** The emitted
fixture is a concrete `Valid_Main` + `Valid_BinaryAdd` witness. A
`#eval`-level check verifies the named constraints hold on that witness and
that `equiv_ADD` specializes to produce the expected output (`x3 = 8`).

**Task 15: `justfile::verify-phase1`.**

```
verify-phase1:
    cargo test --manifest-path tools/zisk-pil-extract/Cargo.toml
    cargo test --manifest-path tools/zisk-fv-harness/Cargo.toml
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout pil/zisk.pilout --air Main --only <add-subset> \
        --output ZiskFv/ZiskFv/Extraction/Main.lean
    diff -w ZiskFv/ZiskFv/Extraction/Main.lean \
            ZiskFv/ZiskFv/Extraction/Main.hand.lean
    cargo run --manifest-path tools/zisk-pil-extract/Cargo.toml -- \
        --pilout pil/zisk.pilout --air BinaryAdd \
        --output ZiskFv/ZiskFv/Extraction/BinaryAdd.lean
    diff -w ZiskFv/ZiskFv/Extraction/BinaryAdd.lean \
            ZiskFv/ZiskFv/Extraction/BinaryAdd.hand.lean
    cargo run --manifest-path tools/zisk-fv-harness/Cargo.toml
    cd ZiskFv && lake build
```

`verify-phase0` becomes a subset (should still pass on regression).

**Task 16: Handoff + memory.** `docs/fv/phase-1-handoff.md` (≤600 words)
listing shipped artifacts, what we learned that contradicts the metaplan,
per-opcode effort estimate for Phase 2 planning. Update
`project_phase0_outcomes.md` → append or add `project_phase1_outcomes.md`;
update `MEMORY.md` index.

### Track A — parallel, subagent-driven

**Single background task, launched on Day 1** (day-zero concept from the
metaplan):

Port `openvm-fv/OpenvmFv/RV32D/` → `ZiskFv/RV64D/`:
1. Mechanically widen `BitVec 32 → BitVec 64`, `U32 → U64` in every file.
2. Switch the `LeanRV` dep in `ZiskFv/lakefile.toml` from `rev = "rv32d"` to
   `rev = "main"` and update imports `LeanRV32D → LeanRV64D`.
3. Port each opcode pure-spec + Sail equivalence that has an RV64 analogue
   (ADD, SUB, AND, OR, XOR, SLL, SRL, SRA, SLT, SLTU, …). Stub RV64-only
   opcodes (`ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`, `LD`, `SD`, `LWU`) with
   `sorry`. Document each `sorry` as "awaiting Phase 3" in a table at
   the top of the file.
4. Expect to patch Sail-translated code (the `LeanRV64D` upstream is WIP).
   If a lemma on the RV32 side doesn't widen cleanly, isolate it, fix
   locally, and file an issue on `NethermindEth/sail-riscv-lean` referenced
   from a TODO in the relevant file.

Track A delivers `ZiskFv/RV64D/*.lean` with `lake build` green and a count
of remaining `sorry`s documented. Track B Task 10 consumes `RV64D/add.lean`
specifically; if Track A is behind, Task 10 inlines the minimum.

## Critical files to read / reference

- **Recon substrate:** `docs/fv/phase-1-recon.md` (to be written Task 0).
- **Extractor extension targets:** `tools/zisk-pil-extract/src/main.rs`
  functions `render_operand` (operand kinds) and `render_constraint`
  (constraint kinds).
- **Main PIL source:** `state-machines/main/pil/main.pil:94-97, 135-136,
  165, 367-374, 393-404` (from Task 0 recon). If the ZisK tree isn't
  vendored as a submodule by Task 1, these references won't resolve on a
  clone — so Task 1 also adds `vendor/zisk/` as a submodule pinned to the
  commit the pilout was built from.
- **Bus schema:** `pil/operations.pil:144` (also needs the submodule).
- **Transpiler reference:** `/home/cody/zisk/core/src/riscv2zisk_context.rs`
  ADD case.
- **Proof template:** `openvm-fv/OpenvmFv/Airs/Alu/BaseAluCoreAir.lean`,
  `openvm-fv/OpenvmFv/Constraints/VmAirWrapper_alu.lean`,
  `openvm-fv/OpenvmFv/Spec/BaseALU.lean`,
  `openvm-fv/OpenvmFv/Equivalence/BaseALU.lean`,
  `openvm-fv/OpenvmFv/Equivalence/Equivalence.lean:153-157`
  (`alu_non_imm_proof`).
- **RV32D template:** `openvm-fv/OpenvmFv/RV32D/add.lean`.
- **Interaction modeling:** `openvm-fv/OpenvmFv/Fundamentals/Interaction.lean:63-80`.
- **Harness pattern:** `/home/cody/zisk/examples/sha-hasher/host/bin/execute.rs`,
  `zisk/sdk/src/prover/mod.rs` (`get_instance_trace`, `get_instance_air_values`).

## Invariant (verification gate)

Phase 1 is complete iff `just verify-phase1` exits 0 from a clean checkout.
Specifically:

1. All extractor unit tests pass.
2. `Main` and `BinaryAdd` regenerated extractions diff-clean against their
   hand oracles.
3. `tools/zisk-fv-harness` runs to completion, emits a valid fixture.
4. `lake build` green including `ZiskFv.Equivalence.Add`.
5. `equiv_ADD` exported with the standard shape, zero `sorry` in the
   Equivalence chain.
6. `ZiskFv.GoldenTraces.Add` `#eval` check passes.
7. Track A: `ZiskFv/RV64D/` builds; remaining `sorry` count in a table.

## Known fragility (and what to do)

- **`LeanRV64D` may have rough edges.** Track A was designed to be
  subagent-driven so this fragility doesn't block Track B. If ADD's
  specific Sail equivalence is broken, Track B Task 10 inlines. If it's
  systemically broken, pause Track A, file upstream issues, and decide
  whether to vendor `sail-riscv-lean` locally. Budget: 4 hours before
  pivoting.
- **`LeanZKCircuit.Interactions` may lack a primitive we need** for
  compositional Main+Binary reasoning (Task 11). Mitigation per metaplan:
  upstream PR vs. vendor-and-extend. Decide at the first concrete friction
  point; don't pre-speculate.
- **Main AIR has 146 constraints; narrowing to the ADD subset may miss a
  load-bearing constraint.** Spot-check by running the harness on ADD and
  confirming every constraint flagged by `verify_constraints()` is either
  (a) in our extracted subset, or (b) provably irrelevant to the ADD bus
  entry. If (b) is not obvious, widen the subset.
- **Extending the extractor's `Challenge` / `AirValue` rendering requires
  knowing `LeanZKCircuit.OpenVM.Circuit`'s exact method names for
  challenges and exposed values.** Read the typeclass definition
  (`.lake/packages/LeanZKCircuit/LeanZKCircuit/OpenVM/Circuit.lean`) and
  use the same names. If our extractor renders `Circuit.challenge` but the
  typeclass calls it something else, the Lean file won't typecheck and the
  diff gate will fail — good, that's how we want failures to surface.
- **Goldilocks primality is 386s cold.** If Phase 1 CI ends up re-building
  Goldilocks on every run, replace `native_decide` with a Pratt certificate
  (vendor the witness) — 2-day detour, not Phase 1 scope by default.
- **`ai_plans/zisk-fv-phase-0.md` assumes `pil/zisk.pilout` is vendored.**
  Task 1 adding a `vendor/zisk/` submodule will touch paths
  `state-machines/binary/pil/binary_add.pil` → `vendor/zisk/…`. Update
  `docs/fv/extractor-notes.md` references in lockstep.

## Decisions captured (reversible but preferred)

- **Track B is serial.** Tasks 1-4 are prereq for 7-12; 5 is independent;
  6 is independent; 9 is prereq for 11. Running 5 + 6 + Track A in parallel
  is the only sanctioned concurrency inside Track B.
- **Track A runs as a single subagent-driven activity**, not day-by-day
  micromanaged. The subagent gets the Phase 1 plan excerpt + a pointer to
  `openvm-fv/OpenvmFv/RV32D/` and iterates.
- **No proof macros in Phase 1.** `alu_non_imm_proof` analogue lives in
  Phase 2 archetype work. Hand-writing ADD is the point.
- **Add `vendor/zisk/` as a submodule in Task 1**, pinned to the commit the
  current `pil/zisk.pilout` was built from (`48cf7ccef` per the Phase 0
  handoff). This lets Phase 1 cite live ZisK sources without vendoring more
  files. The `pil/zisk.pilout` stays as a vendored artifact because it's
  gitignored upstream.
- **Target: minimal-viable-ADD**, not a polished theorem. First try succeeds
  = commit. Don't refactor mid-phase; log cleanups for Phase 2.

## Verification section (how we test end-to-end)

1. From clean checkout: `just verify-phase1`. Expected: exit 0.
2. `git grep -n 'sorry' ZiskFv/Airs ZiskFv/Spec ZiskFv/Equivalence
   ZiskFv/GoldenTraces` — expected: no matches. RV64D/ may have stubs
   documented as "Phase 3".
3. Manual inspection: open `ZiskFv/Equivalence/Add.lean` — confirm
   `theorem equiv_ADD` has the metaplan-specified shape.
4. Manual inspection: open `ZiskFv/GoldenTraces/Add.lean` — confirm the
   fixture is a concrete witness, not a stub.
5. Read `docs/fv/phase-1-handoff.md` — confirm it lists metaplan revisions
   needed and per-opcode effort estimate.

## Parallelism overview

- **Days 1-3:** Task 0 (recon), Task 1 (extractor constraint-kinds), Task 5
  (Goldilocks extensions), Task A1 kickoff (RV64D port).
- **Days 4-8:** Tasks 2, 3, 4 (extractor + extractions).
- **Days 9-14:** Tasks 6, 7, 8, 9 (Transpiler, Airs, bus model).
- **Days 15-22:** Tasks 10, 11, 12 (RV64D/add, Spec, Equivalence). Track A
  converges by end of this window.
- **Days 23-25:** Tasks 13, 14, 15 (harness + fixture + gate).
- **Days 26-27:** Task 16 (handoff + memory). Metaplan revision review.

**Estimate:** ~4 weeks of focused work (Track B), overlapping Track A's
~2-3 weeks. Real-wall-clock depends heavily on how rough `LeanRV64D` turns
out to be. First serious slip point is Task 11's compositional proof —
that's where a week could silently become three. If Task 11 isn't showing
progress after 3 days, stop and audit `LeanZKCircuit.Interactions`
primitives directly.
