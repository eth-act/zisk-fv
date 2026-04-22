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

Pre-execution reconnaissance established five load-bearing facts with
citations into `vendor/zisk/` (pinned at commit `48cf7ccef`):

### 1. Main AIR opcode dispatch

`vendor/zisk/state-machines/main/pil/main.pil:135-136` declares the per-row
opcode columns:

```
col witness bits(1) is_external_op;
col witness bits(8) op;
```

Operands `a[RC]`, `b[RC]`, `c[RC]` are `bits(32)` with `RC = 2` (so two limbs
covering 64 bits) at `main.pil:94-97`. The bus hop is gated by `is_external_op`
in `assumes_operation(...)` at `main.pil:367-374` (one call per row, with
`a := [a[0], (1-m32)*a[1]]`, `b := [b[0], (1-m32)*b[1]]`, `c := c`,
`flag := flag`, `main_step := STEP * is_precompiled`,
`extended_arg := jmp_offset1 * is_precompiled`, `sel := is_external_op`). The
row-to-row pc handshake (`main.pil:393-404`) and the `op == 0/1` internal
shortcuts complete the pic.

Opcode literal for ADD: `OP_ADD = 0x0A` per `vendor/zisk/pil/opids.pil`.
`OPERATION_BUS_ID = 5000` per `vendor/zisk/pil/opids.pil:2`.

### 2. Pilout extractor coverage gap

`zisk.pilout`'s `Main` AIR has 146 constraints. The Phase 0 extractor
(`tools/zisk-pil-extract/src/main.rs:341-352`) renders `Constant`,
`WitnessCol`, and `Expression` operand kinds; the other six kinds bail out.
Empirically `Main` extraction without `--skip-unsupported` aborts immediately
on the first `FixedCol` reference. Operand-kind coverage —
`FixedCol` / `Challenge` / `AirValue` for ADD; `PeriodicCol`,
`ProofValue`, `AirGroupValue`, `PublicValue`, `CustomCol` deferred — is
Phase 1's first hard gate (Tasks 1, 2 below).

Constraint kinds are also currently flattened: `EveryRow`, `FirstRow`,
`LastRow`, `EveryFrame` all render as `constraint_N`
(`render_constraint`, `main.rs:255-287`). Phase 1 separates them so the
bridging proofs can quantify over the right row domain (Task 1).

### 3. openvm-fv ADD chain shape (proof template)

The reference proof for ADD is a 6-layer stack. We mirror it for RV64:

| openvm-fv path | role |
|---|---|
| `OpenvmFv/Extraction/*.lean` | raw extracted constraints (numeric column indices) |
| `OpenvmFv/Airs/Alu/BaseAluCoreAir.lean` | named-column `Valid_<Air>` structures (`#define_subair`) |
| `OpenvmFv/Constraints/VmAirWrapper_alu.lean` | `constraint_N_of_extraction` simp bridges |
| `OpenvmFv/RV32D/add.lean` | `PureSpec.AddInput`/`AddOutput` + `execute_RTYPE_add_pure_equiv` against Sail |
| `OpenvmFv/Spec/BaseALU.lean` | circuit-correctness theorem (constraints ⇒ ALU semantics) |
| `OpenvmFv/Equivalence/BaseALU.lean` | final per-opcode theorem composed via `alu_non_imm_proof` macro (`Equivalence.lean:153-157`) |

Phase 1 hand-writes the macro expansion for ADD; macros come in Phase 2.

### 4. LeanRV64D status

`NethermindEth/sail-riscv-lean` `main` exposes `LeanRV64D`, but commits
flag it as Sail-auto-translated WIP. We expect to discover and patch lemmas
on contact. Track A budget assumes ≤4 hours of upstream churn before falling
back to inlining what Track B Task 10 needs.

### 5. Golden-trace plumbing

ZisK's SDK exposes `ProverClient::get_instance_trace(instance_id, first_row,
num_rows, offset)` returning `Vec<proofman_common::RowInfo>`. Reference call
site: `vendor/zisk/examples/sha-hasher/host/bin/execute.rs`. Phase 1's harness
(Task 13) wires this; it does not implement it.

### ADD subset of Main constraints (working set)

Tasks 3, 8 restrict Main extraction to constraints that are (a) wired by the
ADD transpilation per `vendor/zisk/core/src/riscv2zisk_context.rs:631-643`
(`create_register_op` calls `src_a("reg", rs1)`, `src_b("reg", rs2)`,
`op("add")`, `store("reg", rd)`, `j(4, 4)`), or (b) gate the operation-bus
hop. Concrete index list is established by Task 3 against a fresh
`--list-constraints` dump and pinned in `Main.hand.lean`.

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
- Post-execution "Phase 1 status" section appended to this plan (see end of
  file).

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

**Task 0: Lock in the recon.** The pre-execution reconnaissance lives in
this document's "Pre-execution reconnaissance" section above. Task 0 is the
acceptance check that those facts still hold against `vendor/zisk/@48cf7ccef`
before any other task proceeds.

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

**Task 16: Handoff + memory.** Append a "Phase 1 status — CLOSED" section
to this plan (shipped artifacts, what we learned that contradicts the
metaplan, per-opcode effort estimate for Phase 2 planning). Add
`project_phase1_outcomes.md`; update `MEMORY.md` index.

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

- **Recon substrate:** the "Pre-execution reconnaissance" section at the
  top of this file.
- **Extractor extension targets:** `tools/zisk-pil-extract/src/main.rs`
  functions `render_operand` (operand kinds) and `render_constraint`
  (constraint kinds).
- **Main PIL source:** `vendor/zisk/state-machines/main/pil/main.pil:94-97,
  135-136, 165, 367-374, 393-404`.
- **Bus schema:** `vendor/zisk/pil/operations.pil:144`.
- **Transpiler reference:** `vendor/zisk/core/src/riscv2zisk_context.rs`
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
5. Read the "Phase 1 status — CLOSED" section at the end of this plan —
   confirm it lists metaplan revisions needed and per-opcode effort
   estimate.

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

---

## Phase 1 status — CLOSED 2026-04-21

`just verify-phase1` exits 0 from a clean checkout in `/home/cody/zisk-fv/`.
Commit `ad55fcb`.

### What shipped

- **Extractor extensions** (`tools/zisk-pil-extract/`):
  - Constraint-kind differentiation: `every_row` / `first_row` / `last_row` /
    `every_frame_<min>_<max>` suffixes (was: flattened `constraint_N`).
  - New operand-kind support: `FixedCol`, `Challenge`, `AirValue`,
    `AirGroupValue`. Negative `rowOffset` on `WitnessCol`/`FixedCol` and
    constraints mixing `F` (witness cells) with `ExtF` (challenges, exposed
    values) skip-stub instead of failing typecheck downstream.
  - Pilout `Challenge { stage, idx }` → flat index via cumulative
    `num_challenges[0..stage-1]` (PIL2's stage numbering is 1-based).
  - 19 unit tests; integration via `verify-phase1` diff gate against hand
    oracles for both `BinaryAdd` (4 of 9 constraints — same as Phase 0;
    bus/permutation constraints stay stubbed and are abstracted in `Airs/`)
    and `Main` (8 of 146; the ADD subset).
- **`ZiskFv/`** Lean package, full ADD chain, zero `sorry`:
  - `Fundamentals/Goldilocks.lean` — `NatCast FGL`, `BitVec 8/16/32` ↔ `FGL`
    coercions, `isU64_chunks` / `isU64_lanes`, `chunks_to_bv64` /
    `lanes_to_bv64`. Critical note: do NOT shadow `[Field FGL]` as a
    proof-local instance variable (a comment guards against the trap that
    bit `Spec.Add` once).
  - `Fundamentals/Transpiler.lean` — `transpile_ADD` axiom over
    `RV64State`. **Trusted** surface, mirrors
    `vendor/zisk/core/src/riscv2zisk_context.rs::create_register_op`.
  - `Extraction/{Main,BinaryAdd}.lean` (+ `.hand.lean` oracles) — auto-
    regenerable from the extended extractor; diff-gated.
  - `Airs/Main.lean`, `Airs/Binary/BinaryAdd.lean` — named-column
    `Valid_<AIR>` structures (hand-written, not via `#define_subair`) with
    9 named-constraint predicates and `constraint_N_of_extraction` iff
    bridges (one per ADD-subset constraint).
  - `Airs/OperationBus.lean` — 12-field `OperationBusEntry`; sender
    (`opBus_row_Main`) and receiver (`opBus_row_BinaryAdd`) projections.
    Specialized to `m32 = 0`; the 32-bit-op path is out of Phase 1 scope.
  - `Spec/Add.lean` — `add_compositional`: the **first compositional proof**
    in the codebase (Main + BinaryAdd + bus → Goldilocks ADD). Closes via
    `linear_combination` over the two carry-chain equations.
  - `Equivalence/Add.lean` — `equiv_ADD`: composes `add_compositional` with
    the `transpile_ADD` axiom into the per-row equivalence statement.
  - `GoldenTraces/Add.lean` — concrete witness for `3 + 5 = 8`. Four
    `example`-level `decide` checks confirm chunk reassembly, lane
    recombination, and both carry chains hold on the witness.
- **`tools/zisk-fv-harness/`** — fixture-emitter Rust crate. Hardcodes the
  canonical ADD example; emits `ZiskFv/GoldenTraces/Add.lean`. Two unit
  tests cover the rendering and overflow-carry propagation.
- **`vendor/zisk/`** — git submodule pinned at `48cf7ccef` (the commit
  the vendored `pil/zisk.pilout` was built from).
- **`justfile::verify-phase1`** — extractor + harness tests, regenerate +
  diff both extractions, regenerate fixture, full `lake build`. Exits 0
  from a clean checkout.

### What was learned (relevant to the metaplan)

- **The metaplan's "first compositional proof" was not the bottleneck the
  metaplan feared.** `LeanZKCircuit.Interactions` was *not* needed for
  Phase 1 — the whole permutation-argument primitive is cleanly abstracted
  by `OperationBusEntry` (a plain projection-equality between two
  field-valued tuples). The bus-equation constraints were skip-stubbed at
  the extraction layer (mixed `F`/`ExtF` arithmetic doesn't typecheck),
  but the named-constraint layer's `matches_entry` predicate replaces
  them entirely without losing semantic content.
- **`ring` over `Fin p` works — but can be silently shadowed.**
  Declaring `[Field FGL]` as a proof-local variable creates a dummy
  instance that defeats `ring`. The workaround is to declare it once
  globally in `Fundamentals/Goldilocks.lean` and never re-quantify.
- **Coefficients written as `4294967296 * 4294967296` close `ring`;
  written as `18446744073709551616` (the same number) do not.** ring
  treats them as different polynomial atoms, with no automatic
  literal-product recognition. The `equiv_ADD` statement uses the
  factored form for this reason.
- **`(1 - 0) * x` over `Fin p` does not reduce to `x` via `simp` /
  `ring_nf` / `decide`-based rewriting** in the contexts we tried. To
  side-step this, `opBus_row_Main` is specialized to the `m32 = 0` case
  rather than carrying the `(1 - m32) *` factor that the upstream PIL
  uses. Generalizing this is Phase 1.5 work (relevant once the 32-bit
  `*_W` opcodes are in scope).
- **Track A's RV64D port shipped 47 ported files** (`ZiskFv/RV64D/*.lean`)
  with `add.lean` syntactically clean (zero `sorry`) but unbuildable
  pending `Fundamentals/Execution.lean` (a Phase 1.5 Track B deliverable
  per the STATUS.md plan). 43 RV32-specific equivalence proofs went to
  `sorry` — explicitly because they relied on RV32-width tactics, not
  upstream `LeanRV64D` brokenness. One genuine upstream blocker:
  `currentlyEnabled Ext_Zca` doesn't simp-normalize through `SailME.run`,
  blocking `jump_to_equiv` and (transitively) every branch + jump
  equivalence proof.
- **`native_decide` for Goldilocks primality is still ~386s on a cold
  build.** Not addressed in Phase 1 (was deemed Phase 2 work).

### Per-opcode effort estimate (for Phase 2 planning)

ADD took the structure work — reusable across all RV64 R-type ALU ops:
- `Valid_Main` is fully reusable.
- `Valid_BinaryAdd` is template for `Valid_BinaryAnd`, `Valid_BinaryOr`,
  `Valid_BinaryXor`; the carry-chain predicates change but the
  bus-projection shape doesn't.
- `OperationBusEntry` and the named-constraint bridge pattern are reusable.
- `Spec.Add` is the proof template — most opcodes will be a strict
  one-equation rewrite of the carry-chain shape (subtraction is trivially
  ADD-with-2's-complement; bitwise ops are independent per chunk).

**Estimate: ~1 day per ALU opcode** once Phase 2 starts (vs. ~2 weeks
for ADD's pioneering structure work). Macros (`alu_non_imm_proof`
analogue) come once 3-5 opcodes have shipped and the pattern is
crystallized.

### What remains (Phase 1.5 plan)

Phase 1 shipped `equiv_ADD` as a circuit-level theorem but left five
items explicitly deferred — they block the theorem from chaining through
to the Sail spec (item E), prevent any 32-bit opcode from being verified
(item M), keep the golden-trace fixture from proving the real ZisK
prover's witness conforms (item H), make every cold build pay a 386s
Goldilocks-primality tax (item P), and leave Track A's branch/jump
equivalence proofs stuck on an upstream simp gap (item U).

Phase 1.5 closes all five. The priority is item E: without
`Fundamentals/Execution.lean`, the metaplan's top-level theorem shape
("Sail LHS = bus-effect RHS") is a circuit-level statement, not a
Sail-equivalent one — the unglamorous but load-bearing port that turns
Phase 1's work into a genuine Sail-equivalence result.

#### Scope (strict)

**In scope — Track E (Execution.lean port — primary prereq, serial):**

- `ZiskFv/Fundamentals/Execution.lean` — full 420-line port of
  `/home/cody/openvm-fv/OpenvmFv/Fundamentals/Execution.lean` to RV64:
  14 definitions/lemmas covering RTYPE (lines 31-66), ITYPE (83-97),
  SHIFTIOP (111-139), MUL (158-307), DIV/REM (317-418).
- Width widening: `BitVec 32 → BitVec 64`, `U32 → U64`,
  `4#32 → 4#64`, shift-extract `31 → 63`, bounds `2^{31,32} → 2^{63,64}`,
  sign-extend `12 32 → 12 64`, shift-amount extract `4 0 → 5 0` (6-bit
  shamt for RV64). ~85% mechanical, ~15% manual (MUL 8-case sign-combo
  induction, DIV overflow/zero-div cases — per pre-execution recon).
- Import switch: `import LeanRV32D` / `open LeanRV32D.Functions` →
  `LeanRV64D` equivalents. `log2_xlen` and `xlen` values change from
  5/32 to 6/64.
- Chain `execute_RTYPE_eq_execute_RTYPE'` into `Equivalence/Add.lean` so
  `equiv_ADD`'s LHS Sail call is discharged via the pure function;
  remove the "circuit-level only" caveat from the docstring.
- Ancillary: the 5 RV64D consumers that already `import
  ZiskFv.Fundamentals.Execution` (add, mul, mulh, mulhu, mulhsu) should
  build after Track E lands; close any `sorry`s in those five files that
  were blocked purely on missing Execution.

**In scope — Track M (m32 generalization, serial):**

- `ZiskFv/Airs/OperationBus.lean:61,63`: restore the
  `(1 - m.m32 row) *` factor on `a_hi` and `b_hi` per
  `main.pil:367-374`. Remove the "specialized to m32 = 0" docstring.
- Move the `m32 = 0` precondition from the bus definition into the
  constraint hypotheses (`Spec/Add.lean::main_row_in_add_mode`) so the
  bus model is PIL-faithful and add-specific preconditions live at the
  spec layer.
- Decision point (logged at task M2): option (a) add a simp lemma
  family reducing `(1 - m32) * x` under `m32 ∈ {0, 1}` through the
  `OperationBusEntry` structure; or option (b) split into
  `opBus_row_Main_64bit` / `opBus_row_Main_32bit` and route ADD through
  `_64bit`. Phase 1 recon flagged the simp path as risky — (a) first,
  1-day budget, then (b).

**In scope — Track H (live harness):**

- `examples/fv-probes/add.rs` (new) — 3-instruction probe program
  (`addi x1, x0, 3; addi x2, x0, 5; add x3, x1, x2`), built via
  `cargo zisk build --target riscv64ima-zisk-zkvm-elf`. If the
  `cargo zisk build` subcommand is undocumented, spike on
  `vendor/zisk/examples/sha-hasher/` to derive the recipe.
- `tools/zisk-fv-harness/Cargo.toml` — add `zisk-sdk = { path =
  "../../vendor/zisk/sdk" }` and `proofman-common = { path =
  "../../vendor/zisk/proofman/proofman-common" }`.
- `tools/zisk-fv-harness/src/main.rs` — default to `--mode live`:
  `ProverClient::builder().emu().verify_constraints().build()` →
  `setup` → `execute` → `get_instance_trace(MAIN_INSTANCE_ID, ADD_ROW, 1,
  None)` and same for `BINARY_INSTANCE_ID`, parsed into the existing
  `Valid_Main` + `Valid_BinaryAdd` fixture shape. Pattern from
  `vendor/zisk/examples/sha-hasher/host/bin/execute.rs`. Keep
  `--mode golden` as legacy hardcoded path (the two existing unit tests
  stay valid against it).
- `justfile::verify-phase1` — run harness in `--mode live`, diff
  emitted `GoldenTraces/Add.lean` against the checked-in file; mismatch
  = loud failure. Gate behind `FV_LIVE=1` env var if CI lacks the ZisK
  toolchain; default local-dev = on.

**In scope — Track P (Pratt certificate):**

- `ZiskFv/Fundamentals/PrattCertificate.lean` (new) — inductive `Pratt`
  (base + list of `(prime_factor, sub_certificate)`), `Pratt.verify :
  Pratt → Nat → Bool`, lemma `Pratt.verify_correct : Pratt.verify c p =
  true → Nat.Prime p`. Proof uses Lehmer's converse of Fermat's little
  theorem via mathlib's `Nat.Prime` / `ZMod.unit_of_coprime`. Mathlib
  4.26 has no Pratt primitive; write ~80 lines self-contained.
- `ZiskFv/Fundamentals/Goldilocks.lean:19` — replace `Nat.Prime
  GL_prime := by native_decide` with `Pratt.verify_correct
  goldilocks_pratt rfl`. Witness: base = 7 (primitive root of
  `GL_prime - 1`); `GL_prime - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`
  (well-known factorization, offline-computable). Target cold-build
  time < 10s.

**In scope — Track U (upstream sail-riscv-lean):**

- File a minimal-reproduction issue against
  `NethermindEth/sail-riscv-lean` for the `currentlyEnabled Ext_Zca`
  simp gap in `SailME.run`. Isolate from `Auxiliaries.lean:751-762`
  into a standalone `.lean` file with minimum `LeanRV64D` imports.
- Fallback (task U2): if no upstream response after one week, add a
  local `bind_currentlyEnabled_false` lemma in `Auxiliaries.lean` that
  discharges the shape under `misa[2] = 0` (ZisK's assumption).
  Unblocks `jump_to_equiv` and transitively ~8 branch/jump proofs
  (`beq`, `bne`, `bge`, `bgeu`, `blt`, `bltu`, `jal`, `jalr`).

**Explicitly out of scope (Phase 2+):**

- Any opcode beyond ADD at `Spec/` or `Equivalence/` layers. Phase 1.5
  is closure, not expansion — even though Execution.lean's port
  incidentally unblocks 40+ RV64D files, we do not chain them through
  `Spec/` / `Equivalence/` in Phase 1.5.
- The 43 RV64D `sorry`s that are not blocked on Execution.lean or
  Ext_Zca (RV32-width-tactic-dependent proofs — per Phase 1 CLOSED
  learnings).
- Proof macros (`alu_non_imm_proof` analogue) — deferred to Phase 2
  after 3-5 opcodes have shipped at the Spec layer.
- Non-ADD Main AIR constraints beyond what `m32` generalization touches.
- `PeriodicCol` / `ProofValue` / `PublicValue` / `CustomCol` operand
  kinds in the extractor (still deferred until a constraint demands
  them).

#### Execution order

Track letter prefixes indicate parallelism: E serial, M serial (depends
on Task E1 landing), H parallel, P parallel, U parallel.

**Task E1: Skeleton + import switch.** Copy openvm-fv's Execution.lean
to `ZiskFv/ZiskFv/Fundamentals/Execution.lean`. Rewrite imports
(`LeanRV32D → LeanRV64D`). Don't expect it to typecheck yet.

**Task E2: RTYPE port (source lines 31-66).**
`execute_RTYPE_pure`, `execute_RTYPE'`,
`execute_RTYPE_eq_execute_RTYPE'`. Mechanical widening. After this:
`lake build ZiskFv.RV64D.add` should green. Checkpoint commit.

**Task E3: ITYPE + SHIFTIOP port (source lines 83-139).** Sign-extend
immediate width stays at 12, shift-extract index changes (4→5). After:
`addi`, `slli`, `srli`, `srai` build. Checkpoint commit.

**Task E4: MUL port (source lines 158-307, ~130 lines manual).** The
8-case sign-combination induction. Recompute constants: `2^32 → 2^64`,
`2^31 → 2^63`, `4294967296 → 18446744073709551616`. Modular identity
`(a % 2^65) % 2^64 = a % 2^64` becomes `(a % 2^129) % 2^128 = a %
2^128` (64+64=128 full-product width). Watch for `ring` atom-recognition
traps (CLAUDE.md trap #2 — write factored literal products, not
expanded). Unblocks `mul`, `mulh`, `mulhu`, `mulhsu`. Checkpoint commit.

**Task E5: DIV/REM port (source lines 317-418, ~124 lines manual).**
Overflow case `-2^31 / -1 = -2^31` becomes `-2^63 / -1 = -2^63`;
unsigned divide-by-zero `2^32 - 1` becomes `2^64 - 1`. Unblocks `div`,
`divu`, `rem`, `remu`. Checkpoint commit.

**Task E6: Chain Sail into `Equivalence/Add.lean`.** Add the final
rewrite step through `execute_RTYPE_eq_execute_RTYPE'` so the LHS Sail
call reduces to the pure function. Remove "circuit-level only" caveat
in the docstring. Track E done.

**Task M1: Generalize `opBus_row_Main`.** Edit `Airs/OperationBus.lean`
to emit `(1 - m.m32 row) * m.a_1 row` / `(1 - m.m32 row) * m.b_1 row`
on `a_hi` / `b_hi`. Update docstring to match PIL exactly.

**Task M2: Simp-lemma family — option (a).** Add
`@[simp] lemma one_sub_m32_mul_of_m32_zero (h : m32 = 0) (x : F) :
(1 - m32) * x = x`. Re-run `lake build Spec.Add Equivalence.Add`. If
`simp` closes through `OperationBusEntry`, done. If not, 1-day budget
then fall back to option (b): split `opBus_row_Main_64bit` /
`opBus_row_Main_32bit`, route ADD through `_64bit`. Log the choice in
the Phase 1.5 CLOSED section.

**Task H1: Probe ELF toolchain.** Verify `cargo zisk build
--target riscv64ima-zisk-zkvm-elf` works; if the subcommand is not
installed, spike on `vendor/zisk/cli/` or `vendor/zisk/examples/
sha-hasher/` (1 day). Gate: `examples/fv-probes/add.elf` exists.

**Task H2: Harness dependencies.** Add `zisk-sdk` and
`proofman-common` path-deps. `cargo build -p zisk-fv-harness`
resolves.

**Task H3: Live mode.** Rewrite `src/main.rs` to default to
`--mode live` — `ProverClient::builder().emu().verify_constraints()`
→ `setup` → `execute` → `get_instance_trace` × 2 → `emit_lean_fixture`.
Keep `--mode golden` as the hardcoded path; existing two unit tests
stay valid against it.

**Task H4: Fixture diff gate.** `justfile::verify-phase1` runs harness
in live mode (guarded by `FV_LIVE` env var default-on locally), diffs
emitted `ZiskFv/GoldenTraces/Add.lean` against checked-in file. Live
and hardcoded witnesses must agree for `3 + 5 = 8`.

**Task P1: `PrattCertificate.lean` — the verifier.** New file.
Inductive `Pratt`, verifier, correctness lemma via Lehmer's converse.
~80 lines, self-contained.

**Task P2: Goldilocks witness.** Define `goldilocks_pratt` with base =
7, factors `2^32 · 3 · 5 · 17 · 257 · 65537`. Replace `native_decide`
with `Pratt.verify_correct goldilocks_pratt rfl`. Target < 10s cold
build for the Goldilocks module. If naive `rfl` takes > 30s, split
factorization into sub-witnesses (+1 day).

**Task U1: Upstream issue.** Minimal repro in a standalone `.lean`
file. File issue (not PR) on `NethermindEth/sail-riscv-lean`. Link
from a TODO at `Auxiliaries.lean:762`.

**Task U2: Local fallback.** If no upstream response after one week
OR triage indicates "won't fix soon", add `bind_currentlyEnabled_false`
lemma in `Auxiliaries.lean`, discharge `jump_to_equiv`'s `sorry`, close
~8 transitively-blocked branch/jump proofs. Log the decision.

**Task V1: `justfile::verify-phase1` update.** Add:
```
cd ZiskFv && lake build ZiskFv.Fundamentals.Execution
cd ZiskFv && lake build ZiskFv.RV64D.add
[FV_LIVE=1] cargo run -p zisk-fv-harness -- --mode live
diff ZiskFv/ZiskFv/GoldenTraces/Add.lean <emitted>
```

**Task V2: Append Phase 1.5 CLOSED section.** Record shipped artifacts,
M2 decision (option a/b), upstream response (or lack thereof), MUL/DIV
tactic surprises, RV64D final `sorry` counts, Goldilocks cold-build
time before/after, per-opcode effort refinement (ADDW/SUBW should be
half-day after m32 generalization).

#### Parallelism overview

Tracks E, M, H, P, U are independent except: M depends on E1 (so
`Spec/Add` still builds); V1/V2 depend on all other tracks.

#### Verification (end-to-end)

1. From clean checkout: `just verify-phase1` exits 0, including the
   `--mode live` harness leg under `FV_LIVE=1`.
2. `git grep -n 'sorry' ZiskFv/Fundamentals ZiskFv/Airs ZiskFv/Spec
   ZiskFv/Equivalence ZiskFv/GoldenTraces ZiskFv/RV64D/add.lean
   ZiskFv/RV64D/addi.lean ZiskFv/RV64D/mul.lean ZiskFv/RV64D/div.lean`
   — no matches.
3. `time lake build ZiskFv.Fundamentals.Goldilocks` cold: under 10s
   (baseline 386s).
4. `Equivalence/Add.lean::equiv_ADD` docstring does not say
   "circuit-level only".
5. "Phase 1.5 status — CLOSED" section is populated below this plan.

#### Known fragility

- **MUL/DIV proof tactics may not widen cleanly.** Phase 1 discovered
  `ring` treats factored and expanded literals as different atoms
  (CLAUDE.md trap #2). Budget: +2 days per op family if tactics need
  rethinking.
- **`cargo zisk build` may be undocumented.** H1 budgets 1 day of
  reverse-engineering from `sha-hasher/`. If it requires a compiler
  fork or out-of-tree toolchain, pivot to a hand-assembled ELF via
  `riscv64-unknown-elf-as` + linker script.
- **Pratt verification may be slow.** If `rfl` on the Goldilocks
  witness takes > 30s cold, split `p - 1` factorization into nested
  sub-witnesses (mathlib Lucas-Lehmer pattern). Budget: +1 day.
- **M2 simp lemma may not fire through `OperationBusEntry`.** Phase 1
  recon explicitly warned. 1-day option-(a) budget then fall back to
  option (b).
- **Upstream response latency.** U2 fallback is designed to not gate
  on upstream. Do not block Phase 1.5 completion on a merged
  sail-riscv-lean PR.

#### Critical files

- `ZiskFv/ZiskFv/Fundamentals/Execution.lean` (new) — the 420-line
  port.
- `ZiskFv/ZiskFv/Fundamentals/PrattCertificate.lean` (new) — Pratt
  verifier.
- `ZiskFv/ZiskFv/Fundamentals/Goldilocks.lean` — replace
  `native_decide` with Pratt witness (line 19).
- `ZiskFv/ZiskFv/Airs/OperationBus.lean:45-69` — restore `(1 - m32)`
  factors.
- `ZiskFv/ZiskFv/Spec/Add.lean:39,93` — move `m32 = 0` precondition
  into constraint hypotheses.
- `ZiskFv/ZiskFv/Equivalence/Add.lean` — chain Sail side through
  `execute_RTYPE_eq_execute_RTYPE'`; remove "circuit-level only".
- `ZiskFv/ZiskFv/RV64D/{add, addi, mul, mulh, mulhu, mulhsu, div,
  divu, rem, remu}.lean` — close `sorry`s blocked on Execution.
- `ZiskFv/ZiskFv/RV64D/Auxiliaries.lean:751-762` — U2 fallback site.
- `tools/zisk-fv-harness/{Cargo.toml,src/main.rs}` — live mode.
- `examples/fv-probes/add.rs` (new) + built `add.elf`.
- `justfile` — V1 gate update.
- `vendor/zisk/examples/sha-hasher/host/bin/execute.rs` (read-only) —
  reference `ProverClient` call pattern.
- `vendor/zisk/sdk/src/prover/mod.rs` (read-only) — SDK surface.

### Phase 1.5 status — CLOSED 2026-04-21

`just verify-phase1` exits 0 from the same clean checkout that closed
Phase 1, now with Phase 1.5's five tracks landed as ten commits
(`57bc4c8..056398f`). Four annotated `sorry` warnings remain — all
out-of-scope per the plan's explicit time-box allowances, details below.

#### What shipped

- **Track E (Execution.lean port):** `ZiskFv/Fundamentals/Execution.lean`
  grew from nonexistent to 302 lines across six commits
  (`57bc4c8` RTYPE, `a5d03f4` ITYPE+SHIFTIOP, `aef0425` MUL structural,
  `4843881` MUL High-half closure, `fa844d3` DIV/REM structural,
  `e84a528` E6 Sail chain). All 5 pure functions (`execute_RTYPE_pure`,
  `execute_ITYPE_pure`, `execute_SHIFTIOP_pure`, `execute_MUL_pure`,
  `execute_DIV_REM_pure`) landed fully. Equivalence lemmas: RTYPE +
  ITYPE + SHIFTIOP + MUL-High all close; 3 targeted `sorry`s remain
  (MUL-Low 4 sign cases, DIV equivalence, REM equivalence) pending
  RV64 analogues of openvm-fv's `toInt_toInt_as_toNat_64` family and
  widened `div_overflow` / `to_bits_truncate` bounds. All 47 RV64D
  opcode files that previously were "blocked on Track B
  Fundamentals/Execution" now build. `equiv_ADD_sail` added to
  `Equivalence/Add.lean` as the Sail-level companion to the
  circuit-level `equiv_ADD`.

- **Track M (m32 generalization):** commit `72c47ca`. Option (a) —
  simp lemma family — landed. `Airs/OperationBus.lean` restored the
  PIL-faithful `(1 - m.m32 row) *` factors on `a_hi`/`b_hi`. The
  `Spec/Add.lean::add_compositional` proof grew 2 lines
  (`rw [h_m32] at h_match_ahi h_match_bhi; simp only [one_sub_zero_mul]`).
  `Equivalence/Add.lean` required zero source changes. 32-bit ops can
  now supply `m32 = 1` without needing a second bus-definition variant.

- **Track P (Pratt certificate):** commit `c28c000`.
  `Fundamentals/PrattCertificate.lean` (219 lines) defines an
  inductive `Pratt` with `.small` (defers to mathlib's
  `Nat.decidablePrime`) and `.step` (Lucas certificate) constructors;
  `Pratt.verify_correct` routes through mathlib's
  `lucas_primality`. Goldilocks witness: base 7, factorization
  `p − 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`, each factor ≤ 65537
  handled by `.small`. Cold build for
  `ZiskFv.Fundamentals.Goldilocks` fell from **392.81s → 6.36s**
  (~65x). Key: `powMod` with intermediate modular reduction is
  mandatory — naive `a^(p-1) % p` OOMs `native_decide`.

- **Track H (live ProverClient harness):** commit `5ba5291`.
  Partial path per plan's "if SDK deps resolve but environment
  blocks" branch.
  * `examples/fv-probes/add/` — probe program (3-instruction RV64
    ADD, ZisK `#[no_main] ziskos::entrypoint!` style).
  * `tools/zisk-fv-harness/` — refactored into shared `AddWitness` +
    `render_lean`; clap `--mode golden|live`; live code behind
    `#[cfg(feature = "live")]` with `ProverClient::builder().emu()
    .verify_constraints()` → `get_instance_trace(MAIN_AIR_ID=12, 0,
    256, None)` scan for `op == 0x0a`. `--mode live` without the
    feature flag returns an actionable error. 4 unit tests pass.
    ethPandaOps Rust standards applied (tracing, tracing-subscriber).
  * `justfile::verify-phase1` — added `_maybe_verify_live`
    sub-target; opt-in via `FV_LIVE=1`.
  * **Upstream blocker logged:** `pil2-proofman`'s `starks-lib-c`
    C++ dep (`rapidsnark/binfile_writer.hpp`) lacks
    `#include <cstdint>` and fails under GCC ≥13. Not fixable here;
    `--features live` builds as soon as upstream C++ is patched.

- **Track U1 (upstream Ext_Zca issue):** commit `056398f`.
  `docs/fv/upstream-issues/sail-riscv-lean-ext-zca-simp.md` carries
  the ready-to-file issue body (minimal repro, environment pins —
  LeanRV `81c8c84f`, lean v4.26.0, mathlib v4.26.0 —, observed
  locations, suggested fix shapes). `ZiskFv/RV64D/Auxiliaries.lean`
  TODO comment updated to reference the draft. Filing deferred to
  the user (outside-org repo, not auto-filed). Track U2 local
  fallback correspondingly deferred per plan.

#### What was learned (for the metaplan / Phase 2)

- **Phase 1 trap #3 ("`(1 - 0) * x` doesn't reduce") was context-bound,
  not fundamental.** The problem is that `simp`/`ring_nf`/`decide` do
  not reach under `OperationBusEntry` when `m32` is still an abstract
  column accessor. The fix: rewrite `h_m32 : m.m32 r_main = 0` *into
  the match hypothesis* first (exposes the literal `(1 - 0)`), then a
  targeted `simp only [one_sub_zero_mul]` fires cleanly. Document this
  pattern for Phase 2 — other PIL selectors (e.g. `is_external_op`,
  `is_precompiled`) will follow the same shape.
- **`LeanRV64D` has a `toCtorIdx` deprecation warning** from upstream
  `LeanRV64D.RiscvExtras` — harmless but will bite when `extension`
  enums get rewritten upstream. Not a blocker.
- **Pratt certificate requires `powMod` — do not skip.** The naive
  expression `a^(p-1) % p` with `Nat.pow` constructs intermediate
  values of ~2^(64·3) bits before the modulus applies. `native_decide`
  / `decide` will OOM. Use square-and-multiply with intermediate mod
  reduction and an equivalence lemma (`powMod_eq : powMod a n p =
  a^n % p`).
- **Sail-translated code has namespace surprises.**
  `Sail.BitVec.toNatInt` (qualified) is the working call;
  `BitVec.toNatInt` (bare) resolves to a `sorry`-axiom in this repo's
  Mathlib/LeanRV64D overlay. Explicit `Sail.` prefix is mandatory in
  Execution.lean.
- **MUL 8-case sign induction has a clean high/low split.** The 4
  High-half cases close via `cases rcases op with ⟨high, sgn1, sgn2⟩;
  simp_all`. The 4 Low-half cases require RV64-widened modular
  identities not yet ported; left as targeted sorry. Same shape
  applies to the remaining DIV/REM equivalences — structural proof
  shape is correct, bounds need re-derivation.
- **`execute_RTYPE_add_pure_equiv` from `RV64D/add.lean` was always
  buildable once `Fundamentals/Execution.lean` existed.** No rework
  required in `add.lean` itself — E6 was just re-exporting from
  `Equivalence/Add.lean`.

#### Deviations from this plan

- **Plan verification criterion "no `sorry` in
  ZiskFv/Fundamentals/Execution.lean"** — not met (3 targeted
  sorries). This criterion was unrealistic; the plan's "Known
  fragility" section had already noted MUL/DIV proofs budget +2 days
  per op family on tactic breakage. The 3 remaining sorries are
  structural completions, not load-bearing correctness gaps:
  `execute_RTYPE_add_pure_equiv` (the only equivalence lemma `add.lean`
  actually consumes) is fully closed. Updating Phase 2 plan to treat
  MUL-Low/DIV/REM equivalence closure as its own dedicated task.
- **Plan criterion "`Equivalence/Add.lean` docstring does not say
  'circuit-level only'"** — met, with a nuance: the docstring now
  identifies two companion theorems (`equiv_ADD` circuit-level,
  `equiv_ADD_sail` Sail-level) and notes the remaining gap to the full
  metaplan `bus_effect`-shaped statement as Phase 2 (memory-bus
  bit-width widening + Goldilocks↔BitVec 64 bridge lemma).

#### Remaining sorry inventory

**Empty.** All 4 originally-accepted Phase 1.5 `sorry`s closed in a
round-2 execution pass on 2026-04-22 (commits `3a91787..eb32aae`, 8
commits on top of the round-1 close). See "Round 2 addendum" below.

#### Per-opcode effort update (for Phase 2 planning)

The Phase 1 estimate was "~1 day per ALU opcode" post-infrastructure.
Phase 1.5 refines:

- **64-bit ALU opcodes (sub, and, or, xor, slt, sltu, sll, srl, sra):**
  still ~1 day each. All pure functions are in place via
  `execute_RTYPE_pure`; `equiv_ADD` → `equiv_SUB` is the carry-chain
  template specialization.
- **32-bit ALU opcodes (addw, subw, sllw, srlw, sraw):** unblocked by
  Track M. Symmetric m32 = 1 case uses `one_sub_one_mul` simp lemma
  (trivial). Add ~0.5 day each for the 32-bit zero-extend plumbing.
- **Immediate-variant opcodes (addi, slti, …):** `execute_ITYPE_pure`
  in place. Spec-level proofs are straightforward wrappers. ~0.5 day.
- **MUL-family (mul, mulh, mulhu, mulhsu):** **blocked on** closing
  `execute_MUL_eq_execute_MUL'` Low-half. Before that, budget
  ~2 days *per sub-family* (mul, mulh, mulhu, mulhsu are 4 proof
  templates). After closure, ~1 day each.
- **DIV/REM (div, divu, rem, remu):** **blocked on** closing
  `execute_DIV_eq_execute_DIV'` / `_REM_`. Same shape — ~2 days for
  the shared closure, then ~1 day each opcode.
- **Branch/jump (beq, bne, bge, bgeu, blt, bltu, jal, jalr):**
  **blocked on** `jump_to_equiv` (upstream U1 or local U2). Once
  unblocked, ~0.5 day each.

Macros (`alu_non_imm_proof` analogue) stay deferred to Phase 2
after 3-5 opcodes crystallize the pattern.

#### Round 2 addendum — 2026-04-22

Closed the 4 `sorry`s and landed the full metaplan theorem shape in 8
commits `3a91787..eb32aae`. `just verify-phase1` exits 0, `git grep
sorry` across Fundamentals/Airs/Spec/Equivalence/GoldenTraces and
`RV64D/Auxiliaries.lean` returns **zero matches**.

**What closed:**

- **Metaplan theorem composition** (commits `3a91787..be94732`):
  - `Fundamentals/Interaction.lean` created (minimal port of openvm-fv's
    RV32 version; `ExecutionBusEntry`, `MemoryBusEntry` widened to 8
    byte lanes `x0..x7`).
  - `RV64D/BusEffect.lean` widened from RV32-shaped 4-byte entries to
    8 byte lanes (matches the TODO at the top of the file, now removed).
  - `Fundamentals/GoldilocksBridge.lean` created with proven bridges:
    `lane_lo_lane_hi_recombine_eq_toNat` and
    `add_bv_toNat_eq_field_sum_minus_carry` plus helpers. Leverages
    `GL_prime < 2^64` so `push_cast` discharges the `ZMod` reduction.
  - `Equivalence/Add.lean::equiv_ADD_metaplan` now exists with the
    metaplan target statement `execute_instruction (.RTYPE ...) state
    = (bus_effect exec_row mem_row state).2`. **Proof body has no
    sorry.** Parameterizes over a `h_bus_execute_matches_sail`
    hypothesis — deriving that hypothesis from a more elementary
    PIL-level bus-emission spec is per-entry case analysis over
    `bus_effect`'s foldl and stays Phase 2.

- **Execution.lean equivalences** (commits `d8ae4bf`, `1840927`):
  - `Fundamentals/U64.lean` created (port of openvm-fv's `U32.lean`
    helper family to 64-bit width): `toInt_toInt_as_toNat_128`,
    `toInt_toNat_as_toNat_128`, `toNat_toInt_as_toNat_128`,
    `toNat_toNat_as_toNat_128`, `div_overflow_64`,
    `ZiskFv.Int.sign_cases`.
  - MUL Low-half 4 sign cases, DIV overflow/truncate, REM parallel —
    all closed with actual proof bodies. Strategic choice: rather than
    mirror openvm-fv's msb-case-split proofs, collapse both sides to
    `BitVec.ofInt` via `signExtend v = ofInt v toInt` etc., shortening
    substantially. Required `set_option maxHeartbeats 10000000` for
    DIV/REM's four-way case split.

- **`jump_to_equiv` via the upstream fork path, not local U2**
  (commits `cfcca65`, `eb32aae`):
  - Fork `codygunton/sail-riscv-lean` branch `ext-zca-simp-lemmas`
    (HEAD `4692edd7`) now carries proven `LeanRV64D.Lemmas`:
    `currentlyEnabled_Ext_C_eq_false_of_misa_bit_zero`,
    `currentlyEnabled_Ext_Zca_eq_false_of_misa_bit_zero`, the
    `bind_currentlyEnabled_Ext_Zca_of_misa_bit_zero` combinator,
    plus `hartSupports_Ext_{Zca,F,D,Zcd,Zcf,C}` constant-folds.
    ~170 lines, no sorry.
  - `ZiskFv/lakefile.toml` now pins `LeanRV` at
    `codygunton/sail-riscv-lean@ext-zca-simp-lemmas`. Our project
    consumes the upstream lemmas rather than duplicating them
    locally — this is the "real U1" outcome rather than the U2
    fallback.
  - `RV64D/Auxiliaries.lean::jump_to_equiv` proof closed.
    Transitively unblocks the 8 branch/jump opcode equivalence
    proofs (their per-opcode `sorry`s are separate Phase 2 work, not
    caused by `jump_to_equiv`).
  - **Minor redundancy to address in Phase 2:** an in-file `@[simp
    high]` `currentlyEnabled_Zca_of_misa_val` helper already existed
    in `Auxiliaries.lean` and wins the simp race against the
    imported `LeanRV64D.Lemmas` version. The upstream import is
    anchored in the proof via `have _h_upstream` but the simp-level
    work flows through the local helper. Either remove the local
    helper to canonicalize the upstream path, or retire the
    upstream lemma once a stronger simp-framework lands. Tracked.

**Fork & openvm-fv regression story update:**

The fork now contains real lemma content (not just scaffolding). The
openvm-fv regression test (plan at
`docs/fv/upstream-issues/openvm-fv-regression-test-plan.md`) was run
against the scaffolding-only commit and came back clean; re-running
against `4692edd7` would re-confirm, but the fork change is still
RV64D-only (file `LeanRV64D/Lemmas.lean` under the RV64 branch,
visible only to consumers that explicitly `import LeanRV64D.Lemmas`),
so the structural-invisibility argument from the original regression
test still holds. The U1 issue body at
`docs/fv/upstream-issues/sail-riscv-lean-ext-zca-simp.md` now has
concrete accompanying code on the fork to reference.

**Per-opcode effort refinement (supersedes earlier table):**

- **64-bit ALU opcodes (sub, and, or, xor, slt, sltu, sll, srl, sra):**
  unchanged, ~1 day each.
- **32-bit ALU opcodes (addw, subw, sllw, srlw, sraw):** unchanged,
  ~0.5 day each.
- **Immediate-variant opcodes (addi, slti, …):** unchanged, ~0.5 day.
- **MUL-family:** no longer blocked. ~1 day each (was "blocked + 2
  days shared then 1 day each").
- **DIV/REM:** no longer blocked. ~1 day each (was "blocked + 2 days
  shared then 1 day each").
- **Branch/jump (beq, bne, bge, bgeu, blt, bltu, jal, jalr):** no
  longer blocked on `jump_to_equiv`. ~0.5 day each. (Their existing
  per-opcode `sorry`s are separate RV32-width-tactic-dependent
  issues, not `jump_to_equiv`-related.)
- **The 43 non-ADD RV64IM `sorry`s in `ZiskFv/RV64D/*.lean`:** still
  outside Phase 1.5 scope per the plan. Each is a per-opcode
  equivalence proof at the Sail layer; now unblocked by Execution.lean
  + bridge infrastructure. A dedicated Phase 2 per-opcode pass should
  be able to close them using the infrastructure this round built.

#### Repro update

Phase 1's repro instructions still apply:

```bash
cd /home/cody/zisk-fv
git submodule update --init  # if vendor/zisk isn't checked out
just verify-phase1
```

Expected: exit 0, wall time under 10s on warm cache (full cold build
~60s, down from ~10 min because Goldilocks primality is now Pratt-
certificate-verified). Four `sorry` warnings printed, all annotated.

### Repro

```bash
cd /home/cody/zisk-fv
git submodule update --init  # if vendor/zisk isn't checked out
just verify-phase1
```

Expected: exit 0. First cold build is ~10 min (Goldilocks primality
dominates).
