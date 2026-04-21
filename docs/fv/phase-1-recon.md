# Phase 1 reconnaissance

Frozen context for `ai_plans/zisk-fv-phase-1.md`. Captures the four findings the
plan references; do not let downstream tasks drift from these citations.

## 1. Main AIR opcode dispatch

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

## 2. Pilout extractor coverage gap

`zisk.pilout`'s `Main` AIR has 146 constraints. The current extractor
(`tools/zisk-pil-extract/src/main.rs:341-352`) renders `Constant`,
`WitnessCol`, and `Expression` operand kinds; the other six kinds bail out.
Empirically `Main` extraction without `--skip-unsupported` aborts immediately
on the first `FixedCol` reference. Operand-kind coverage —
`FixedCol` / `Challenge` / `AirValue` for ADD; `PeriodicCol`,
`ProofValue`, `AirGroupValue`, `PublicValue`, `CustomCol` deferred — is
Phase 1's first hard gate (Tasks 1, 2 in the plan).

Constraint kinds are also currently flattened: `EveryRow`, `FirstRow`,
`LastRow`, `EveryFrame` all render as `constraint_N`
(`render_constraint`, `main.rs:255-287`). Phase 1 separates them so the
bridging proofs can quantify over the right row domain (Task 1).

## 3. openvm-fv ADD chain shape (proof template)

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

## 4. LeanRV64D status

`NethermindEth/sail-riscv-lean` `main` exposes `LeanRV64D`, but commits
flag it as Sail-auto-translated WIP. We expect to discover and patch lemmas
on contact. Track A budget assumes ≤4 hours of upstream churn before falling
back to inlining what Track B Task 10 needs.

## 5. Golden-trace plumbing

ZisK's SDK exposes `ProverClient::get_instance_trace(instance_id, first_row,
num_rows, offset)` returning `Vec<proofman_common::RowInfo>`. Reference call
site: `vendor/zisk/examples/sha-hasher/host/bin/execute.rs`. Phase 1's harness
(Task 13) wires this; it does not implement it.

## ADD subset of Main constraints (working set)

Tasks 3, 8 restrict Main extraction to constraints that are (a) wired by the
ADD transpilation per `vendor/zisk/core/src/riscv2zisk_context.rs:631-643`
(`create_register_op` calls `src_a("reg", rs1)`, `src_b("reg", rs2)`,
`op("add")`, `store("reg", rd)`, `j(4, 4)`), or (b) gate the operation-bus
hop. Concrete index list is established by Task 3 against a fresh
`--list-constraints` dump and pinned in `Main.hand.lean`.

## Provenance pin

`pil/zisk.pilout` and the expectations in this document are taken from ZisK
commit `48cf7ccef`. Task 1b vendors that exact commit at `vendor/zisk/`.
