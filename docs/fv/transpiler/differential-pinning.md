# Lean Transpiler Model And Differential Pinning

`ZiskFv/Transpiler/Static.lean` is a non-trusted Lean model of the static
RV64IM slice of ZisK's Rust transpiler. It covers only fields fixed by the
instruction bits and by `ZiskInstBuilder`: source selectors, immediate chunks,
store selectors and offsets, jump offsets, `store_pc`, `set_pc`, `ind_width`,
`is_external_op`, `m32`, and row count.

It deliberately does not model runtime register contents, memory values, Main
witness columns, Sail state, or the ROM/Main/dataflow bridges covered by the
explicit `transpiler_contract_sound` bridge axiom.

The Rust harness in `tools/transpiler-diff` constructs `riscv::RiscvInstruction`
values directly, runs production `Riscv2ZiskContext::convert`, projects the
resulting `ZiskInst` rows to the same static schema, and compares those rows
against `ZiskFv.Transpiler.Static.transpile` through
`tools/transpiler-diff/LeanOracle.lean`.

Default CI coverage exhausts all register fields and shift immediates. It also
exhausts 12-bit I/S/B immediates across the x0/x1/x31 register partition and
checks all register combinations at immediate boundaries.

Set `ZISK_DIFF_FULL_12BIT=1` for the full 12-bit Cartesian sweep over all
register combinations for I/S/B/load families. Split that sweep with
`ZISK_DIFF_12BIT_SHARD_COUNT=N` and `ZISK_DIFF_12BIT_SHARD_INDEX=K`.

U/J instructions use a boundary partition suite by default; set
`ZISK_DIFF_FULL_UJ=1` to run the large immediate sweep locally. Split that sweep
with `ZISK_DIFF_UJ_SHARD_COUNT=N` and `ZISK_DIFF_UJ_SHARD_INDEX=K`.

This is evidence, not proof of the production Rust transpiler. Narrowing or
retiring `transpiler_contract_sound` still requires separate proof work for the
ROM/Main/register and memory bridges, plus a reviewed trust-ledger update.

## Classified Mismatch: JALR Proof Shape

The Lean model and Rust differential harness agree on current upstream JALR
lowering:

* `imm % 4 = 0`: one external `and` row with `set_pc = 1`, `store_pc = 1`;
* otherwise: an `add` row followed by an `and` row.

The existing proof stack still proves a legacy single-row internal-`copyb`
JALR archetype. That mismatch is not a Lean-model/Rust mismatch; it is an
existing proof/trust mismatch exposed by the model. Until the JALR equivalence
is refactored to the real `and`/two-row lowering, `transpiler_contract_sound`
must still cover the legacy JALR contract explicitly.
