# Lean Transpiler Model With Differential Pinning

Status: implemented in this branch, including the more ambitious
trust-ledger narrowing requested after the original evidence-building
plan.

## Scope

This plan adds a non-trusted Lean model of the RV64IM static transpiler
surface and a Rust-vs-Lean differential harness against ZisK's pinned
production `Riscv2ZiskContext::convert`.

The model covers static row fields: opcode, source selectors, immediate
chunks, store kind and offset, `store_pc`, `set_pc`, `ind_width`,
`jmp_offset1`, `jmp_offset2`, `is_external_op`, `m32`, and row count.
It intentionally excludes runtime register contents, memory contents,
Sail-state bridges, and Main-AIR witness construction.

## Implemented Artifacts

* `ZiskFv/Transpiler/Static.lean` — executable Lean model.
* `tools/transpiler-diff/` — Rust harness plus Lean oracle.
* `docs/fv/transpiler/differential-pinning.md` — operational notes,
  coverage modes, and the production JALR proof shape.
* `nix/test.nix` — quick differential suite wired into the project test
  command.

## Coverage Modes

The default suite exhausts all register fields for R-type, W-type,
M-extension, shift-immediate, and boundary-immediate cases. It exhausts
all 12-bit I/S/B/load immediates over the x0/x1/x31 register partition,
checks all register combinations at immediate boundaries, and runs a
U/J boundary partition suite.

Full finite-domain modes:

```bash
ZISK_DIFF_FULL_12BIT=1 \
ZISK_DIFF_12BIT_SHARD_COUNT=N \
ZISK_DIFF_12BIT_SHARD_INDEX=K \
cargo run --manifest-path tools/transpiler-diff/Cargo.toml --quiet

ZISK_DIFF_FULL_UJ=1 \
ZISK_DIFF_UJ_SHARD_COUNT=N \
ZISK_DIFF_UJ_SHARD_INDEX=K \
cargo run --manifest-path tools/transpiler-diff/Cargo.toml --quiet
```

## Trust Replacement

The legacy source-level `transpile_<OP>` axioms have been converted to
theorem wrappers over the single explicit bridge axiom
`ZiskFv.Trusted.transpiler_contract_sound`. This is an axiom narrowing,
not a proof that Rust is correct: Rust-vs-Lean agreement remains
external differential evidence, and runtime witness facts remain inside
the explicit bridge.

The trust ledger, axiom index, and semantic closure baselines are
regenerated around `transpiler_contract_sound` plus three explicit
JALR source-C / unaligned-final-row bridge axioms.

## Completion Audit

Original plan requirements:

* Non-Trusted Lean RV64IM static transpiler model: implemented in
  `ZiskFv/Transpiler/Static.lean`.
* Production Rust differential harness: implemented in
  `tools/transpiler-diff`, calling `Riscv2ZiskContext::convert` and
  comparing projected `ZiskInst` rows field-for-field against the Lean
  oracle.
* Proof-field testing: default CI exhausts all register fields for
  register, W, M-extension, and shift-immediate families; exhausts all
  12-bit immediates over the x0/x1/x31 partition plus all-register
  immediate boundaries; and provides sharded full 12-bit and U/J modes.
* Builder projection unit tests: `cargo test` covers x0 source rewrite,
  rd=x0 store elision, signed-immediate splitting, `store_pc`, `set_pc`,
  `ind_width`, `m32`, and row-hash field ordering.
* Trust story: documented in `docs/fv/transpiler/differential-pinning.md`
  and `docs/fv/trusted-base.md`. Rust-vs-Lean agreement is explicitly
  external evidence, not a Lean proof of Rust.
* Mismatch policy: the JALR proof/trust mismatch found by the model is
  resolved in this branch. The equivalence proof consumes the production
  final `OP_AND` row, and the unaligned `ADD -> lastc -> AND` bridge is
  derived from explicit non-segment Main source-C axioms plus an explicit
  unaligned final-row selector contract.
* More ambitious trust replacement: the former source-level
  `transpile_<OP>` axioms are theorem wrappers over
  `transpiler_contract_sound`; the global closure baseline is regenerated
  at 75 axioms.

Verification command used for this branch:

```bash
nix run .#test
```

That command runs the Rust unit tests, the default 2,231,425-case
Rust-vs-Lean differential suite, `lake build`, the V1 syntactic trust
gate, the V2 semantic trust gate, and the flake reproducibility check.
