# Lean 4.28 Compatibility Probe

The main `zisk-fv` Lake project is pinned to Lean 4.28.0. The pinned Aeneas
runtime used by this extraction harness is pinned upstream to Lean 4.30.0-rc2, so the extraction harness
script applies a small compatibility patch before building the generated Lean.

`scripts/aeneas-rv64im-lean428-compat.sh` rebuilds the pinned extraction and
checks that the generated Aeneas RV64IM package builds on Lean 4.28.

The patch does four things:

1. Forces both the extraction harness package and copied Aeneas runtime to Lean 4.28.0.
2. Re-pins Aeneas' mathlib dependency from `v4.30.0-rc2` to `v4.28.0`.
3. Patches small Lean API drifts in Aeneas' copied runtime:
   `Monoid.toPow` to `Monoid.toNatPow`, `PredTrans` constructor fields to
   `apply`/`conjunctive`, and removes `@[implicit_reducible]`.
4. Narrows the generated transpiler import from the full `Aeneas` umbrella to
   the scalar/array/default runtime surface used by this extraction, and strips
   generated `@[discriminant isize]` attributes that Lean 4.28 does not know.

Current result: `Rv64imExtract.Generated` and the full `Rv64imExtract` bridge
build on Lean 4.28 after the compatibility patch.

This means the generated Aeneas decoder/lowerer is no longer isolated on the
Aeneas Lean 4.30 toolchain. It can be consumed by a Lean 4.28 package after the
compatibility patch. The remaining work to retire `transpiler_contract_sound`
is not importability; it is to connect the generated decode/lower result to
the `Valid_Main` row facts currently asserted by the transpiler contract.

Until that row-contract bridge is proved or checked, `transpiler_contract_sound`
cannot be retired just by importing the generated Aeneas file.
