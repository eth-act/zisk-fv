# Aeneas RV64IM Transpiler Extraction

This isolated Lake project de-risks replacing the hand-written Lean static
transpiler with Lean generated from the Rust `rv64im_transpiler` module.

It intentionally does not yet replace the main `zisk-fv` transpiler contract.
The main repo is pinned to Lean 4.28.0, while the current Aeneas Lean runtime is
pinned upstream to Lean 4.30.0-rc2. The extraction script applies a documented
compatibility patch so the generated decoder/lowerer and bridge build on Lean
4.28. See [`LEAN428_COMPAT.md`](LEAN428_COMPAT.md).

## Run

From the repository root:

```sh
nix run .#aeneas-rv64im-extract
```

This uses the Aeneas flake revision pinned in the repository `flake.lock`.
For ad hoc experiments against another Aeneas revision, run the script
directly with `AENEAS_FLAKE=... scripts/aeneas-rv64im-extract.sh`.

The script:

1. Resolves the pinned Aeneas flake source.
2. Copies Aeneas' Lean runtime into `.aeneas-lean/`.
3. Runs Charon on the narrowed Rust entry points:
   `decode_rv64im32`, `lower_rv64im32`, and `decode_and_lower_rv64im32`.
4. Runs Aeneas with the Lean backend.
5. Builds the isolated bridge lemmas and cross-model cases.

Generated files and local Lake/runtime artifacts are gitignored.

For a cheap checkpoint check of the generated manifest files already present
in the workspace, run:

```sh
scripts/check-aeneas-rv64im-manifest.sh
```

This does not rerun Charon or Aeneas. It checks that the generated Aeneas,
main-static, and cross-model files still contain 71 valid cases, 3 invalid
decode cases, 71 cross-model equalities, and the AUIPC/JAL/JALR x0 cases that
exercise `store_reg(rd, true)` lowering to `storeNone`.

To probe whether the generated Aeneas transpiler can be imported directly into
the main Lean 4.28 project, run:

```sh
scripts/aeneas-rv64im-lean428-compat.sh
```

This should rebuild the pinned extraction and build the generated Aeneas bridge
under Lean 4.28.

## Bridge Coverage

`Rv64imExtract/Bridge.lean` normalizes generated Aeneas rows into a small
`Nat`/`Int`/`Bool` row view and proves concrete decode/lower equalities for:

- `ADDI x5, x0, -1` (`0xfff00293`)
- `JALR x1, 6(x2)` (`0x006100e7`), covering the two-row unaligned case
- `SD x3, 8(x4)` (`0x00323423`), covering memory-store row shape

The script also runs `zisk/core/examples/aeneas_bridge_cases.rs`, which emits
three files from one shared encoded-word manifest. The Rust generator and the
extraction script both fail on manifest drift: the expected surface is 71 valid
encoded-word cases, 3 invalid decode cases, and 71 cross-model equality
theorems. The manifest includes x0 AUIPC, JAL, and aligned/unaligned JALR cases
to cover the production `store_reg(rd, true)` branch where `rd = x0` lowers to
`storeNone`.

- `Rv64imExtract/GeneratedCases.lean` builds `native_decide` bridge theorems
  for the Aeneas-extracted decoder/lowerer across canonical RV64IM instruction
  words, plus invalid-word decoding checks.
- `MainModelCases.lean` builds matching `native_decide` bridge theorems for
  the main Lean 4.28 static transpiler model on the same decoded cases.
- `Rv64imExtract/CrossModelCases.lean` imports both the Aeneas extraction and
  the main `ZiskFv.Transpiler.Static` model, then proves the two row lists are
  equal for each manifest instruction word.

Together these cases exercise the Aeneas-extracted instruction decoder and tie
its lowering output directly to the hand-written main Lean static model over
the same case manifest.

This is still static decode/lower evidence. It does not prove that an arbitrary
`Valid_Main` witness row has the operand lanes and control columns asserted by
`ZiskFv.Trusted.transpiler_contract_sound`; retiring that axiom still requires
threading or proving a row-provenance bridge from extracted/static rows to Main
witness columns.

The main repo now has the proof-facing target for that bridge:
`ZiskFv.Compliance.MainStaticRowProvenance`. It ties a selected `Valid_Main`
row and its `MainRowWithRom` ROM columns to one
`ZiskFv.Transpiler.Static.ZiskStaticRow` and exposes static/control projection
lemmas. It deliberately leaves runtime register/dataflow lane facts as a
separate obligation.

The printed axiom closures include Aeneas runtime axioms/sorries and the
`native_decide` axiom for each concrete bridge theorem. That is acceptable for
this extraction harness; the next implementation phase should replace concrete
native checks with reusable proof-facing bridge lemmas where practical.
