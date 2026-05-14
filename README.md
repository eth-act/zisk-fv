# zisk-fv

⚠️This code has is currently undergoing quality control. It should not be regarded as showing that any version of ZisK's circuits correctly implement the RISC-V ISA standard. ⚠️

Lean 4 formal verification of the [ZisK](https://github.com/0xPolygonHermez/zisk)
zkVM against the [Sail RISC-V specification](https://github.com/rems-project/sail-riscv),
via [`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean)'s
`LeanRV64D` module. This effort follows the pattern established by [openvm-fv](https://github.com/openvm-org/openvm-fv), and we are grateful to the authors of that library for their excellent work.

**Status:** the verification claim is the global compliance theorem
`ZiskFv.Equivalence.Compliance.Global.zisk_riscv_compliant_program_bus`
(in `ZiskFv/Equivalence/Compliance/Global.lean`), which dispatches all
63 RV64IM opcodes through a 35-arm `OpEnvelope` sum type to per-opcode
`equiv_<OP>_from_trust` wrappers, each discharging its canonical
`equiv_<OP>` theorem's promise hypotheses from the trust ledger. The
trusted computing base is **122 axioms across 12 classes** (51
transpile contracts + 14 bus / lookup soundness + 35 Arith range /
table / Euclidean pins + 14 Binary / BinaryExtension lookup soundness
+ 3 range-bus byte-range + 1 memory-state load bridge + 4 platform
scope — full per-class breakdown in `docs/fv/trusted-base.md`), 0
sorries. Closure mechanically enforced: V2 gate
`check-closure-vs-baseline` asserts
`#print axioms zisk_riscv_compliant_program_bus` equals
`trust/baseline-axioms.txt` exactly. The load-bearing claim is
`lake build`: every per-opcode equivalence theorem + every wrapper +
the uber theorem typechecks. Run `nix run .#test` for the full suite
(cargo + lake + trust gate V1 + V2 + flake repro check).

## Layout

| Path                   | Purpose                                                                                                |
| ---------------------- | ------------------------------------------------------------------------------------------------------ |
| `docs/fv/`             | Live library-reference notes: trust ledger, extractor contract, AIR inventory                          |
| `tools/pil-extract/`   | Rust CLI: decodes `.pilout` protobuf → Lean constraint definitions                                     |
| `ZiskFv/`              | Lake 4 package (mathlib + LeanZKCircuit + LeanRV, toolchain v4.26.0). See [Inside `ZiskFv/`](#inside-ziskfv) below. |
| `zisk/`                | ZisK source tree (git submodule, pinned at `48cf7ccef`)                                                |
| `trust/`               | Trust-boundary baselines + enforcement scripts. See `trust/README.md`.                                 |
| `flake.nix`, `nix/`    | Nix flake that builds the pilout + Sail-Lean spec + extracted Lean reproducibly. See `nix/README.md`.  |
| `build/`               | Generated artifacts. Gitignored — produced by `nix run .#populate`. See [Inside `build/`](#inside-build) below. |
| `docs/site/`           | Single-page trust-boundary explainer (run `docs/site/serve.sh`, port 4044).                            |

## Inside `ZiskFv/`

The Lake 4 package. Subdirectories track the proof's data flow: foundations
→ extraction → per-AIR named layer → per-opcode lifted semantics → Sail-side
mirror → equivalence theorems.

```
ZiskFv/
├── Fundamentals/   foundations: Goldilocks field, BitVec/U64 lemmas, transpiler axioms
├── Extraction/     3 hand-written extraction-layer files (auto-generated set lives in build/extraction/)
├── Airs/           per-AIR named-column wrappers + single-AIR correctness theorems
├── Circuit/        per-opcode lifted circuit semantics — one .lean per RV64IM opcode
├── Sail/           per-opcode Sail-side mirrors with equivalence-to-LeanRV64D lemmas
├── Tactics/        instruction-shape archetype tactics that drive the per-opcode proofs
├── Equivalence/    the per-opcode canonical equiv_<OP> theorems
├── Compliance.lean global theorem zisk_riscv_compliant_program_bus
├── Compliance/     per-Op dispatch (Dispatch.lean) + trust-discharge wrappers (FromTrust/<Op>.lean ×63)
└── ZiskFv.lean     root module — imports the whole tree
```

### `ZiskFv/Fundamentals/`

Foundational definitions and lemmas the rest of the tree builds on.
`Goldilocks.lean` defines `FGL := Fin (2^64 - 2^32 + 1)` and the canonical
`[Field FGL]` instance — declared once globally and never shadowed
(shadowing it as a proof-local variable defeats `ring`).
`PrattCertificate.lean` proves the prime is prime via `native_decide`
(~6 min cold; the slowest single proof in the build). `U64.lean` and the
`PackedBitVec/` subdirectory hold the fixed-width arithmetic lemmas needed
for carry-free decompositions across packed lanes. `Transpiler.lean` and
`TranspileConsumers.lean` declare the `transpile_*` axioms that bridge
RISC-V instruction encoding to ZisK's microinstruction format (class
#1 — 51 axioms — in `docs/fv/trusted-base.md`). `Execution.lean` and
`Interaction.lean` define generic execution-trace and bus-interaction
structures shared across all AIRs.

### `ZiskFv/Extraction/`

Three hand-written extraction-layer files that supplement the auto-generated
set under `build/extraction/Extraction/`:

- `ArithTable.lean` — hand-transcribed from
  `zisk/state-machines/arith/src/arith_table_data.rs::ARITH_TABLE` (74 rows).
  The Rust constant is itself generated from PIL with `generate_table = 1`;
  we transcribe rather than extending the Rust extractor.
- `MemoryBuses.lean` — hand-curated subset of memory-bus emissions
  (bus_id = 10) extracted from PIL2 `gsum_debug_data` hints.
- `OperationBuses.lean` — hand-written operation-bus emission for the Main
  AIR (bus_id = 5000); needed because the auto-extracted form became a
  multiplicity-0 stub starting v0.16.0.

### `ZiskFv/Airs/`

The per-AIR layer. For each ZisK AIR (`Main`, `Binary`, `BinaryAdd`,
`BinaryExtension`, `Arith`, `Mem`, `MemAlign{,Byte,ReadByte,WriteByte}`)
this layer provides:

- a `Valid_<AIR>` structure naming each column (so `m.cout_1 row` instead of
  `Circuit.main circ (column := 9) (row := row) (rotation := 0)`), with
  `_def` lemmas tying the names back to the underlying anonymous accessors;
- iff-bridges that turn each anonymous `constraint_N_every_row` into a
  meaningfully-named predicate (e.g. `core_every_row` for BinaryAdd's carry
  chain);
- **single-AIR correctness theorems** — proofs that one AIR's constraints,
  in isolation, imply the BitVec relation they claim. These are the heaviest
  files in the layer: `BinaryPackedCorrect.lean` is 2,109 lines,
  `BinaryExtensionPackedCorrect.lean` is 2,804;
- bus-protocol machinery (`OperationBus.lean`, `OpBusEffect.lean`,
  `BusEmission.lean`, …) and lookup-table soundness (`BinaryTable.lean`,
  `BinaryExtensionTable.lean`, plus `Arith/ArithTable.lean` for the
  table-soundness theorem that consumes `Extraction/ArithTable.lean`'s
  table data).

Files are organized **by ZisK constraint table**, not by RISC-V instruction
— a single AIR (e.g. Binary) covers many opcodes (ADD, SUB, AND, OR, XOR,
all branches, …).

### `ZiskFv/ZiskCircuit/`

Per-opcode lifted circuit semantics — one file per RV64IM opcode (62
files total, including shared infrastructure like `MemModel.lean`,
`MulField.lean`, `DivFieldSigned.lean`). Each file composes the relevant `Airs/` pieces via
the operation-bus abstraction (`Airs/OperationBus.lean::matches_entry`) and
concludes that the involved AIR rows together produce `f(inputs)` for some
BitVec function `f`. The math stays in `Fin p` (Goldilocks); the BitVec lift
itself happens in `Equivalence/`. Files are organized **by RISC-V opcode**,
not by AIR — `Circuit/Add.lean` projects out the Add behaviour from
`Airs/Main.lean` + `Airs/Binary/BinaryAdd.lean`, both joined by their
matching bus row.

### `ZiskFv/Sail/`

Per-opcode Sail-side mirrors (lowercase, one per opcode: `add.lean`,
`lw.lean`, …, 65 files total = 63 opcodes + `Auxiliaries.lean` +
`BusEffect.lean`). Each
opcode file does two jobs:

1. **Defines a pure version** in `PureSpec` namespace — the Sail-extracted
   `execute_instruction` rewritten in clean BitVec/Option terms, monad
   stripped, decoder dispatch removed, ZisK-irrelevant trap arms eliminated
   via the four platform axioms in `Auxiliaries.lean` (PMP/CLINT/PMA inert,
   Zicfilp disabled — all scope-honest for ZisK's RV64IM target, ledger
   entries 10–13).
2. **Proves an equivalence lemma**
   `execute_<OP>_pure_equiv : LeanRV64D.Functions.execute (.<shape> …) state = … = PureSpec.execute_<shape>_<op>_pure …`.
   The lemma is what keeps the pure form honest — drift between
   `build/sail-lean/` and the pure form is a build failure, not a silent
   trust extension.

`BusEffect.lean` defines the `bus_effect` function that produces a
Sail-shaped state update from circuit-side rows — this is the RHS of every
equivalence theorem.

### `ZiskFv/Tactics/`

Archetype tactics: instruction-shape templates that drive the per-opcode
proofs. The 12 archetypes (`ALURTypeArchetype`, `ALUITypeArchetype`,
`BranchArchetype`, `LoadArchetype`, `StoreArchetype`, `JumpArchetype`,
`MulArchetype`, `ShiftArchetype`, `SignExtendLoadArchetype`,
`RTypeWArchetype`, `UTypeArchetype`, `ArithSMArchetype`) each package the
standard simp/rewrite cascade for one instruction shape. Per-opcode files
under `Equivalence/` mostly instantiate the relevant archetype with the
opcode's specific Sail-side rewrite and `Circuit/` compositional theorem;
this is what makes 63 individual proofs feasible without 63 bespoke proof
scripts.

### `ZiskFv/Equivalence/`

The top-level FV theorems, organised in three layers:

1. **Per-opcode canonical theorems** — one file per opcode, each
   containing
   `equiv_<OP> : execute_instruction (.<shape> …) state = (bus_effect exec_row mem_row state).2`.
   Both sides live in Sail's state space: the LHS is Sail's `execute`;
   the RHS comes from `Sail/BusEffect.lean`. Every parameter is in one
   of the safe trust classes ({CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE,
   TRANSPILE-BRIDGE, TRANSPILE-PIN}); uniformly enforced by the trust
   gate's `check-no-output-eq.sh` (V1) + `check-no-output-eq-v2.sh`
   (V2) against `trust/forbidden-param-shapes.txt` /
   `forbidden-types.txt` — no exemptions, including loads (the 7 load
   opcodes were closed by deriving their cross-entry rd-value byte
   equations from circuit witnesses, see
   `Circuit/LoadDerivation.lean` and `Circuit/SextLoadBridge.lean`).
   Bus-precondition variants (`equiv_<OP>_from_bus`,
   `equiv_<OP>_bus_self`, `equiv_<OP>_op_bus`) bridge alternate
   precondition shapes into the same canonical conclusion.
   `WriteValueProofs/` factors out shared rd-value lemmas across
   opcodes that share a derivation pattern.

2. **`Compliance/<Op>Exemplar.lean` wrappers** — 63
   `equiv_<OP>_from_trust` wrappers (plus `DivPilot.lean`), one per
   opcode. Each wrapper discharges its canonical theorem's promise
   hypotheses from the trust ledger, exposing only the minimal
   caller-burden surface (recorded in
   `trust/baseline-wrapper-caller-burden.txt`, drift-guarded by
   `check-wrapper-caller-burden.sh`).

3. **`Compliance/Global.lean`** — the uber theorem
   `zisk_riscv_compliant_program_bus`, dispatching all 63 opcodes
   through a 35-arm `OpEnvelope` sum type by chaining the per-op
   wrappers. **This is the verification claim.** Its transitive
   `#print axioms` closure is mechanically asserted equal to
   `trust/baseline-axioms.txt` by the V2 gate's
   `check-closure-vs-baseline` subcommand — 122 axioms, no dead
   trust, no silent additions. **`lake build` succeeding IS the
   formal-verification claim.** All 63 RV64IM opcodes covered, 0
   sorries.

## Inside `build/`

```
build/
├── sail-lean/      Sail RV64 spec compiled to Lean (LeanRV64D module). 149 generated files.
├── extraction/     Lake lib `Extraction` — auto-generated PIL2 extraction (11 per-AIR files).
└── zisk.pilout     Compiled ZisK constraint set (protobuf). The pil-extract input.
```

Everything under `/build/` is regenerated by `nix run .#populate` from
flake-pinned inputs and is gitignored. The audit surface for these
artifacts is `flake.lock` (content-hashed pins of the Sail compiler,
sail-riscv source, ZisK source, and `pil2-*` toolchain), not the files
themselves.

### `build/sail-lean/`

The Sail RV64 spec mechanically compiled to Lean by
[`NethermindEth/sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean)
(149 files). Defines `LeanRV64D.Functions.execute`, the monadic decoder
that pattern-matches every RV64GD instruction, plus all supporting types
(registers, memory model, traps, PMP, CLINT, …). This is the **trusted
source of truth** for the LHS of every equivalence theorem; per-opcode
ergonomic mirrors live in `ZiskFv/Sail/`.

### `build/extraction/`

A standalone Lake library named `Extraction`, required by the root
`lakefile.toml` via `[[require]] path = "build/extraction"`. Contains the
11 auto-generated per-AIR `.lean` files emitted by `tools/pil-extract`
from `build/zisk.pilout` (`Arith`, `Binary`, `BinaryAdd`, `BinaryExtension`,
`Buses`, `Main`, `Mem`, `MemAlign`, `MemAlignByte`, `MemAlignReadByte`,
`MemAlignWriteByte`). Each file defines anonymous `constraint_N_every_row`
predicates directly over witness columns; the human-readable named bridges
live in `ZiskFv/Airs/`. The static `lakefile.toml` and root `Extraction.lean`
are written into the directory by `nix/populate.nix` (they aren't part of
any Nix derivation), so wiping `build/` and re-running populate restores
the full lib.

### `build/zisk.pilout`

The ZisK PIL2 constraint set in protobuf form, the output of `pil2-compile`
applied to ZisK's `.pil` source tree. Input to `tools/pil-extract` (which
produces `build/extraction/Extraction/*.lean`). At ~17 GiB peak / ~24 min
wall on cold rebuild, this is the dominant cost in the `populate` pipeline.

## Trust gate (CI)

The trust boundary is **mechanically enforced** on every PR via
`.github/workflows/trust-gate.yml`, which runs both layers:
`trust/scripts/check-all.sh` (V1, 9 syntactic checks, no build) and
`trust/scripts/check-all-semantic.sh` (V2, 3 semantic checks, requires
`lake build`). Together they ensure:

**V1 (9 checks, syntactic):**

- All `axiom` / `opaque` / `constant` / `unsafe def` / `partial def`
  / `@[extern]` / `@[implemented_by]` declarations live in one of the
  files listed in `trust/allowed-axiom-files.txt`.
- The hash + name + location of every project axiom matches
  `trust/baseline-axioms.txt`. Any add, remove, rename, or subtle
  weakening of an axiom shows up as a diff on this file.
- No canonical `equiv_<OP>` theorem accepts a retired OUTPUT-EQ
  hypothesis parameter (`h_rd_val`, `h_byte_sum`, etc. — see
  `trust/forbidden-param-shapes.txt`); uniformly enforced across all
  63 opcodes (no carve-out).
- Sanity floors on axiom count (≥ 82) and canonical-theorem count
  (≥ 63), plus cross-witness check.
- Zero `sorry` under `ZiskFv/{Fundamentals,Airs,Circuit,Equivalence,Tactics,Sail}`.
- Uniformity: every one of 63 RV64IM opcodes has a canonical
  `equiv_<OP>`.
- Anti-laundering tripwires: per-theorem hypothesis count + canonical
  caller-burden ledger + wrapper caller-burden ledger all
  drift-guarded against their respective baselines.

**V2 (3 checks, semantic — `lake exe trust-gate`):**

- **Per-theorem axiom closure** (`baseline-equiv-axiom-deps.txt`):
  transitive non-kernel axiom dependencies of every canonical
  `equiv_<OP>` recorded; any silent change (additions OR removals)
  fails the gate.
- **Forbidden binder types** (`forbidden-types.txt`): walks each
  canonical theorem's binders via `forallTelescope` + `whnfR`,
  catching the `abbrev`-aliasing dodge V1's regex misses.
- **Closure vs baseline**: transitive project-axiom closure of
  `Compliance.Global.zisk_riscv_compliant_program_bus` must equal the
  set of names in `baseline-axioms.txt` exactly. Catches **dead
  trust** (axioms hash-fresh in the ledger but no longer reachable
  from the uber theorem).

To legitimately extend the trust surface, edit the relevant allowlisted
file, run `trust/scripts/regenerate.sh`, commit the updated baselines
(`baseline-axioms.txt`, `baseline-zisk-riscv-compliant.txt`,
`baseline-equiv-axiom-deps.txt`), and have a CODEOWNER review the
diff (these files are protected by `.github/CODEOWNERS`). See
`trust/README.md` for the full process and `CLAUDE.md` for guidance
to AI agents contributing to this repo.

Run `trust/scripts/check-all.sh` locally (V1, no build) and
`trust/scripts/check-all-semantic.sh` after `lake build` (V2) to see
what CI will check; `nix run .#test` runs both in sequence.

## First-time setup — build the spec + pilout

zisk-fv reads two artifacts that aren't checked into the repo: the
Sail-Lean RV64D **spec** (the Lean translation of the official Sail
RISC-V specification, which is what the proofs are _about_) and the
ZisK pilout (compiled constraint set, which is what the proofs are
_checked against_). **Both are built locally from primary source via
Nix** — nothing is pulled pre-built. Requires Nix with flakes
enabled; one-time install:

```bash
curl --proto '=https' --tlsv1.2 -sSf -L \
  https://install.determinate.systems/nix | sh -s -- install
```

Then, once after cloning:

```bash
nix run .#populate    # ~30 min cold; ~seconds warm via Nix store cache
                       # produces build/sail-lean/, build/zisk.pilout,
                       # and build/extraction/Extraction/*.lean
```

The artifacts persist under `build/`, reused
on every subsequent `lake build`. Re-run only when `flake.lock` or any
`nix/*.nix` file changes (in which case the rebuild is incremental
via the Nix store).

The lakefile points at `build/sail-lean/` via a path-based require,
so `lake build` reads the locally-built spec — there is no upstream
git dep for the spec to drift against. The audit surface for build
inputs is **`flake.lock`**: it pins every transitive dependency
(sail/sail-riscv/zisk/pil2-* sources + nixpkgs revision) by content
hash, so the build is deterministic across machines.

## Vendored ZisK inputs

The ZisK tree is pulled in as a git submodule at `zisk/`,
pinned to `0xPolygonHermez/zisk@48cf7ccef` (`Merge pull request #875
from 0xPolygonHermez/develop`). Clone with
`git clone --recurse-submodules` or run `git submodule update --init`
after cloning. The submodule is the source-text reference for
`transpile_*` axiom rationales; the pilout itself is built by the
flake from a separate pinned commit of upstream zisk (see
`flake.nix::inputs.zisk-src`).

## Getting started

After the first-time `nix run .#populate` (above), three commands cover
everything:

```bash
nix run .#populate                # refresh artifacts (cached after first build)
nix develop --command lake build  # the FV check
nix run .#test                    # full test suite
```

Or enter the devshell once and run `lake build` without the `nix
develop` prefix:

```bash
nix develop
lake build
```

`lake build` succeeding **is** the formal-verification claim. Everything
in `nix run .#test` past `lake build` (cargo unit tests, trust gate,
flake repro check) is auxiliary scaffolding around that core proof
check.

First cold `lake build` takes roughly 10 minutes, dominated by
`native_decide` on Goldilocks primality. The devshell provides
`cargo`, the Lean toolchain (`elan`), python3, and jq — the same
toolchain `nix run .#test` bundles.

## Resource requirements

Cold first-time `nix run .#populate` (no Cachix hits, empty Nix
store) is bounded by the pilout build:

| Step                              | Peak RAM   | Wall time  |
|-----------------------------------|------------|------------|
| `.#zisk-pilout` (cold rebuild)    | ~17 GiB    | ~24 min    |
| `lake build` worst process (`Sail/sd.lean`) | ~8 GiB RSS / ~7 GiB PSS | (subset of total `lake build`) |
| Everything else                   | < 5 GiB    | minutes    |

The pilout build dominates because `pil2-compiler` (Node, V8 heap
capped at 12 GiB) composes every AIR's algebraic constraints in one
process; total RSS hits ~16 GiB plus OS overhead. **A 16 GiB machine
cannot run the cold pilout build** — 32 GiB is the practical minimum.
CI runs on `size-xl-x64` (32 GiB).

Once the pilout is in the local Nix store or Cachix, every subsequent
`nix run .#populate` is a few-second cached download (~5 MB) with
trivial RAM cost. The 17 GiB ceiling only matters when a `flake.lock`
input changes (i.e. an upstream version bump).

## Build cache architecture

Three independent cache layers, each with a different scope:

| Layer                         | Caches                              | Scope                                                                   | Eviction                                  |
| ----------------------------- | ----------------------------------- | ----------------------------------------------------------------------- | ----------------------------------------- |
| **Cachix** (`zisk-fv.cachix.org`) | Nix derivations: `sail-lean-tree`, `zisk-pilout`, `extracted-lean` | Content-addressed; visible to every machine + CI run                    | Manual; near-permanent in practice         |
| **GitHub Actions cache**      | `.lake/` (compiled oleans for ZiskFv) | Per `refs/<branch-or-PR>/` ref; PR runs read their own ref + `main`'s | 7 days idle; 10 GB total per repo         |
| **Lake's Azure cache**        | Mathlib oleans (via `lake exe cache get`) | Public; content-addressed by Mathlib commit                             | Effectively never                          |

Together these mean a steady-state PR run sees: cachix HIT on all
flake outputs (no pilout rebuild), GitHub-cache HIT on `.lake` (no
ZiskFv re-elaboration), Azure HIT on mathlib (no Mathlib compile).
Cold cost is paid only when a flake input changes (cachix miss) or
when no PR has touched main in over a week (GitHub-cache miss).

### Why not a Nix-cached `lake build`?

The community project [`lean4-nix`](https://github.com/lenianiva/lean4-nix)
provides `lake2nix.mkPackage`, which builds Lake projects as content-
addressed Nix derivations and pushes results to Cachix. This would
replace the GitHub-Actions `.lake` cache with a per-content-hash one
(no 7-day eviction, no per-ref scoping). We considered it and
deliberately stayed with stock Lake. Two reasons:

1. **It would lose Mathlib's Azure cache.** `lake exe cache get`
   pulls Mathlib's oleans (multi-GB) directly from Mathlib's CI cache;
   under `lean4-nix` we'd either have to package Mathlib as a Nix
   derivation (full rebuild on every Mathlib bump, hours) or skip the
   cache and accept ~10 min cold compile per Mathlib update. The lake
   side is the part of our pipeline that already has a working
   community cache; trading it for our own cache is net negative.
2. **Granularity.** A single `mkPackage` derivation hashes over the
   entire ZiskFv source tree, so any source edit invalidates the
   whole derivation. To approach Lake's per-file incremental rebuild,
   we'd have to split ZiskFv into many derivations and hand-encode
   the import graph — duplicating Lake's bookkeeping in Nix for
   marginal benefit over what we already have.

If we ever do hit real friction (e.g. CI gaps long enough that
`.lake` evicts every time), a much smaller move is to keep stock Lake
and just relocate the `.lake` cache off GitHub Actions to S3/GCS keyed
by `(lake-manifest, lakefile, toolchain, flake.lock)` hashes —
preserves Mathlib's Azure cache, no per-ref scoping, ~30 LoC of glue.
