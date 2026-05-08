# zisk-fv — project context for Claude

## Goal

Lean 4 formal verification of [ZisK](https://github.com/0xPolygonHermez/zisk)'s
zkVM circuit against the official [Sail RISC-V specification](https://github.com/riscv/sail-riscv),
per-opcode, restricted to RV64IM. Each opcode gets a theorem of the
canonical shape:

```
execute_instruction (.RTYPE rs2 rs1 rd rop.ADD) state
  = (bus_effect exec_row mem_row state).2
```

- **LHS** = Sail spec, built locally from primary source into
  `build/sail-lean/` (Sail compiler + sail-riscv compiled into Lean).
  The lakefile points at `build/sail-lean/` via a path-based require —
  no pre-built dep is pulled.
- **RHS** = ZisK's Goldilocks-valued circuit constraints composed
  with the operation-bus model.

**Out of scope:** Zicclsm, precompiles (Keccak / SHA256 / big-int /
DMA / etc.), ECALL/EBREAK, ZisK's custom internal ops.

**Status:** all 63 RV64IM opcodes proved (0 sorries; 84 trusted
axioms across 13 ledger classes; **all 63** canonical `equiv_<OP>`
theorems are OUTPUT-EQ-free, mechanically enforced uniformly by
`trust/scripts/check-no-output-eq.sh` against
`trust/forbidden-param-shapes.txt`. The 7 loads were closed by
deriving their cross-entry rd-value byte equations from circuit
witnesses — see `ZiskFv/Circuit/LoadDerivation.lean` plus the
bus-permutation closure axioms `memalign_load_high_bytes_zero`
and `signextend_load_c_packed`).

## Pipeline

```
flake.nix inputs (sail, sail-riscv, zisk, pil2-* sources, nixpkgs)
        │ pinned by content hash in flake.lock
        ▼
nix run .#populate            ← single command; builds and copies into the repo
        │
        ▼
build/sail-lean/, build/zisk.pilout, build/extraction/Extraction/*.lean
        │
        │ tools/pil-extract (run inside the flake)
        ▼
build/extraction/Extraction/<AIR>.lean  ← auto-generated, gitignored.
        │
        │ named-column wrappers
        ▼
ZiskFv/Airs/Valid_<AIR>       ← human-readable column accessors + simp lemmas
        │
        │ circuit-correctness theorems
        ▼
ZiskFv/Circuit/<family>       ← circuit semantics in BitVec / FGL
        │
        │ + LHS bridge to Sail spec
        ▼
ZiskFv/Equivalence/<OP>       ← equiv_<OP> : Sail.execute = bus_effect.2
```

## Build / verify / test

Bootstrap (run once after a fresh clone, ~30 min cold; ~seconds warm):

```bash
nix run .#populate    # → build/sail-lean/, build/zisk.pilout,
                       #   build/extraction/Extraction/*.lean
```

Day-to-day (inside `nix develop` shell, or prefix each command with
`nix develop --command`):

```bash
lake build       # the FV check — every per-opcode theorem typechecks
nix run .#test  # full suite: cargo + lake + trust gate + flake check
```

`lake build` succeeding **is** the formal-verification claim;
everything else is auxiliary scaffolding. The audit surface for build
inputs is `flake.lock` — a single committed file pinning every
transitive dep by content hash.

## Resource requirements (cold)

Costs that matter when `flake.lock` changes (cachix miss) or when
running on a fresh machine:

- `.#zisk-pilout` rebuild: **~17 GiB peak / ~24 min wall**.
  `pil2-compiler` (Node, V8 heap capped at 12 GiB in
  `nix/zisk-pilout.nix:142`) composes every AIR's algebraic
  constraints in one process; total RSS hits ~16 GiB plus OS overhead.
  This is the hard ceiling for the whole pipeline.
- `lake build` worst process: **~8 GiB RSS / ~7 GiB PSS** during
  `Sail/sd.lean` elaboration (post the PR #4 layered `dsimp`+`rw`
  refactor — was 42 GiB before). Other files stay below 5 GiB.

CI runner: needs ≥32 GiB (`size-xl-x64`). 16 GiB OOMs on cold pilout.
Warm runs (cachix hit) are seconds — once an input is in the cache,
downstream PRs reuse it. Upstream does not publish the raw `.pilout`
protobuf, so we self-host via cachix; checked
`storage.googleapis.com/zisk-setup/` and the GitHub releases — only
proving-key derivatives and circom verifiers are published, not the
input we need.

## Trust gate (READ THIS — agents must respect it)

The gate runs in two layers. Layer 1 is syntactic and runs in seconds
without `lake build`; layer 2 is semantic and consumes oleans (so
runs after `lake build`). Both must pass.

### Layer 1 — V1 syntactic (`trust/scripts/check-all.sh`, no build)

Six checks; if you break any, CI fails:

1. **Locality.** Lean trust-leak constructs (`axiom`, `opaque`,
   `constant`, `unsafe def`, `partial def`, `@[extern]`,
   `@[implemented_by]`) may appear ONLY in files listed in
   `trust/allowed-axiom-files.txt`. Adding a file to that list
   needs CODEOWNER review (see `.github/CODEOWNERS`).
2. **Baseline freshness.** `trust/baseline-axioms.txt` records every
   axiom's source-text hash. Adding / renaming / removing / subtly
   weakening any axiom → run `trust/scripts/regenerate.sh` and commit
   the updated baseline. The hash diff IS the audit surface for review.
3. **Forbidden OUTPUT-EQ parameters.** Canonical `equiv_<OP>`
   theorems may not include the retired OUTPUT-EQ named parameters
   (`h_rd_val`, `h_byte_sum`, `h_bus_execute_matches_sail`,
   `h_entry_hi_nat`, `h_pc_fgl_lo_nat`, `h_pci_lo_val`,
   `h_entry_lo_eq`, `h_high_bytes_signext`, `h_high_bytes_zeroext`,
   `h_e1_e2_bytes`). Pattern list: `trust/forbidden-param-shapes.txt`.
   Enforced uniformly across all 63 opcodes (no exemptions).
4. **Floors.** ≥82 axioms in baseline, ≥63 canonical `equiv_<OP>`
   theorems, plus a cross-witness check that the parser hasn't been
   sabotaged.
5. **Zero sorry** under `ZiskFv/{Fundamentals,Airs,Circuit,Equivalence,Tactics,Sail}`.
6. **Uniformity.** Every one of 63 RV64IM opcodes has a canonical
   `equiv_<OP>` theorem.

### Layer 2 — V2 semantic (`trust/scripts/check-all-semantic.sh`, requires `lake build`)

Two checks; runs via the `lake exe trust-gate` Lake exe at
`bin/TrustGate/`:

7. **Per-theorem axiom-closure baseline.**
   `trust/baseline-equiv-axiom-deps.txt` records the transitive
   non-kernel axiom dependencies of each canonical `equiv_<OP>`
   theorem (computed via `Lean.collectAxioms`). Any silent change
   to a theorem's trust footprint — additions OR removals — fails
   the gate. Run `trust/scripts/regenerate.sh` (with oleans
   present) and review the diff before committing.
8. **Forbidden binder types.** Walks each canonical theorem's
   parameter binders via `forallTelescope` + `whnfR` (which unfolds
   `abbrev` / `@[reducible] def` chains) and fails on any reference
   to Names listed in `trust/forbidden-types.txt`. Closes the
   `abbrev`-aliasing dodge that V1's textual regex cannot see.

**Run `trust/scripts/check-all.sh` locally before pushing** (V1,
seconds, no build). Run `trust/scripts/check-all-semantic.sh` after
`lake build` — `nix run .#test` runs both in sequence.

**To extend the TCB** (high bar — most "fixes" should not need a new
axiom):

1. Add the axiom to one of the files in `trust/allowed-axiom-files.txt`.
2. Run `trust/scripts/regenerate.sh` to refresh the baseline.
3. Add a `docs/fv/trusted-base.md` entry describing the trust class +
   closure path.
4. Commit axiom + baseline + ledger entry in the same PR.
5. CODEOWNER review of the `trust/baseline-axioms.txt` diff is the
   audit step.

Don't try to bypass the gate by editing `trust/forbidden-param-shapes.txt`
or `trust/allowed-axiom-files.txt` directly — both are CODEOWNER-protected.

## Traps to avoid (don't re-discover these)

1. **Never shadow `[Field FGL]` as a proof-local variable** — it
   creates a dummy instance that defeats `ring`. The Field instance
   is declared once globally in `Fundamentals/Goldilocks.lean`; a
   guard comment lives there.
2. **`ring` treats `4294967296 * 4294967296` and
   `18446744073709551616` as distinct polynomial atoms** (same
   number, different literal form). When `linear_combination` needs
   to close against carry-chain coefficients, write the factored form.
3. **`(1 - 0) * x` over `Fin p` does not reduce via `simp` /
   `ring_nf` / `decide`.** Phase 1 sidesteps by specializing
   `opBus_row_Main` to `m32 = 0`.
4. **`LeanZKCircuit.Interactions` is NOT needed for compositional
   proofs.** The `Airs/OperationBus.lean::matches_entry` predicate
   replaces them — use that.

## Documentation map

| Where | What |
|---|---|
| `docs/fv/trusted-base.md` | Human-readable trust ledger. Pairs with `trust/baseline-axioms.txt`. Edit when you legitimately add/remove an axiom. |
| `docs/fv/extractor-notes.md` | Durable contract for `tools/pil-extract`. Read first when extending the extractor. |
| `docs/fv/air-inventory.md` | 22-AIR table: which are extracted, which have named wrappers, which are absorbed into trust. |
| `trust/README.md` | Full reference for the gate scripts + baseline files. |
| `nix/README.md` | Flake-level docs: what each derivation produces, why we use Nix. |
| `docs/site/index.html` | Public-facing single-page explainer (run `docs/site/serve.sh`, port 4044). |
| **agent memory** | `/home/cody/.claude/projects/-home-cody-zisk-fv/memory/` — facts that persist across conversations; update when current state changes. |

## Past work removed from the tree

Recover via `git show`:

- **`ai_plans/`** — commit `ac2d5e4`. The pre-completion planning
  tree (overall plan + per-phase plans, all CLOSED with
  retrospectives). Recover with `git show ac2d5e4^:ai_plans/<file>`.
- **`docs/fv/`** purge — commit `661fe36`. Commit message lists each
  removed file and what it covered, so it doubles as the recovery index.
- **`docker/`** — commit `cd4e4d9` ("chore: delete docker pipeline
  (replaced by flake)"). The Dockerfiles, build scripts, and
  `docker/versions.txt` (per-artifact fingerprint pins) are all
  superseded by the Nix flake; `flake.lock` is the new audit surface
  for build inputs. Recover the old pipeline with
  `git show cd4e4d9^:docker/<file>`.

## Conventions

- **Always build and test before claiming completion.** Minimum is
  `lake build`; ideally `nix run .#test`.
- **Do not use destructive git commands** (`reset --hard`, force push,
  `branch -D`) without explicit permission.
- The `zisk/` submodule is a **citation surface** for `transpile_*`
  axiom rationales, NOT the source of `build/zisk.pilout`. The pilout
  is built by the flake from `flake.nix::inputs.zisk-src` (a separate
  pinned commit of upstream zisk).
- All extraction lives under `build/extraction/Extraction/`
  (gitignored, regenerated by `nix run .#populate`). `tools/pil-extract`
  emits per-AIR constraint files, the operation-bus `Buses.lean`,
  the memory-bus `MemoryBuses.lean`, and `ArithTable.lean` (the 74-row
  state-machine lookup table parsed from
  `zisk/state-machines/arith/src/arith_table_data.rs`). Per-slot ExtF
  detection in the bus-emission renderer means partially-tainted
  emissions (e.g. Main's op-bus tuple, whose 9th slot references an
  AirValue) emit their F-clean slots verbatim while stubbing only the
  ExtF-tainted ones.
- `native_decide` on Goldilocks primality takes ~6 min cold. Mathlib's
  Azure cache via `lake exe cache get` handles the rest.
