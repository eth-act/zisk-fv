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

**Status:** all 63 RV64IM opcodes proved (0 sorries; 82 trusted
axioms across 13 ledger classes; 45 of the 63 also have `_tier1`
companions with the OUTPUT-EQ retirement — see
`docs/fv/trusted-base.md`).

## Pipeline

```
flake.nix inputs (sail, sail-riscv, zisk, pil2-* sources, nixpkgs)
        │ pinned by content hash in flake.lock
        ▼
nix run .#populate            ← single command; builds and copies into the repo
        │
        ▼
build/sail-lean/, build/zisk.pilout, ZiskFv/Extraction/*.lean
        │
        │ tools/pil-extract (run inside the flake)
        ▼
ZiskFv/Extraction/<AIR>.lean  ← auto-generated; gitignored except 3 hand-written files
        │
        │ named-column wrappers
        ▼
ZiskFv/Airs/Valid_<AIR>       ← human-readable column accessors + simp lemmas
        │
        │ circuit-correctness theorems
        ▼
ZiskFv/Spec/<family>          ← circuit semantics in BitVec / FGL
        │
        │ + LHS bridge to Sail spec
        ▼
ZiskFv/Equivalence/<OP>       ← equiv_<OP>_metaplan : Sail.execute = bus_effect.2
```

## Build / verify / test

Bootstrap (run once after a fresh clone, ~30 min cold; ~seconds warm):

```bash
nix run .#populate    # → build/sail-lean/, build/zisk.pilout,
                       #   ZiskFv/Extraction/*.lean
```

Day-to-day (inside `nix develop` shell, or prefix each command with
`nix develop --command`):

```bash
lake build       # the FV check — every per-opcode theorem typechecks
bin/test.sh      # full suite: cargo + lake + trust gate + flake check
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
  `RV64D/sd.lean` elaboration (post the PR #4 layered `dsimp`+`rw`
  refactor — was 42 GiB before). Other files stay below 5 GiB.

CI runner: needs ≥32 GiB (`size-xl-x64`). 16 GiB OOMs on cold pilout.
Warm runs (cachix hit) are seconds — once an input is in the cache,
downstream PRs reuse it. Upstream does not publish the raw `.pilout`
protobuf, so we self-host via cachix; checked
`storage.googleapis.com/zisk-setup/` and the GitHub releases — only
proving-key derivatives and circom verifiers are published, not the
input we need.

## Trust gate (READ THIS — agents must respect it)

CI runs `trust/scripts/check-all.sh` on every PR. It enforces six
things; if you break any of them, the build fails:

1. **Locality.** Lean trust-leak constructs (`axiom`, `opaque`,
   `constant`, `unsafe def`, `partial def`, `@[extern]`,
   `@[implemented_by]`) may appear ONLY in files listed in
   `trust/allowed-axiom-files.txt`. Adding a file to that list
   needs CODEOWNER review (see `.github/CODEOWNERS`).
2. **Baseline freshness.** `trust/baseline-axioms.txt` records every
   axiom's source-text hash. Adding / renaming / removing / subtly
   weakening any axiom → run `trust/scripts/regenerate.sh` and commit
   the updated baseline. The hash diff IS the audit surface for review.
3. **Forbidden tier1 parameters.** `equiv_<OP>_metaplan_tier1`
   theorems may not include the named parameters retired by the
   finishing series (`h_rd_val`, `h_byte_sum`,
   `h_bus_execute_matches_sail`, `h_entry_hi_nat`, `h_pc_fgl_lo_nat`,
   `h_pci_lo_val`, `h_entry_lo_eq`). Pattern list:
   `trust/forbidden-param-shapes.txt`.
4. **Floors.** ≥80 axioms in baseline, ≥40 `_tier1` theorems, plus a
   cross-witness check that the parser hasn't been sabotaged.
5. **Zero sorry** under `ZiskFv/{Fundamentals,Airs,Spec,Equivalence,Tactics,RV64D}`.
6. **Uniformity.** Every one of 63 RV64IM opcodes has a canonical
   `equiv_<OP>_metaplan` theorem.

**Run `trust/scripts/check-all.sh` locally before pushing** (it
takes seconds — none of these checks need `lake build`).

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

- **`ai_plans/`** — commit `ac2d5e4`. Contained the metaplan, per-phase
  plans (Phase 0 / 1 / finishing1-5) with CLOSED retrospectives.
  Recover with `git show ac2d5e4^:ai_plans/<file>`.
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
  `lake build`; ideally `bin/test.sh`.
- **Do not use destructive git commands** (`reset --hard`, force push,
  `branch -D`) without explicit permission.
- The `zisk/` submodule is a **citation surface** for `transpile_*`
  axiom rationales, NOT the source of `build/zisk.pilout`. The pilout
  is built by the flake from `flake.nix::inputs.zisk-src` (a separate
  pinned commit of upstream zisk).
- `ZiskFv/Extraction/` is mixed: most files are gitignored
  auto-generated build outputs (`nix run .#populate`
  regenerates them); 3 stay tracked because they're hand-written:
  - `ArithTable.lean` — hand-transcribed from
    `zisk/state-machines/arith/src/arith_table_data.rs`.
  - `MemoryBuses.lean` — hand-curated subset of memory-bus emissions
    with documentation.
  - `OperationBuses.lean` — hand-written operation-bus emission for
    Main. The auto-extracted `Buses.lean::bus_emission_Main_0` became
    a multiplicity-0 stub starting v0.16.0 (the new `proves_operation`
    macro emits ExtF-typed challenge cells the V1 extractor can't
    render). The hand-written replacement lives here.
- `native_decide` on Goldilocks primality takes ~6 min cold. Mathlib's
  Azure cache via `lake exe cache get` handles the rest.
