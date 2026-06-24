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

**Status:** `zisk_riscv_compliant_program_bus` is proved
(`ZiskFv/Compliance.lean`); its trust closure
is the **0-name global compliance closure** enumerated in
`trust/generated/baseline-zisk-riscv-compliant.txt`; the source trust ledger
records **0 axioms** in `trust/generated/baseline-axioms.txt`, documented
per-class in `trust/trusted-base.md`. All 63 RV64IM opcodes are covered as
`ZiskFv.Compliance.equiv_<OP>` wrappers under
`ZiskFv/Compliance/Wrappers/<Op>.lean`, dispatched by the global theorem through a 63-arm
`OpEnvelope` sum type.
`ZiskFv.Completeness.root_completeness` is also checked in as an
acceptance/coverage theorem for Sail-executable RV64IM raw words outside the
recorded FENCE decode gap. It is interface-mediated through the Aeneas
extraction gate and does not revive Clean prover completeness non-claims.
The Clean completeness side is no longer a set of vacuous non-claims: all
17 fields now have honest-row constructibility proofs with gate-checked
witnesses. The documented scope is row-local constructibility only, with
Arith limited to unsigned slices and Binary/BinaryExtension using the
table-index route. These proofs do not claim cross-row trace completeness or
fill the signed-Arith/table-op follow-up scopes.

Per-opcode the proof is a 3-layer tower: `ZiskFv/EquivCore/<Op>.lean`
(the real Sail↔circuit proof, plus shared `EquivCore/{Bridge,Promises,
WriteValueProofs}/`) → `ZiskFv/Compliance/Wrappers/<Op>.lean` (promise
discharge) → `ZiskFv/Equivalence/<Op>.lean` (the canonical
`equiv_<OP>`, channel-balance form). The global theorem aggregates the
ten per-family dispatchers in `ZiskFv/Compliance/Dispatch/`. The principal "promise hypothesis"
soundness gap surveyed in
[`trust/README.md`](trust/README.md) is closed at the
global theorem: the semantic trust gates
(`check-closure-vs-baseline` + the per-theorem axiom-closure baseline)
mechanically prevent regression. The 63 canonical `equiv_<OP>`
theorems remain OUTPUT-EQ-free, enforced uniformly by
`trust/scripts/check-no-output-eq.sh` against
`trust/forbidden-param-shapes.txt`. The 7 loads were closed by
deriving their cross-entry rd-value byte equations from circuit
witnesses — see `ZiskFv/ZiskCircuit/LoadDerivation.lean` for the
copyb / MemAlign families and `ZiskFv/ZiskCircuit/SextLoadBridge.lean`
for the LB/LH/LW signed-load chain
(`binary_extension_sext_{b,h,w}_chunks_eq_signextend_nat` plus
Clean/static lookup witnesses). The
LBU/LHU/LWU zero-pad is itself a derived theorem
(`memalign_subdoubleword_load_high_bytes_zero` in
`Airs/MemoryBus/MemAlignBridge.lean`) consuming an explicit
`SubdoublewordLoadProviderWitness` and ROM-derived row facts. No
MemAlign permutation or MemAlignRom axiom remains in canonical/global
closure.

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
ZiskFv/ZiskCircuit/<family>   ← circuit semantics in BitVec / FGL
        │
        │ + LHS bridge to Sail spec
        ▼
ZiskFv/EquivCore/<OP>         ← core proof : Sail.execute = bus_effect.2
        │
        │ promise discharge
        ▼
ZiskFv/Compliance/Wrappers/<OP>  ← Compliance.equiv_<OP>
        │
        │ channel-balance bridge
        ▼
ZiskFv/Equivalence/<OP>       ← canonical equiv_<OP> : Sail.execute = state_effect_via_channels
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
  `SailSpec/sd.lean` elaboration (post the PR #4 layered `dsimp`+`rw`
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

`check-all.sh` runs 15 checks; if you break any, CI fails. The
soundness-load-bearing core is described below (the script also runs
ArithTable-axiom, Clean-integration, CODEOWNERS, retired-row-shape,
Aeneas-artifact/manifest/boundary, generated-axiom-allowlist, and
shrinkage-floor checks):

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
4. **Floors.** The baseline's tracked trust-declaration count must match the
   tree-wide cross-check, the shrinkage floor must not be exceeded, and ≥63 canonical `equiv_<OP>`
   theorems, plus a cross-witness check that the parser hasn't been
   sabotaged.
5. **Zero sorry** under `ZiskFv/{Fundamentals,Airs,ZiskCircuit,Equivalence,Tactics,Sail}`.
6. **Uniformity.** Every one of 63 RV64IM opcodes has a canonical
   `equiv_<OP>` theorem.

> **Retired (2026-06):** the V1 hypothesis-count and caller-burden
> ledger checks — the per-theorem binder-count / caller-burden
> *anti-laundering metrics* — have been removed now that the discharge
> campaign concluded at **0 project axioms**. They only churned on
> benign refactors; the soundness-load-bearing checks above plus the
> Layer-2 axiom-closure baselines fully cover regression.

### Layer 2 — V2 semantic (`trust/scripts/check-all-semantic.sh`, requires `lake build`)

`check-all-semantic.sh` runs 13 checks via the `lake exe trust-gate`
Lake exe at `bin/TrustGate/` plus consistency/instantiation witnesses.
The two core baseline gates are:

1. **Per-theorem axiom-closure baseline.**
   `trust/baseline-equiv-axiom-deps.txt` records the transitive
   non-kernel axiom dependencies of each canonical `equiv_<OP>`
   theorem (computed via `Lean.collectAxioms`). Any silent change
   to a theorem's trust footprint — additions OR removals — fails
   the gate. Run `trust/scripts/regenerate.sh` (with oleans
   present) and review the diff before committing.
2. **Forbidden binder types.** Walks each canonical theorem's
   parameter binders via `forallTelescope` + `whnfR` (which unfolds
   `abbrev` / `@[reducible] def` chains) and fails on any reference
   to Names listed in `trust/forbidden-types.txt`. Closes the
   `abbrev`-aliasing dodge that V1's textual regex cannot see.

> **Retired (2026-06):** the V2 DEEP construction-theorem-binder gate
> (`baseline-construction-theorem-binders.txt`) was removed alongside
> the V1 anti-laundering metrics for the same reason.

**Run `trust/scripts/check-all.sh` locally before pushing** (V1,
seconds, no build). Run `trust/scripts/check-all-semantic.sh` after
`lake build` — `nix run .#test` runs both in sequence.

**To extend the TCB** (high bar — most "fixes" should not need a new
axiom):

1. Add the axiom to one of the files in `trust/allowed-axiom-files.txt`.
2. Run `trust/scripts/regenerate.sh` to refresh the baseline.
3. Add a `trust/trusted-base.md` entry describing the trust class +
   closure path.
4. Commit axiom + baseline + ledger entry in the same PR.
5. CODEOWNER review of the `trust/baseline-axioms.txt` diff is the
   audit step.

Don't try to bypass the gate by editing `trust/forbidden-param-shapes.txt`
or `trust/allowed-axiom-files.txt` directly — both are CODEOWNER-protected.

### Anti-laundering principle (READ THIS — for any agent or human doing promise discharge)

> **Status (2026-06): guidance, not gate-enforced.** The mechanical
> *anti-laundering metric* checks — the V1 hypothesis-count and
> caller-burden ledger baselines and the V2 DEEP construction-binder
> baseline — have been **retired** now that the discharge campaign
> concluded at **0 project axioms**. The operational "every PR must
> reduce/hold the hypothesis-count and caller-burden columns" metric
> below is therefore no longer enforced by CI; the principle remains as
> authoring guidance. Soundness regression is still gated mechanically
> by the kept checks (zero-sorry, locality, axiom-closure baselines,
> headline closure/binder baselines, Aeneas-trust, and floors).

**Vocabulary.** This section uses **promise hypothesis**, **promise
discharge**, **discharge bridge**, **trust ledger**, **caller-burden
ledger**, **anti-laundering metric**, and **constructibility** as
defined in [`trust/README.md`](trust/README.md#anti-laundering-terms).
Any plan / PR / commit / agent prompt touching this work must use
those terms with those meanings; ad-hoc synonyms fragment the audit
trail.

**The work.** *Promise discharge* — the activity of replacing
caller-supplied *promise hypotheses* on canonical `equiv_<OP>`
theorems with derivations from the *trust ledger* — exists to
**reduce** the project's residual trust surface. There are several
ways a refactor can **look like** progress while actually just
rearranging the trust:

1. **Axiom inflation.** A promise hypothesis becomes an axiom of
   the same shape. The trust ledger grows; the verification claim
   does not. **Refusal:** every new axiom must fit one of the
   trust classes already documented in `trust/trusted-base.md`,
   with a citation to a specific PIL line, Rust function, or
   protocol-soundness theorem. New trust *kinds* are a separate
   prior PR with explicit justification.
2. **Hypothesis splitting / renaming.** One promise becomes N
   smaller promises. The trust surface stays the same or grows.
   **Refusal:** this was formerly detected mechanically by the
   hypothesis-count and caller-burden gates (now retired). It is now
   an authoring/review discipline — a PR whose net per-theorem binder
   burden holds steady or grows did not discharge anything and should
   be rescoped.
3. **Universalizing too eagerly.** Replacing `(h_x : P r)` with
   `(h_univ : ∀ r, P r)` *moves* the trust to a stronger
   caller-supplied universal — usually still undischarged.
   **Refusal:** the caller-burden ledger records the type shape;
   the diff makes the change visible. Reviewers must confirm the
   universal IS dischargeable from the trust ledger by some downstream
   consumer (a derivation lemma proved against the existing axioms).
4. **Overstrong AIR validators (constructibility).** A
   `Valid_<AIR>` record with declared constraints stronger than
   what ZisK's circuit actually enforces makes the equivalence
   theorems vacuous — they universally quantify over
   `Valid_<AIR>` instances that nobody can produce. **Refusal:**
   any change to `Valid_<AIR>` constraints requires an explicit
   citation to the PIL constraint it mirrors and a constructibility
   sketch (how a real ZisK trace witnesses the constraint).
5. **Definitional aliasing.** `def AddSpec := <promise>` hides a
   hypothesis behind a name. V2's `whnfR` unfolds `abbrev` and
   `@[reducible] def`; non-reducible `def`s slip past. **Refusal:**
   any new top-level `def` introduced inside a refactor PR must be
   reviewed for whether it could hide a hypothesis. If unsure, mark
   it `@[reducible]` so V2 unfolds it.

The former operational metric — *every plan PR must reduce or hold
both the `total` and `hypothesis` per-theorem binder columns, and every
PR's caller-burden diff must visibly REMOVE more lines than it adds* —
**is retired** (its backing baselines were removed). It survives only
as the intuition behind the guidance above: a PR that is "net zero" on
trust surface did not discharge anything; it just moved the trust
around. Such a PR should be either rescoped or abandoned.

**Exception class — structural unpacking (historical).** While the
metric was enforced, one narrow exception applied:
*structural-unpacking refactors* that replace a single compressed
*promise hypothesis* with the explicit validator + universal-row-
constraint + structural-pin parameters needed to derive it. The
per-opcode metric apparently grew but the global-theorem trust
footprint provably did not — because the added validator and
universal-row-constraint parameters collapse into shared parameters
of `Compliance.lean`, which already takes one set of those per
provider AIR. (The exception list `structural-unpacking-exceptions.txt`
was removed with the metric.) This nuance is retained here only as
authoring guidance for reasoning about whether a refactor genuinely
reduces global trust.

When delegating to a sub-agent for any plan step, **include this
anti-laundering principle verbatim in the prompt AND require the
agent to read [`trust/README.md`](trust/README.md#anti-laundering-terms)
before starting**. The agent must explicitly check, before
declaring a *promise discharge* step complete, that:
* the trust surface shrank — the refactor shows a net REDUCTION in
  caller-supplied promise hypotheses (the hypothesis-count and
  caller-burden baselines that once measured this are retired, so this
  is now a review-and-author discipline), AND
* any new *trust-ledger* axiom fits an existing class with
  citation, AND
* any new `Valid_<AIR>` constraint or top-level `def` was reviewed
  for hidden-promise risk (see "*constructibility*" in the
  glossary), AND
* the PR title, body, and commit messages use the canonical terms
  from the glossary (no ad-hoc synonyms).

Skip any of these and the refactor failed at its stated goal even
if the build is green and `lake build` typechecks. The mechanical
*anti-laundering metric* gates (hypothesis-count + caller-burden +
construction-binder baselines) have been retired now that the
discharge campaign concluded at 0 axioms; the agent's self-check above
and reviewer discipline now enforce this principle, while the kept
axiom-closure baselines mechanically prevent any soundness regression.

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
| `trust/trusted-base.md` | Human-readable trust ledger. Pairs with `trust/baseline-axioms.txt`. Edit when you legitimately add/remove an axiom. |
| `docs/extraction/extractor-notes.md` | Durable contract for `tools/pil-extract`. Read first when extending the extractor. |
| `docs/extraction/air-inventory.md` | 22-AIR inventory and extraction orientation. Trust status lives in `trust/`. |
| `trust/README.md` | Full reference for the gate scripts + baseline files. |
| `nix/README.md` | Flake-level docs: what each derivation produces, why we use Nix. |
| **agent memory** | `/home/cody/.claude/projects/-home-cody-zisk-fv/memory/` — facts that persist across conversations; update when current state changes. |

## Past work removed from the tree

Recover via `git show`:

- **`ai_plans/`** — commit `ac2d5e4`. The pre-completion planning
  tree (overall plan + per-phase plans, all CLOSED with
  retrospectives). Recover with `git show ac2d5e4^:ai_plans/<file>`.
- **former `docs/fv/` purge** — commit `661fe36`. Commit message lists each
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
- The `zisk/` submodule carries the Aeneas extraction branch. It is based on
  the same upstream ZisK `v0.17.0` revision as `flake.nix::inputs.zisk-src`,
  with explicit extraction-only feature patches on top. Generated Aeneas
  Lean/LLBC stays under `build/aeneas-production-extraction/` and is not
  checked in.
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
