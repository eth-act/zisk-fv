# zisk-fv — project context for Claude

## Goal

Formally verify, in Lean 4, that [ZisK](https://github.com/0xPolygonHermez/zisk)'s
zkVM circuit implementation matches the official Sail RISC-V specification,
per-opcode, restricted to RV64IM. The goal is per-opcode theorems of the shape

```
execute_instruction (.RTYPE rs2 rs1 rd rop.ADD) state = (bus_effect exec_row mem_row state).2
```

where the LHS is the Sail spec (via `NethermindEth/sail-riscv-lean`'s
`LeanRV64D` module) and the RHS is ZisK's Goldilocks-valued circuit
constraints composed with the operation-bus model.

Zicclsm, precompiles (Keccak, SHA256, …), and ZisK's custom internal ops
are **out of scope** for the initial effort.

## Template: openvm-fv

We are adapting the **openvm-fv** Lean project (Nethermind / OpenLabs,
45 RV32IM opcodes verified). It is the closest prior art — same Lean
toolchain, same `LeanZKCircuit` dependency, same pipeline shape. We
studied it first and we are explicitly following its pattern.

- Local symlink: `/home/cody/openvm-fv` (read-only reference; don't
  modify it). A gitignored convenience symlink also exists at
  `/home/cody/zisk-fv/openvm-fv → /home/cody/openvm-fv` so paths
  relative to this repo resolve.
- Pipeline stages we mirror:
  `Extraction/` (auto-generated raw constraints) →
  `Airs/` (named-column `Valid_<AIR>` structures) →
  `Constraints/` (simp-lemma bridges, inlined into `Airs/` for Phase 1) →
  `RV<N>D/<opcode>.lean` (pure spec + Sail equivalence) →
  `Spec/<family>.lean` (circuit-correctness theorem) →
  `Equivalence/<family>.lean` (final per-opcode theorem).

## Substantive differences from openvm-fv

ZisK is architected differently from OpenVM, so the template adapts —
it doesn't transfer directly:

- **Field:** Goldilocks (`2^64 − 2^32 + 1`), not BabyBear.
- **Constraint language:** PIL2 + compiled `.pilout` protobuf, not a
  Plonky3 `SymbolicConstraintsDag`. The `openvm-fv/extractor/` binary is
  **not reusable** — we built `tools/zisk-pil-extract/` to walk pilout.
- **Execution model:** one monolithic Main AIR over "Zisk instructions"
  (a microinstruction IR) that multiplexes opcodes via flags and
  delegates heavy ops to secondary state machines (arith, binary,
  precompiles) via the operation bus (`OPERATION_BUS_ID=5000`). Contrast
  with OpenVM's one-AIR-per-opcode-family layout. This means ZisK FV
  proofs are always compositional (Main + secondary + bus), never
  self-contained in a single AIR.
- **RISC-V transpilation:** ZisK's `core/src/riscv2zisk_context.rs` maps
  one RV instruction to 1+ Zisk microinstructions. We axiomatize that
  contract (see `ZiskFv.Fundamentals.Transpiler`) — it's part of the
  **trusted** surface.

## Trusted surface

**Single source of truth: `trust/baseline-axioms.txt`** — auto-generated
from the `*.lean` files listed in `trust/allowed-axiom-files.txt`. The
list below is human-readable narrative; the baseline file is the
machine-readable enforcement target. CI (`.github/workflows/trust-gate.yml`)
runs `trust/scripts/check-all.sh` on every PR; if the live tree's trust
surface diverges from the baseline, the build fails and the diff
becomes the audit surface for review.

**To add a trust-surface item** (high bar — see below for what counts):

1. Add the `axiom` declaration to one of the files in
   `trust/allowed-axiom-files.txt` (or update that allowlist with
   explicit reviewer ack — both files are CODEOWNER-protected).
2. Run `trust/scripts/regenerate.sh` to refresh `trust/baseline-axioms.txt`.
3. Add a corresponding entry to `docs/fv/trusted-base.md` describing
   the trust class + closure path.
4. Commit the axiom + the new baseline + the docs entry in the same PR.
5. CODEOWNER review of the `trust/baseline-axioms.txt` diff is the
   audit step. The hash that appears in that file is over the
   axiom's source-text statement, so a subtle weakening of an
   existing axiom shows as a hash change — reviewers see exactly
   what changed semantically.

**The Lean trust-leak shapes the gate watches** (any of these counts as
trust): `axiom`, `opaque`, `constant`, `unsafe def`, `partial def`,
`@[extern]`, `@[implemented_by]`. Don't reach for any of them outside
the allowlisted files. If a proof feels like it needs one, the right
move is almost always to find an existing axiom that covers the gap or
to escalate explicitly rather than adding a new one.

Items below are accepted as axioms; downstream theorems compose on top
of them. Improving any of them to a proven theorem is a strict trust
reduction and is welcome but out of scope for current phases.

- `ZiskFv.Fundamentals.Transpiler` — the RV→Zisk microinstruction
  contract from `core/src/riscv2zisk_context.rs`.
- `ZiskFv.Airs.OperationBus.matches_entry` — operation-bus protocol
  soundness (`bus_id=5000`): a Main row's emission equals the matched
  secondary AIR's row.
- `ZiskFv.Airs.BinaryTable` (added in `finishing2.md` S0) — the binary
  lookup table at `bus_id=125` carries the per-byte switch semantics
  defined by `vendor/zisk/state-machines/binary/pil/binary_table.pil`
  (AND/OR/XOR bitwise ops; LT/LTU/EQ/GT/LE/LEU/LT_ABS_*/MIN(U)/MAX(U)
  comparison ops; ADD/SUB carry semantics; SEXT_00/FF byte sign-extends).
  Mirrors openvm-fv's `Fundamentals/Interaction.lean::BitwiseBusEntry`
  (whose XOR semantics is similarly trusted at the bus-entry definition).
- `ZiskFv.Airs.BinaryExtensionTable` (added in `finishing2.md` S0) — the
  shift lookup table at `bus_id=124` carries per-byte shift semantics
  from `binary_extension_table.pil` (SLL/SRL/SRA byte-level views).
- `ZiskFv.Airs.MemoryBus.LaneMatch.memory_bus_register_write_perm_sound`
  (added in `finishing3.md` S4) — memory-bus permutation soundness for
  register writes (`bus_id=10`): bundles the multi-row Mem-AIR chain
  (writing Main row's emission ↔ writing Mem row ↔ persistence rows ↔
  consuming Mem row ↔ next-read Main row's `prev_value`) under the
  store-reg gating, in the same shape as `OperationBus.matches_entry`.
  Closes the K2 writes-side lane match. See
  `docs/fv/trusted-base.md`'s entry MB-W for the full provenance and
  closure path.
- `ZiskFv.Airs.MemoryBus.MemBridge.lookup_consumer_matches_provider_load`
  / `..._store` (added in `finishing3.md` S3) — memory-bus permutation
  soundness for the *memory-side* (`as=2`) load / store paths used by
  LD / SD / LW / SW / LH / SH / LB / SB. Pair Main's load/store
  emission with a Mem AIR row carrying the same
  `(addr, step, value_0, value_1)` projection. Same trust class as
  MB-W (logUp / permutation argument over `bus_id=10`); separate
  axioms because they operate on the memory-side address space rather
  than the register-side. Entries MB-L / MB-S in
  `docs/fv/trusted-base.md`.
- `ZiskFv.Spec.MemModel.row_models_sail_state_load` / `..._store`
  (added in `finishing3.md` S3) — Sail-side state-bridge: a Mem AIR
  row matching a memory bus entry agrees with `state.mem` byte-by-byte
  (load: pre-state matches; store: post-state matches). Replaces the
  per-opcode M-family `*_pure_equiv_axiom` parameters at the metaplan
  layer. Trust class: implementation-models-spec faithfulness between
  ZisK's Mem state-machine and Sail's memory model. Entries MS-L /
  MS-S in `docs/fv/trusted-base.md`.

## Working conventions

### Past work removed from the tree

Two earlier folders (`ai_plans/` and most of `docs/fv/`) accumulated
phase-by-phase planning notes and library-reference reflections through
finishing5. They were removed once the trust gate became the system of
record for current state. To recover any of that history:

- **`ai_plans/` removal:** commit `ac2d5e4` (`remote ai_plans to reduce
  grep noise`). Contained `zisk-fv-metaplan.md`, per-phase plans
  (Phase 0 / 1 / finishing1-5) with their CLOSED retrospectives, and
  feasibility / handoff notes. Each phase plan is reachable via
  `git show ac2d5e4^:ai_plans/<file>`.
- **`docs/fv/` purge:** commit `661fe36` (`archive docs/fv: prune
  historical phase notes; keep live references only`). The commit
  message itself enumerates each removed file and what it contained,
  so it doubles as the recovery index.

If a future task needs context from those removed docs, `git show
<commit>:<path>` produces them on demand. They are not loaded into
your normal grep / read scope — that's intentional.

### Documentation split (live)

- **`docs/fv/`** — three library-reference notes that ARE load-bearing:
  - `trusted-base.md` — the human-readable trust ledger; pairs with
    `trust/baseline-axioms.txt`. Edit this when you legitimately add
    or remove an axiom (see "Trusted surface" above).
  - `extractor-notes.md` — durable contract / pilout structure /
    oracle rules for `tools/zisk-pil-extract/`. Read first when
    extending the extractor.
  - `air-inventory.md` — 22-AIR table (which are extracted into
    Lean, which have named wrappers, which are absorbed into trust).
- **`trust/`** — baselines and enforcement scripts; see
  `trust/README.md`.
- **`repro/`** — Docker-based reproducibility for the two
  trusted artifacts (`build/zisk.pilout` and the `LeanRV` Lake dep).
  See `repro/README.md`. Pinned upstream versions live in
  `repro/versions.txt`.
- **memory** — agent-private notes at
  `/home/cody/.claude/projects/-home-cody-zisk-fv/memory/`. Project
  facts that persist across conversations; update when current state
  changes.

### Traps captured during early phases (don't re-discover these)

The phase-1 detailed write-up lives at `ai_plans/zisk-fv-phase-1.md`
in the pre-`ac2d5e4` tree (`git show ac2d5e4^:ai_plans/zisk-fv-phase-1.md`).
Short list of the highest-impact traps:

1. **Never shadow `[Field FGL]` as a proof-local variable** — it creates
   a dummy instance that defeats `ring`. Declare Field once globally in
   `Fundamentals/Goldilocks.lean` and never re-quantify. A guard comment
   lives in Goldilocks.lean.
2. **`ring` treats `4294967296 * 4294967296` and `18446744073709551616`
   as different polynomial atoms** (same number, different literal
   form). When a theorem statement needs `linear_combination` to close
   against carry-chain coefficients, write the factored form.
3. **`(1 - 0) * x` over `Fin p` doesn't reduce via `simp` / `ring_nf` /
   `decide`-based rewriting.** Phase 1 sidesteps by specializing
   `opBus_row_Main` to `m32 = 0`; generalizing this is Phase 1.5 work.
4. **The permutation-argument constraints (mixed `F`/`ExtF`) skip-stub
   at the extraction layer.** `LeanZKCircuit.Interactions` is **not**
   needed for compositional proofs — the `Airs/OperationBus.lean`
   `matches_entry` predicate replaces them cleanly.

### Build and verification

- The project gate is `just verify-phase<N>` (or `just verify-phase1`
  for the current state of the art). It regenerates extractions, diffs
  them against hand oracles, emits fixtures, runs cargo tests, and
  builds the full Lean package.
- Do NOT use destructive git commands (reset --hard, force push, branch
  -D) without explicit permission. Build and test before claiming
  completion.
- `native_decide` on Goldilocks primality takes ~386s cold. Mathlib's
  Azure cache via `lake exe cache get` handles the rest.

### Trust-gate workflow (READ THIS — agents must respect it)

Before merging, CI runs `trust/scripts/check-all.sh`. It enforces four
things; an agent who breaks any of them will fail the gate:

1. **Locality.** Lean trust-leak constructs (`axiom`, `opaque`,
   `constant`, `unsafe def`, `partial def`, `@[extern]`,
   `@[implemented_by]`) may appear ONLY in the files listed in
   `trust/allowed-axiom-files.txt`. Adding a new such file requires
   editing the allowlist AND a CODEOWNER reviewer ack — these files
   are protected by `.github/CODEOWNERS`.
2. **Baseline freshness.** `trust/baseline-axioms.txt` records every
   axiom's source-text hash. If you add, rename, remove, or
   subtly weaken any axiom, you must run `trust/scripts/regenerate.sh`
   and commit the updated baseline; CI fails otherwise. The hash
   change shows up in the PR diff and is the audit surface.
3. **Forbidden tier1 parameters.** Hypotheses on
   `equiv_<OP>_metaplan_tier1` theorems may not include the named
   parameters retired by the finishing series (`h_rd_val`,
   `h_byte_sum`, `h_bus_execute_matches_sail`,
   `h_entry_hi_nat`, `h_pc_fgl_lo_nat`, `h_pci_lo_val`,
   `h_entry_lo_eq`). Pattern list:
   `trust/forbidden-param-shapes.txt`.
4. **Floors.** ≥80 axioms in baseline, ≥40 tier1 theorems, plus a
   cross-witness check that catches a sabotaged regenerate.py or
   an emptied allowlist.

**Run the gate locally before pushing:** `trust/scripts/check-all.sh`.

**To legitimately extend the TCB** (high bar — most "fixes" should
not need new axioms): see "Trusted surface" section above for the
five-step process. **Adding a new trust item without those five
steps will fail CI.** Don't try to bypass the gate by editing
`trust/forbidden-param-shapes.txt` or `trust/allowed-axiom-files.txt`
without CODEOWNER review — those changes themselves are gated.

When the gate fails locally, the script names which check failed and
points at the file/line. The `trust/README.md` has the full reference.

## Layout quick-reference

```
/home/cody/zisk-fv/
├── CLAUDE.md                           # you are here
├── README.md
├── trust/                              # TCB baselines + CI gate scripts
│   ├── README.md
│   ├── baseline-axioms.txt             # source of truth (auto-generated)
│   ├── allowed-axiom-files.txt
│   ├── forbidden-param-shapes.txt
│   └── scripts/                        # check-{locality,baseline,no-output-eq,floor,all}.sh
├── docs/fv/                            # 3 live library-reference notes
│   ├── trusted-base.md                 # trust ledger; pairs with trust/baseline-axioms.txt
│   ├── extractor-notes.md              # tools/zisk-pil-extract contract
│   └── air-inventory.md                # 22-AIR extraction status
├── lakefile.toml                       # Lake 4 package config (mathlib + LeanZKCircuit + LeanRV)
├── lake-manifest.json                  # Lake-pinned dep manifest
├── lean-toolchain                      # Lean version pin
├── ZiskFv.lean                         # entry point (imports below)
├── ZiskFv/                             # Lean source
│   ├── Fundamentals/                   # Goldilocks, Transpiler
│   ├── Extraction/                     # auto-generated from pilout
│   ├── Airs/                           # named-column Valid_<AIR> + constraint bridges
│   ├── RV64D/                          # Track A: ported openvm-fv RV32D → RV64
│   ├── Spec/                           # circuit → semantic theorems
│   ├── Equivalence/                    # final per-opcode equivalence
│   └── GoldenTraces/                   # concrete witness fixtures
├── tools/
│   ├── zisk-pil-extract/               # pilout → Lean CLI (19 unit tests)
│   └── zisk-fv-harness/                # fixture emitter
├── repro/                              # Docker reproducibility containers
├── build/                              # Generated artifacts (gitignored)
│   └── zisk.pilout                     # produced by repro/build-pilout.sh
├── vendor/zisk/                        # git submodule pinned at 48cf7ccef
└── justfile                            # verify-phase0 / verify-phase1
```
