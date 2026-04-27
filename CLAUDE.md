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

### Metaplan + prompted phases

Work proceeds under **`ai_plans/zisk-fv-metaplan.md`**, which defines the
phase sequence and scope. The user manually prompts the agent to begin
each phase (e.g. "execute Phase 1"). The agent does **not** self-dispatch
the next phase — between phases there are usually architectural
decisions or memory updates the user wants to review first.

Each phase has a `ai_plans/zisk-fv-phase-N.md` plan:
- Pre-execution sections (Context, Reconnaissance, Scope, Execution
  order, Verification) are written before work starts.
- When the phase finishes, append a **"Phase N status — CLOSED <date>"**
  section containing: what shipped, what was learned, what remains. Do
  not create separate handoff files — append in-place so each plan is a
  self-contained historical record.

### Documentation split

- **`ai_plans/`** — planning docs. One per phase. Append-only after
  execution (CLOSED sections).
- **`docs/fv/`** — *library reference* notes. These should explain
  durable facts about the library (contracts, invariants, known quirks)
  that future agents need to understand the code. **Not** transient
  phase handoffs or task lists. Current contents:
  `extractor-notes.md` (contract / pilout structure / oracle rules for
  `tools/zisk-pil-extract/`).
- **memory** — agent-private notes at
  `/home/cody/.claude/projects/-home-cody-zisk/memory/`. Project-level
  facts that persist across conversations; update in lockstep with
  CLOSED sections.

### Traps captured during Phase 1 (don't re-discover these)

See `ai_plans/zisk-fv-phase-1.md` "What was learned" for details.
Short list:

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

## Layout quick-reference

```
/home/cody/zisk-fv/
├── CLAUDE.md                           # you are here
├── README.md
├── ai_plans/                           # metaplan + per-phase plans (append-only)
│   ├── zisk-fv-metaplan.md
│   ├── zisk-fv-feasibility.md
│   ├── zisk-fv-phase-0.md              # CLOSED
│   └── zisk-fv-phase-1.md              # CLOSED
├── docs/fv/                            # library-reference notes only
│   └── extractor-notes.md
├── ZiskFv/                             # Lake 4 package (mathlib + LeanZKCircuit + LeanRV)
│   └── ZiskFv/
│       ├── Fundamentals/               # Goldilocks, Transpiler
│       ├── Extraction/                 # auto-generated from pilout
│       ├── Airs/                       # named-column Valid_<AIR> + constraint bridges
│       ├── RV64D/                      # Track A: ported openvm-fv RV32D → RV64
│       ├── Spec/                       # circuit → semantic theorems
│       ├── Equivalence/                # final per-opcode equivalence
│       └── GoldenTraces/               # concrete witness fixtures
├── tools/
│   ├── zisk-pil-extract/               # pilout → Lean CLI (19 unit tests)
│   └── zisk-fv-harness/                # fixture emitter
├── pil/zisk.pilout                     # vendored 7MB artifact (gitignored upstream)
├── vendor/zisk/                        # git submodule pinned at 48cf7ccef
└── justfile                            # verify-phase0 / verify-phase1
```
