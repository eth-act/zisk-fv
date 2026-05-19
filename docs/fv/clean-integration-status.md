# Clean integration — current status (clean-full branch)

This is the working branch for the full Clean integration per
[`/home/cody/.claude/plans/ok-i-will-let-humble-reddy.md`]. It
branches off `clean-integration` (which had landed the bus-level
axiom consolidation from 122 → 116 axioms without taking Clean as
a dep).

## Completed phases

### Phase 0 — Nix dep + Lake dep + shrinkage gate (commit `24bd2cb`)

- Clean (Verified-zkEVM/clean @ 95c8cc2e) pinned as a flake input.
- `nix/clean.nix` builds the source tree; `nix/populate.nix` copies
  to `build/clean-lean/`; `lakefile.toml` has the path require.
- `trust/.shrinkage-floor` (starts at 116) + `check-shrinkage.sh`
  as V1 gate #10. Lowering the floor requires CODEOWNER review of
  the diff alongside the axiom removal.
- `nix flake check --no-build` passes; `lake build` clean; all
  10/10 V1 + V2 trust gates green.

### Phase 1 — Typed channels (commit `9caf133`)

- `ZiskFv/Channels/OperationBus.lean` — `OpBusMessage`
  ProvableStruct + `OpBusChannel : Channel FGL OpBusMessage`.
- `ZiskFv/Channels/MemoryBus.lean` — analogous for memory bus.
- `ZiskFv/Channels/RangeBus.lean` — `BytesTable :
  StaticLookupChannel`, `BytesChannel := Channel.fromStatic ...`.
- Two feedback entries filed in `docs/clean-feedback.md` (the
  `import Clean` ↔ Mathlib `Batteries.Data.Fin.Fold` collision;
  the `[Field F]` ↔ TypeMap mismatch).
- 4 channels remain (BinaryTable, BinaryExtensionTable, ArithTable,
  MemAlignRom) — deferred to Phase 3 to land alongside the AIR
  rewrites that consume them.

### Phase 2 — `state_effect_via_channels` + ADD probe (commit `1acd7b0`)

- `ZiskFv/Vm/StateEffect.lean` — `ChannelEnsembleOutput`,
  `state_effect_via_channels`, and the compatibility bridge
  `state_effect_via_channels_eq_bus_effect_2` (`rfl` for the
  trivial extractor; non-trivial extractors come from Phase 3's
  channel-balance derivations).
- `ZiskFv/Vm/Probe_ADD.lean` — `equiv_ADD_v2` derived from
  `equiv_ADD` as a one-line corollary. Validates Phase 4's wrapper
  pattern works.
- Critical architectural risk *(can the channel-balance form
  be expressed as a pure function of channel output?)* — RESOLVED:
  by definition `rfl` via the trivial extractor; trust improvement
  comes in *who supplies the rows* (Phase 3).

## Active phase

### Phase 3 — Per-AIR transpiler rewrite

Status: **not started in this session.** Reference for the next
PR series:

1. Rust side (`tools/pil-extract/src/clean_emit.rs`): adapt the
   spike-branch transpiler at `tools/pil-to-clean/` (which already
   emits Clean components for a single AIR) into the existing
   `tools/pil-extract` shape. The spike's emitter is ~275 LoC.

2. AIR-by-AIR (lowest blast radius first): **BinaryAdd → Binary →
   BinaryExtension → MemAlign{Byte,ReadByte,_} → Mem → Arith{Mul,
   Div,_} → Main**. Each PR:
   - emits `build/extraction/Clean/<AIR>.lean` (gitignored)
   - hand-writes `ZiskFv/AirsClean/<AIR>/{Spec,Soundness}.lean`
   - provides compatibility lemma: existing `Valid_<AIR>` derived
     from `<AIR>.circuit.Soundness`
   - retires that AIR's old axiom-file entries from
     `trust/allowed-axiom-files.txt`
   - lowers `trust/.shrinkage-floor` by exactly the number of
     axioms removed (e.g. BinaryAdd: 116 → 115)

3. Important adaptation note: the spike's `BinaryAdd/Soundness.lean`
   uses `[Fact (p > 2^65)]`. Goldilocks `p ≈ 2^64` so `2^65 > p` —
   the pGt fact doesn't directly hold. The port needs to weaken the
   spike's assumption to `p > 2^33` (sufficient for 32-bit chunk
   range bounds), or specialise more aggressively against FGL.

4. Per-AIR expected axiom reduction (from the plan):
   - BinaryAdd: −1 (op-bus emission bundle)
   - Binary: −5 (range pins + table-consumer-wf)
   - BinaryExtension: −7 (range pins + table chain)
   - MemAlign\*: −2 (perm + ROM lookup)
   - Mem: −9 (7 main_*_emission_bundle + lookup + LaneMatch)
   - Arith\*: −30 (range pins consolidated; some Euclidean pins irreducible)
   - Main: −1 (op-bus consumer wf)
   - **Aggregate target: 116 → ~70 axioms.**

## Phases 4–7

Same plan as the master file. Phase 4 (per-opcode `equiv_<OP>_v2`)
follows the pattern proved in `ZiskFv/Vm/Probe_ADD.lean`: a single
`rw [state_effect_via_channels_eq_bus_effect_2]` followed by
`exact equiv_<OP>`. The 63 wrappers can be batched by archetype
into 10–12 PRs.

## Trust gate state

| Metric                 | Value |
| ---------------------- | ----- |
| Axiom baseline         | 116   |
| Shrinkage floor        | 116   |
| Canonical equiv_<OP>   | 63    |
| V1 checks              | 10/10 |
| V2 semantic            | green |
| `lake build`           | 8508 jobs |
| `nix flake check`      | green |
