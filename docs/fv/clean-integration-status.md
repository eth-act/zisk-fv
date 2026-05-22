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

### C2.5 — Defect framework setup (current branch, 2026-05-22)

- `docs/fv/defect-ledger-design.md` defines the rule: a defect is neither a
  trust-ledger axiom nor a silent scope exclusion.
- `docs/fv/defects.md` seeds the ledger with the ArithTable trust-shape
  defect, the signed-MUL malicious-witness soundness defect, and the
  FENCE no-op/incomplete-support triage item.
- `ZiskFv/Compliance/Defects.lean` adds the Lean-side `DefectId`,
  `Blocks`, and `NoKnownDefect` predicates.
- `ZiskFv.Compliance.zisk_riscv_compliant_program_bus_except_known_defects`
  adds the explicit `h_known_bugs : Defects.NoKnownDefect env` binder.
  The existing `OpEnvelope` constructors already carry validity witnesses,
  so `h_known_bugs` is an orthogonal defect-exclusion hypothesis rather than
  a replacement for validity.
- The defect-aware theorem now routes DIVU and the remaining Arith-family
  arms through `h_known_bugs` instead of through the old Arith proof closure.
  Direct closure check:
  `lake exe trust-gate print-axiom-closure
  ZiskFv.Compliance.zisk_riscv_compliant_program_bus_except_known_defects`
  lists 66 project axioms and no `arith_table_op_*` /
  `arith_{mul,div}_table_lookup_sound` entries.

## Active phase

### C5 — BinaryExtension

Status: in progress. C3/C4-b is closed under the agreed known-defect convention:
ArithTable trust-shape cleanup is complete, and the confirmed signed-MUL
circuit defect is visible through `h_known_bugs` / the false
`h_no_signed_mul_witness_defect` premise. The next Clean integration phase
is BinaryExtension.

Initial C5 progress: `AirsClean/BinaryExtension` now has a Clean
`GeneralFormalCircuit`, `Air.Flat.Component`, and minimal op-bus ensemble.
The component emits the BinaryExtension operation-bus push and has no F-only
`assertZero` constraints, matching the extracted AIR. Its `Spec` remains
`True`; BinaryExtensionTable semantic facts still flow through the existing
lookup-soundness axiom (`bin_ext_table_consumer_wf`) until the
Binary-family lookup phase. There is no trust delta for the component:
BinaryExtension completeness is proved directly because the local circuit is
only an operation-bus push with `True` guarantees.

Provider-side op-bus bridge progress: `AirsClean/BinaryExtension/Bridge.lean`
now defines the FGL-level Clean `OpBusMessage` emitted by the component and
proves
`opBusMessage_toEntry_rowAt_eq_opBus_row`, a definitional equality with the
pre-Clean `opBus_row_BinaryExtension` row. This gives C7 a concrete
adapter from the Clean provider payload into the existing operation-bus
entry surface without adding trust or pretending the
BinaryExtensionTable lookup facts have been discharged.

The C5 `spec_via_component` theorem now also follows the same F-3 route as
the non-trivial components: normalize `circuit.soundness`, instantiate a
constant-expression row, and project the resulting `Spec`. Since the local
`Spec` is still `True`, this is a hygiene/load-bearing-entrypoint cleanup
rather than promise discharge.

C5 also retires the redundant `binary_extension_row_byte_lookups` axiom:
the `ByteLookupHypotheses` bundle is now constructed definitionally from
the BinaryExtension row columns. The remaining table semantics still rely on
`bin_ext_table_consumer_wf`, so this is a duplicate witness-shape removal,
not the terminal BinaryExtensionTable proof.

`binary_extension_op_is_shift_pin` is also now derived from the constructed
byte-0 entry plus `bin_ext_table_consumer_wf`; the table's per-op
well-formedness predicates already pin `op_is_shift` for the shift and
SEXT opcode families. After this, BinaryExtension has one remaining
table-semantics axiom: `bin_ext_table_consumer_wf`.

### C3.2-P — controlled ArithTable axiom purge

Status: complete. This was a temporary invariant-relaxation phase for the
arithmetic-table cleanup. C3 and C4 are tracked separately. C3 owns only
`MULHU`, `MULH`, `MULHSU`, `MUL`, and `MULW`; C4 owns only the Div/Rem
family. The visible progress metric was removing constructors from
`Defects.UsesOpcodeSpecificArithTableAxiom`, which is now empty.

Arithmetic-table axiom classification is tracked in
[`arith-table-axiom-audit.md`](arith-table-axiom-audit.md). That audit is
the source of truth for whether an old `arith_table_op_*` fact is a true
finite-table projection, false as stated, or requires a dynamic row proof.

Current C3.2-P checklist:

- 🪓 C3.2-P1 arithmetic-table facts classified in
  `arith-table-axiom-audit.md`.
- 🪓 C3.2-P2 false opcode-shaped facts purged from active closures.
- 🪓 C3.2-P3 true static facts replaced by Clean finite-table projections.
- 🪓 C3.2-P4 non-static breaks classified as dynamic proof targets or
  explicit defects.
- 🪓 C3.2-P5 zero-sorry and normal trust gates restored.
  Completed for the ArithTable purge: all W-contract holes are removed
  (`MULW`, `DIVUW`, `REMUW`, `DIVW`, and `REMW`), the false opcode-shaped
  ArithTable axiom declarations for `MUL`, `MULH`, `MULHSU`, `MULW`,
  unsigned-W DIV/REM, and signed-W DIV/REM have been deleted from
  `Ranges.lean`, and the signed-MUL residual is now an explicit
  known-defect exclusion rather than a `sorry`.

C3.2-P2 completion note: the active wrappers for `MULH`, `MULHSU`, `MUL`,
`MULW`, `DIVUW`, `REMUW`, `DIVW`, and `REMW` no longer call
`arith_table_op_mulh_mode_pin`, `arith_table_op_mulhsu_mode_pin`,
`arith_table_op_mul_mode_pin`, `arith_table_op_mulw_mode_pin`,
`arith_table_op_div_rem_unsigned_w_mode_pin`, or
`arith_table_op_div_rem_signed_w_mode_pin`. `lake build` succeeds without
proof holes. The three signed-MUL residuals are visible as
`h_no_signed_mul_witness_defect : False` binders and as the global
`h_known_bugs` hypothesis.

C3.2 and C3.3 are complete under the current branch convention: `MULH` and
`MULHSU` are not claimed non-vacuously. Their theorem statements carry the
explicit false premise `h_no_signed_mul_witness_defect : False`, derived at
the global theorem from `h_known_bugs`, so the theorem interface itself
marks the confirmed circuit bug. In a separate ZisK worktree at commit
`0142ab5d7`, branch `repro/mulh-mulhsu-malicious-witness-demo`, Docker image
`zisk-arith-mul-repro:mulh-demo` accepted and verified malicious proofs for
`MUL(-1,1)=1`, `MULH(-1,1)=0`, and `MULHSU(-1,1)=0`.

Current C3 checklist:

- 🪓 C3.1 `MULHU` unblocked from `arithTableTrustShape`.
- 🪓 C3.2 `MULH` defect-qualified; no static-ROM `np_xor`, no
  opcode-shaped ArithTable axiom, and the remaining semantic claim is
  intentionally under the false `h_no_signed_mul_witness_defect` premise.
- 🪓 C3.3 `MULHSU` defect-qualified; same convention as `MULH`.
- 🪓 C3.4 low-half `MUL` ArithTable trust-shape repaired; any remaining
  semantic claim is intentionally under `arithMulSignedWitnessSoundness`.
- 🪓 C3.5 `MULW` repaired and unblocked; no static-ROM `sext = 0`.
  `equiv_MULW` is routed through the real W sign-extension evidence and
  op-bus-derived operand high-chunk zeroes; `.mulw` is removed from
  `UsesOpcodeSpecificArithTableAxiom`.

Current C4 checklist:

- 🪓 C4.1 `DIVU` and `REMU` unblocked.
- 🪓 C4.2 non-W signed `DIV` and `REM` unblocked; dynamic facts classified
  as Binary-side / `assumes_operation`, not static ArithTable facts.
- 🪓 C4.3 unsigned W-mode `DIVUW` and `REMUW` repaired and unblocked; no
  static-ROM `sext = 0`.
- 🪓 C4.4 signed W-mode `DIVW` and `REMW` repaired and unblocked; no
  static-ROM `sext = 0`.

C3/C4 trust-shape completion note: all ArithMul and Div/Rem-family
constructors are now removed from `UsesOpcodeSpecificArithTableAxiom`.
The remaining signed-MUL blockers are recorded under
`arithMulSignedWitnessSoundness`. The remaining signed Div/Rem trust items
in their closures are documented dynamic row/range/bus facts deferred to C6,
not C4 ArithTable trust-shape blockers.

Per-opcode completion rule: inspect closure, remove exactly that
constructor from `UsesOpcodeSpecificArithTableAxiom`, update the defect
ledger/status, then run `lake build`, V1, and V2.

### Phase 3 — Per-AIR transpiler rewrite

Reference for the broader PR series after C3/C4:

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
