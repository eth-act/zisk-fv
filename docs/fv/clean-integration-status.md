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

### C7 — terminal-A op-bus + Binary-family ensemble

Status: in progress. `AirsClean/BinaryFamily/Ensemble.lean` now assembles
the migrated Main assume-side component plus the BinaryAdd, Binary, and
BinaryExtension provider components behind one finished `OpBusChannel`. The
old generic op-bus consumer table has been removed from this ensemble.
This proves the Main/three-provider family can live on one balanced Clean
operation-bus path, but it does not retire `op_bus_permutation_sound` until
the balanced-channel result is projected into the canonical `matches_entry`
bridges and threaded into the opcode proofs.

Main-side Clean progress: `AirsClean/Main/Circuit.lean` packages the existing
nine Main F-typed constraints with `mainWithOpBus`, which emits the
PIL-faithful operation-bus assume-side interaction using multiplicity
`-is_external_op`. `Constraints.main` remains the extracted per-row
constraint circuit; the op-bus emission is layered separately so the
generated constraint meaning is not changed.

Row-level interaction projection groundwork is now explicit for all four C7
participants. Main, BinaryAdd, Binary, and BinaryExtension each name their
`opBusMessageExpr`, expose their single op-bus interaction through
`exposedChannels`, and prove a `component_interactionsWith_opBus` lemma.
This is the hook the balance-to-`matches_entry` proof should use instead of
unfolding each component's full constraint list.
`AirsClean/BinaryFamily/Balance.lean::opBus_balanced_of_witness` now also
projects the Binary-family ensemble's `BalancedChannels` hypothesis to the
concrete `BalancedInteractions (witness.interactionsWith OpBusChannel.toRaw)`
fact used by the next bridge layer. The same file starts that next layer with
`exists_matching_nonpull_of_active_main_interaction`, a direct Clean-balance
replacement shape for the old permutation axiom: an active Main interaction
has a same-message non-pull counterpart. The remaining work is to specialize
that counterpart to BinaryAdd/Binary/BinaryExtension provider rows.

BinaryTable and BinaryExtensionTable now both have static provider-side
Clean `StaticTable` modules:
`AirsClean/BinaryTable.lean` decodes the `binary_table.pil` fixed-column
row set (`2^22 + 2^20 + 2^18` rows), and
`AirsClean/BinaryExtensionTable.lean` decodes the
`binary_extension_table.pil` row set (`6 * 2^19 + 3 * 2^11` rows). In both
cases `Spec` is exact decoded-row membership and `contains_iff` is
definitional, following the large-ROM pattern from `AirsClean/ZRomSpike.lean`.

This is still provider-side membership only. It does not by itself retire
`bin_table_consumer_wf` or `bin_ext_table_consumer_wf`: load-bearing
retirement requires the lookup-aware Binary/BinaryExtension consumers and
these static providers to be composed in the terminal Binary-family
ensemble, then threaded to the opcode proofs without adding caller promises.

Static-provider lookup entry points are now present for both consumers:
`AirsClean/Binary/Constraints.lean::mainWithStaticBinaryTable` emits the
same eight BinaryTable rows as direct `lookup (Table.fromStatic
BinaryTable.binaryTable)` operations, and
`AirsClean/BinaryExtension/Constraints.lean::mainWithStaticBinaryExtensionTable`
does the same for BinaryExtensionTable. Their bridge lemmas,
`binary_table_specs_of_static_lookup_const_soundness` and
`binary_extension_table_specs_of_static_lookup_const_soundness`, extract the
eight exact static-table membership facts from `ConstraintsHold.Soundness`.
These are provider-membership facts, not semantic `wf_properties` facts yet.
First membership-to-semantics projection has started on the
BinaryExtensionTable side:
`AirsClean/BinaryExtensionTable.lean::spec_range_conditions` derives the
legacy `range_conditions` clause from static provider membership.
The same file now also proves decoder scaffolding for per-op projections:
`blockOfIndex_lt_9` bounds the nine table blocks, and
`rowOfIndex_op_is_shift_eq_{one,zero}_of_block_*` projects the decoded
`op_is_shift` flag once the block class is known.

BinaryTable now has the analogous first provider-membership semantic
projection:
`AirsClean/BinaryTable.lean::spec_range_conditions` derives the legacy
`range_conditions` clause from exact static-table membership. The proof
projects the decoder's `a_byte`, `b_byte`, `cin`, and `c_byte` bounds over
the real 19 table blocks; it does not assert any per-op semantic clause or
retire `bin_table_consumer_wf` yet.
The BinaryTable per-op semantic projections now cover the bitwise, SEXT,
ADD/SUB, and comparison rows: `spec_wf_AND`, `spec_wf_OR`, `spec_wf_XOR`,
`spec_wf_SEXT_00`, `spec_wf_SEXT_FF`, `spec_wf_ADD`, `spec_wf_SUB`,
`spec_wf_LTU`, `spec_wf_EQ`, and `spec_wf_LT` all derive their legacy
`wf_*` clauses from exact static membership. The `LT` work fixed a stale
overstrong legacy predicate, not a circuit defect: the unsigned byte-chain
clause is now conditional on non-final bytes or same-sign final bytes, while
the signed final-byte override handles opposite signs. Downstream SLT/SLTI
proofs consume the already-existing `pi0..pi6 ≠ 1` and `pi7 = 1`
structural pins, so no `h_known_bugs` carve-out or new caller promise was
introduced.

BinaryExtensionTable lookup-channel groundwork now mirrors the BinaryTable
side: `Channels/BinaryExtensionTable.lean` defines the typed payload/channel,
`AirsClean/BinaryExtension/Constraints.lean` exposes a separate
`mainWithBinaryExtensionTable` / `binaryExtensionWithTableElaborated` path
that pulls the eight per-byte table messages, and
`AirsClean/BinaryExtension/Bridge.lean` has
`binary_extension_table_wf_of_lookup_aware_const_soundness`, extracting the
eight `wf_properties` facts from that lookup-aware path for a concrete row.
`AirsClean/BinaryExtensionTable.lean` now makes the decoded `c_lo_byte` /
`c_hi_byte` split explicitly in `Nat` before coercion to `FGL`, avoiding a
Goldilocks-modulus split for sign-extension outputs above the field modulus.
It also proves `spec_wf_SEXT_B`, `spec_wf_SEXT_H`, and `spec_wf_SEXT_W` from
exact static membership. The 64-bit shift rows now have the same
membership-to-semantics projection: `spec_wf_SLL`, `spec_wf_SRL`, and
`spec_wf_SRA` prove their shifted lo/hi output equations and
`op_is_shift = 1` from exact static membership. The W-mode shift rows are
also projected: `spec_wf_SLL_W`, `spec_wf_SRL_W`, and `spec_wf_SRA_W` prove
the 32-bit shift contribution and sign-extension split from exact static
membership. BinaryExtensionTable now has all nine per-op `wf_*` projections
plus `spec_range_conditions`; C7 still has to compose these provider facts
with the lookup-aware consumers and rewire load-bearing proofs to retire
`bin_ext_table_consumer_wf`.

Static lookup bridges now project provider membership to legacy semantics:
`AirsClean/Binary/Bridge.lean::binary_table_wf_of_static_lookup_const_soundness`
and
`AirsClean/BinaryExtension/Bridge.lean::binary_extension_table_wf_of_static_lookup_const_soundness`
return the same eight per-byte `wf_properties` facts as the old lookup-aware
axiom-facing bridges, but derive them from
`lookup (Table.fromStatic ...)` membership and the static providers'
`spec_wf_properties` lemmas. This still does not remove the two legacy axioms
from closures until the load-bearing opcode proofs are rewired to consume
these static-lookup bridge facts.

The bitwise BinaryTable route is now threaded through the load-bearing proof
stack for AND/ANDI/OR/ORI/XOR/XORI without changing canonical theorem
signatures. `Airs/Binary/BinaryPackedCorrect.lean` has static-provider
`binary_{and,or,xor}_chunks_eq_bv_{and,or,xor}_of_wf` lifts over
`consumer_byte_match_wf`; `EquivCore/Bridge/Binary.lean` packages the
faithful eight-byte static lookup shape (bytes 0-3 use `b_op`, bytes 4-7 use
`b_op_or_sext`) and derives the low-byte `b_op` pin from Binary core
constraints plus the existing emitted-op / `b_op_or_sext` pin.
`EquivCore/WriteValueProofs/BinaryLogic.lean`, the six bitwise opcode cores,
the six compliance wrappers, the six channel-level equivalence files, and
the RTYPE/ITYPE dispatchers now expose `_of_static_lookup` routes. Globally,
`Compliance.lean::zisk_riscv_compliant_program_bus_binary_family_of_static_lookup`
composes those bitwise BinaryTable routes with the existing BinaryExtension
static routes. The canonical theorem still uses the old route until the C7
terminal ensemble supplies `StaticLookupSoundness` internally rather than as
a noncanonical theorem parameter. Binary core facts are now projected from
that same static-lookup path.

The 64-bit Binary chain route has now reached the same lower proof layers for
SUB/SLTU/SLTIU/SLT/SLTI. `BinaryPackedCorrect.lean` has
`consumer_byte_match_chain_wf` lifts for `OP_SUB`, `OP_LTU`, and `OP_LT`;
`WriteValueProofs/Arith.lean` and `WriteValueProofs/BinaryCompare.lean`
have `_of_wf` rd-value closures; and `EquivCore/Bridge/Binary.lean`
packages the faithful static lookup shape for 64-bit chain rows, including
carry-link and position pins plus a static SUB final-carry closer.
`EquivCore/Sub.lean` now has `equiv_SUB_of_wf` and
`equiv_SUB_of_static_lookup`, and `EquivCore/{Sltu,Sltiu,Slt,Slti}.lean`
have `_of_wf` theorem variants over the same static-provider chain predicate.
The compare c-lane closer is proved in `EquivCore/Bridge/Binary.lean`: static
LTU/LT rows force all c-bytes to zero and emit `carry_7` as the result.
`EquivCore/{Sltu,Slt,Sltiu,Slti}.lean` now expose
`equiv_*_of_static_lookup` routes. The core routes still take the concrete
64-bit row-shape pins, but the Compliance wrappers now derive those pins from
the selected Binary row's op-bus emission plus derived `b_op < 128` and
`mode32 < 2` range facts. The RTYPE and ITYPE dispatchers thread those five
static routes through the same noncanonical C7 surface as the bitwise Binary
routes; their BinaryTable obligation has now shrunk to
`StaticLookupSoundness` alone, with no explicit `h_binary_chain_shape`
premise, no separate Binary core premise, and no reuse of the old chain-pin
axiom.

### C8 — Mem

Status: in progress. `AirsClean/Mem` now packages the existing Mem
`Row`/`Constraints`/`Spec`/`Soundness` material as a Clean
`GeneralFormalCircuit`, `Air.Flat.Component`, and minimal ensemble. The
component covers the nine F-typed per-row Mem constraints and routes
`spec_of_valid` through `spec_via_component`. Its Clean table assumptions are
`True` so the ensemble remains constructible; the unused boolean/range
assumptions stay outside the component trust boundary.

The memory-bus provider path is intentionally not claimed here. The Mem row
stores two 32-bit chunks, while the current memory-bus message carries eight
byte lanes; wiring that provider side requires an explicit byte-lane witness
and range/packing proof against the real PIL bus shape. That belongs to the
memory-family terminal work, not to a hidden C8 promise.

### C6 — Binary

Status: complete. C3/C4-b is closed under the agreed known-defect convention:
ArithTable trust-shape cleanup is complete, and the confirmed signed-MUL
circuit defect is visible through `h_known_bugs` / the false
`h_no_signed_mul_witness_defect` premise. C5 BinaryExtension is complete;
the next Clean integration phase is C7 terminal-A.

Initial C6 progress: `AirsClean/Binary` now has a Clean
`GeneralFormalCircuit`, `Air.Flat.Component`, and minimal op-bus ensemble.
The component covers the seven F-typed Binary constraints and emits the
Binary operation-bus push. `Bridge.lean` exposes
`opBusMessage_toEntry_rowAt_eq_opBus_row`, definitionally matching the Clean
provider payload to the legacy `opBus_row_Binary`, and `spec_of_valid` now
routes through `spec_via_component`. BinaryTable lookup semantics still
flow through the existing Binary lookup-soundness axioms until C7. No new
trust-ledger axiom is added: the mandatory Clean completeness field is
conditional on the same row `Spec`, so it does not claim honest-prover
constructibility beyond the already-stated soundness relation.

Lookup-channel groundwork: `Channels/BinaryTable.lean` now defines the typed
`BinaryTableChannel` whose guarantee is the existing `BinaryTable.wf_properties`
predicate, and `AirsClean/Binary/Constraints.lean` exposes a separate
`mainWithBinaryTable` / `binaryWithBinaryTableElaborated` path that pulls the
eight per-byte BinaryTable messages. `AirsClean/Binary/Bridge.lean` also has
`binary_table_wf_of_lookup_aware_const_soundness`, which extracts the eight
`wf_properties` facts from that lookup-aware path for a concrete row. This
does not retire `bin_table_consumer_wf` by itself: C7 still has to supply the
balanced table provider side before those guarantees can replace the legacy
lookup axiom in load-bearing opcode proofs.

### C5 — BinaryExtension

Status: complete. The remaining BinaryExtension table-semantics axiom,
`bin_ext_table_consumer_wf`, is intentionally deferred to C7 because that is
the Binary-family terminal lookup/ensemble phase.

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
