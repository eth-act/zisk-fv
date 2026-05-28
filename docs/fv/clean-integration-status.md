# Clean integration — current status (clean-full branch)

This is the working branch for the full Clean integration per
[`/home/cody/.claude/plans/ok-i-will-let-humble-reddy.md`]. It
branches off `clean-integration` (which had landed the bus-level
axiom consolidation from 122 → 116 axioms without taking Clean as
a dep). Current working status after T5:
`lake build`, V1, and V2 pass with 58 source trust-ledger axioms and a
55-name global compliance closure.

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
  lists 58 source trust-ledger axioms and no `arith_table_op_*`,
  `arith_{mul,div}_table_lookup_sound`, or DIV/REM `transpile_*`
  entries.

## Active phase

### T7 — Final ensemble re-root and deletion pass

T4 (memory-family terminal phase) is **CLOSED** as of commit `f8528f2`
(2026-05-27). All load/store canonical paths route through Clean
structural memory witnesses; 7 memory-bus / MemAlign trust axioms
retired from the global closure. Trust ledger: 82 source axioms /
80-name compliance closure. `lake build` + V1 + V2 all green.

C8 (chunk-shape `MemoryBusEntry` cutover) and T4.0 (ZisK instruction
ROM modeling) were the enabling prerequisites and are also closed.

T5 (Arith-family terminal phase) is **CLOSED** as of commit `de5080d`
(2026-05-28). The first
T5 landing retired `arith_mul_table_lookup_sound` /
`arith_div_table_lookup_sound` from source and from the global closure:
canonical `MUL*`, `DIV*`, and `REM*` paths now consume explicit
row-native `ArithTableSpec` witnesses. The second T5 landing retired
`main_external_arith_emission_bundle` from the canonical/global closure:
the 13 Arith-family canonical paths now consume an
`ExternalArithMemoryWitness` that exposes the selected Clean Main
`cMemMessage`, row equality, `store_pc = 0`, and memory-entry match
needed to derive the rd-write byte lanes. The source axiom remains only
as historical documentation; it is retired from the trust ledger.
`main_store_pc_emission_bundle` remains a T6/T7 target.

The third T5 landing replaced the raw canonical `ArithTableSpec`
binders with lookup-aware Clean witnesses:
`ArithMulTableWitness` / `ArithDivTableWitness`. These witnesses carry
`ConstraintsHold.Soundness` for the selected
`mainWithArithTable (constVar (rowAt v r_a))` operation and derive
`ArithTableSpec` through the Clean bridge, so table membership is no
longer an opaque caller promise.

The final T5 landings retired the signed-MUL witness trust through explicit
defect gating, retired every remaining class-#6b Arith dynamic source axiom,
and removed the DIV/REM transpiler contracts from the trust ledger while
those opcodes are blocked by
`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`. The active phase is now
**T7 — Final ensemble re-root and deletion pass**. T6's range-bus terminal
retirement remains an open dependency for final T7 closure.

### C7 — CLOSED (axiom retirements landed in T4-purge commits)

Closed 2026-05-25/26. The C7 checklist below shows the project state
when work began; the actual axiom retirements landed in T4-purge
commits `c2046e6` (T4.P1+P2 immediate-shift `_of_wf` rename),
`e52485e` (T4.P3+P4+P6 — `op_bus_permutation_sound` and
`bin_ext_table_consumer_wf` retired from source), `fbfe959` (T4.P5
tolerated completeness-direction axiom), `774845e`
(`bin_table_consumer_wf` source + orphan-helper cascade-delete), and
`fad1a40` (scope-of-follow-up doc). Net: all four C7-target axioms
(`op_bus_permutation_sound`, `op_bus_perm_sound_{Binary,BinaryAdd,
BinaryExtension}`, `bin_table_consumer_wf`,
`bin_ext_table_consumer_wf`) are gone from both
`trust/baseline-axioms.txt` and the global theorem closure.
Source-text references that remain are exclusively docstring/comment
mentions, no live declarations.

`AirsClean/BinaryFamily/Ensemble.lean` now assembles
the migrated Main assume-side component plus the BinaryAdd, Binary, and
BinaryExtension provider components behind one finished `OpBusChannel`. The
old generic op-bus consumer table has been removed from this ensemble.
This proves the Main/three-provider family can live on one balanced Clean
operation-bus path. A lookup-aware parallel route,
`binaryFamilyStaticBinaryTableOpBusEnsemble`, now replaces the plain Binary
and BinaryExtension components with
`AirsClean.Binary.staticLookupComponent` and
`AirsClean.BinaryExtension.staticLookupComponent`; this is the route for
bitwise Binary rows whose op-bus provider row must also carry direct static
table lookup constraints and whose non-Binary provider branches must be
excluded from provider-local facts. Neither ensemble retires
`op_bus_permutation_sound` until the balanced-channel result is threaded into
the canonical theorem closures.

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
`exists_matching_nonzero_nonpull_of_active_main_interaction`, a direct
Clean-balance replacement shape for the old permutation axiom: an active Main
interaction has a same-message counterpart whose multiplicity is neither
`-1` nor `0`. This uses the Clean fork theorem
`exists_nonzero_push_of_pull`; the older non-pull theorem remains as a
compatibility projection. The remaining work is to specialize that
counterpart to BinaryAdd/Binary/BinaryExtension provider rows.
The next bridge layer has started:
`component_mem_binaryFamily_cases` exposes the concrete verifier/Main/
BinaryAdd/Binary/BinaryExtension component list, and
`exists_matching_nonMain_component_of_active_main_interaction` proves that
the balanced counterpart lies on a non-Main table from `witness.Constraints`
and `witness.BalancedChannels`, with no caller-supplied Main multiplicity
premise. The Main exclusion is local:
`AirsClean/Main/Circuit.lean::is_external_op_boolean_of_mainWithOpBus_constraints`
projects the `is_external_op` boolean assertion directly from concrete
`mainWithOpBus` operations, and
`is_external_op_boolean_of_component_constraints` adapts it through Clean's
`Component.constraintsHold_iff` idiom. `Balance.lean` then proves
`main_table_opBus_mult_neg_one_or_zero_of_constraints`, excluding nonzero
non-pull Main rows by the field fact `x * (1 - x) = 0 -> x = 0 or x = 1`.
The same file now also proves
`exists_matching_provider_component_of_active_main_interaction`: the
balanced counterpart must come from BinaryAdd, Binary, or BinaryExtension
after the empty verifier table and Main are ruled out. The lookup-aware
parallel lemmas
`exists_static_matching_nonzero_nonpull_of_active_main_interaction`,
`exists_static_matching_nonMain_component_of_active_main_interaction`, and
`exists_static_matching_provider_component_of_active_main_interaction` prove
the same classification for `binaryFamilyStaticBinaryTableOpBusEnsemble`,
with the Binary branch classified as `Binary.staticLookupComponent`.

Provider-row projection groundwork is now explicit. `Balance.lean` has a
generic singleton-channel row extractor,
`exists_row_eval_of_singleton_interactionsWith`, plus Main/BinaryAdd/Binary/
BinaryExtension specializations that turn a concrete table-level op-bus
interaction into the corresponding exposed Clean interaction evaluated at
some table row. At the channel level,
`Channels/OperationBus.lean::matches_entry_of_eval_msg_eq` converts equality
of evaluated raw Clean op-bus message arrays into legacy
`OperationBus.matches_entry` for multiplicity `1` on both entries.
`AirsClean/BinaryFamily/Balance.lean::exists_provider_row_matches_entry_of_active_main_table_interaction`
now composes those pieces: from a constrained Binary-family
`EnsembleWitness`, a balanced `OpBusChannel`, and an active Main table
interaction, it returns a concrete Main table row, a concrete provider table
row, provider classification (`BinaryAdd | Binary | BinaryExtension`), and a
legacy `matches_entry` between the evaluated Clean messages. This deliberately
does not assert that an arbitrary Clean row corresponds to an arbitrary legacy
`Valid_*` row; the remaining terminal C7 work is to thread these Clean-row
facts through the noncanonical static routes and then the canonical closures.
The lookup-aware companion,
`exists_static_provider_row_matches_entry_of_active_main_table_interaction`,
returns the same shape for the static ensemble and keeps the Binary provider
row on `Binary.staticLookupComponent`, so the next bridge can consume that
same row's static BinaryTable facts. The noncanonical bitwise routes now
consume lookup-aware Binary table rows directly:
`Equivalence/{And,Or,Xor}.lean::equiv_*_of_static_table_row` derives the
Binary core row facts and static BinaryTable facts from
`Binary.staticLookupComponent`'s `table.Spec` before invoking the row-native
AND/OR/XOR wrappers. `Compliance/Dispatch/RTYPE.lean` threads those
table-row routes through an `OpEnvelope` family route for RTYPE bitwise arms,
and `Compliance.lean::zisk_riscv_compliant_program_bus_binary_family_of_static_table_row`
threads that through the global noncanonical C7 Binary-family theorem while
the not-yet-row-native Binary-family arms remain on their existing static
lookup route.

Current C7 checklist:

- 🪓 Clean balance projects active Main op-bus rows to concrete provider rows.
- 🪓 Binary provider rows now have row-native byte-table facts.
- 🪓 Row-native packed AND/OR/XOR identities are proved over `BinaryRow`.
- 🪓 Row-native write-value facts added.
- 🪓 Row-native opcode-core theorems added.
- 🪓 Channel-level row-native wrappers added.
- 🪓 Lookup-aware Binary component exposes the same op-bus provider row plus static BinaryTable lookup facts.
- 🪓 Lookup-aware Binary-family ensemble and provider-row `matches_entry` projection added.
- 🪓 Thread the static-provider row route into the noncanonical C7 global route.
- 🪓 Thread that route into canonical closures for the six bitwise
  Binary-family arms (AND/OR/XOR/ANDI/ORI/XORI). The legacy wrapper surface
  now exposes static-provider-row versions of those theorem names, so
  `binary_b_op_or_sext_eq_op_general` and
  `binary_per_byte_lookup_witness` are deleted from the live trust ledger.
- 🪓 Thread the same static-provider row route into the remaining 64-bit
  BinaryTable consumers `SUB`, `SLT`, `SLTU`, `SLTI`, and `SLTIU`.
- 🪓 Thread the static-provider BinaryExtension row route into the full
  shift family (`SLL/SRL/SRA`, immediate shifts, and W-shifts).
- 🪓 Record the remaining non-shift consumers of `op_bus_permutation_sound`.
- 🪓 Record the remaining non-shift consumers of `bin_table_consumer_wf` and
  `bin_ext_table_consumer_wf`.

Retirement blocker update: the evaluated-message projection issue is cleared.
The lookup-aware ensemble constrains both Binary rows and BinaryExtension rows
with their direct static table facts. BinaryExtension uses
`AirsClean.BinaryExtension.staticLookupComponent`, whose `Spec` includes the
eight exact BinaryExtensionTable memberships for the same row that emits the
op-bus message. `AirsClean.BinaryExtensionTable.spec_op_val_ne_bitwise` proves
those table rows cannot carry bitwise Binary opcodes 14/15/16, and
`staticLookupComponent_op_val_ne_bitwise_of_spec` projects that fact through
the component `Spec`. `Channels.OperationBus.OpBusMessage.eval_op`,
`AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr`, and
`AirsClean.Main.component_eval_opBusMessageExpr` now bridge evaluated Clean
messages back to their row-native bus messages without unfolding full
provider rows in `Balance.lean`. The static balance route therefore refines
the provider disjunction to a concrete lookup-aware Binary provider row and
then rewrites the selected Clean Main row back to legacy
`opBus_row_Main m r_main`. The row-native XOR/XORI table routes no longer
carry an explicit `b_op_or_sext = OP_XOR` promise:
`BinaryTable.spec_op_val_ne_zero`,
`Binary.static_table_b_op_or_sext_eq_of_xor_emit`, and
`Binary.static_table_xor_mode_pins_of_emit` derive the pins from the same
lookup-aware provider row by ruling out the ambiguous `mode32 = 1, b_op = 0`
shape. Canonical dispatcher replacement is now threaded for the six bitwise
Binary-family arms (AND/OR/XOR/ANDI/ORI/XORI): the relevant `OpEnvelope`
constructors carry the concrete lookup-aware Binary provider table row, and
the RTYPE/ITYPE dispatchers call the row-native `equiv_*_of_static_table_row`
routes directly. The legacy wrapper theorem names have also been migrated to
static-provider-row signatures, so `binary_b_op_or_sext_eq_op_general` and
`binary_per_byte_lookup_witness` are no longer live declarations. After
regeneration, `lake build`, `trust/scripts/check-all.sh`, and
`trust/scripts/check-all-semantic.sh` pass with 92 axioms in both
`baseline-axioms.txt` and the global compliance closure.

The remaining 64-bit BinaryTable consumers now follow that same route.
`EquivCore/Bridge/Binary.lean` adds a row-native 64-bit chain discharge over
`StaticBinaryTableWfFacts row`; `EquivCore/{Sub,Slt,Sltu,Slti,Sltiu}.lean`
expose `*_of_static_row` variants; and
`Equivalence/{Sub,Slt,Sltu,Slti,Sltiu}.lean` plus the corresponding
`Compliance/Wrappers` theorem names now take the concrete lookup-aware
Binary provider table row. The regenerated semantic closure removes
`binary_consumer_byte_match_chain_pin`, `op_bus_permutation_sound`, and
`bin_table_consumer_wf` from those five canonical opcode closures; each now
depends only on `range_bus_sound` plus its `transpile_*` axiom.

T1.6 is complete. The same concrete-row pattern now covers the whole
BinaryExtension shift family: `SLL/SRL/SRA`, `SLLI/SRLI/SRAI`, and
`SLLW/SRLW/SRAW/SLLIW/SRLIW/SRAIW`. `AirsClean/BinaryExtension/Bridge.lean`
exposes `validOfRow`; the relevant `EquivCore/*` files expose row-native
`*_of_static_row` routes; the canonical wrappers/equivalence files and
`OpEnvelope` now carry the lookup-aware BinaryExtension provider table row.
The immediate-W write-value helpers consume `ByteLookupWfHypotheses`
directly, so their closure no longer re-enters
`bin_ext_table_consumer_wf`. After regeneration, all twelve shift-family
canonical closures are exactly `range_bus_sound` plus the corresponding
`transpile_*` axiom, with no `op_bus_permutation_sound` and no
`bin_ext_table_consumer_wf`. `lake build`, `trust/scripts/check-all.sh`,
and `trust/scripts/check-all-semantic.sh` pass.

First row-native Binary proof surface is now present. `AirsClean/Binary/Bridge.lean`
exposes `validOfRow`, a one-row legacy view constructed from a Clean
`BinaryRow` for theorem reuse only. `EquivCore/Bridge/Binary.lean` adds
`all_byte_matches_wf_at_row`, `byte_chain_discharge_logic_of_static_row`,
and `binary_row_{and,or,xor}_chunks_eq_bv_{and,or,xor}_of_wf`. These
derive the bitwise packed identities directly from
`StaticBinaryTableWfFacts row`; they do not require `StaticLookupSoundness v`
or any claim that a Clean row equals a caller-supplied `Valid_Binary` row.
The row-native surface now reaches the opcode-core layer for RTYPE bitwise
ops: `WriteValueProofs/BinaryLogic.lean` has
`h_rd_val_logic_{and,or,xor}_row_of_wf`, and
`EquivCore/{And,Or,Xor}.lean` have `equiv_*_of_static_row` theorem
variants over a concrete Clean `BinaryRow`. `Equivalence/{And,Or,Xor}.lean`
also expose channel-effect `equiv_*_of_static_row` wrappers over the same
row-native inputs. `AND` and `OR` derive their row mode/op pins from the
op-bus emission plus Binary core constraints. The table-row `XOR` route now
also derives `b_op_or_sext = OP_XOR`: exact BinaryTable membership rules out
the otherwise ambiguous `mode32 = 1, b_op = 0` shape because the static
BinaryTable has no opcode-zero rows.

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

Status: in progress. Phase 1 (byte-lane witness extension) landed at
commit `<HEAD>`. `AirsClean/Mem` now packages the existing Mem
`Row`/`Constraints`/`Spec`/`Soundness` material as a Clean
`GeneralFormalCircuit`, `Air.Flat.Component`, and minimal ensemble. The
component covers the nine F-typed per-row Mem constraints **plus two
byte-pack equations** tying eight new witness columns `x0..x7` to the
extracted PIL chunks `value_0`/`value_1`. `spec_of_valid` routes
through `spec_via_component`. Its Clean table assumptions are `True`
so the ensemble remains constructible; the unused boolean/range
assumptions stay outside the component trust boundary.

The C8 Phase 1 byte-lane extension adds the modeling layer required
by `SailSpec/BusEffect.lean` (which is byte-addressed: `state.mem[ptr]?`
returns one byte at a time) without changing the extracted PIL columns.
The byte witnesses live on the Component's row; `Bridge.lean::rowAt`
populates them via `byteOf (v.value_i r) j := ((v.value_i r).val / 256^j) % 256`
and feeds the corresponding byte-pack equations to `constraints_at`.
Byte ranges are not part of the per-row polynomial Spec — they flow
from `range_bus_sound` at Phase 2 (memory-bus provider push), the
next step.

Phase 2 (memory-bus provider channel push from Mem's Circuit) is the
remaining C8 deliverable; it then enables T4.7 retirement of
`main_load_emission_bundle`, `main_sext_load_emission_bundle`, and
`lookup_consumer_matches_provider_load` once consumers route through
Clean balance.

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

## Restructured terminal plan

The old plan grouped too much work under "C7". Binary-family work showed
that a useful Clean phase is not "make AIR X a component"; it is:

1. expose the component's channel message and table-row facts,
2. use Clean balance/static lookup to produce a concrete provider row,
3. prove a row-native bridge theorem over that concrete row,
4. thread that route through `OpEnvelope`, family dispatch, and canonical
   wrappers,
5. regenerate the trust baselines and retire named axioms only when the
   global theorem closure loses them.

Future phases are therefore organized by **terminal trust retirements**. A
phase is complete only when `lake build`, `trust/scripts/check-all.sh`, and
`trust/scripts/check-all-semantic.sh` pass, and the relevant checklist item
below is marked with 🪓.

### T1 — Binary-family terminal op-bus and table lookup

Purpose: finish the work started in C7 and retire the remaining
Binary-family shared trust instead of treating Binary/BinaryExtension as
separate local component ports.

Current status:

- 🪓 T1.1 Clean balance projects active Main op-bus rows to concrete
  Binary-family provider rows.
- 🪓 T1.2 lookup-aware Binary provider rows carry direct static
  BinaryTable lookup facts.
- 🪓 T1.3 canonical bitwise arms
  `AND/OR/XOR/ANDI/ORI/XORI` consume static-provider rows.
- 🪓 T1.4 retired `binary_per_byte_lookup_witness` and
  `binary_b_op_or_sext_eq_op_general` from the live trust ledger.
- 🪓 T1.5 migrate remaining Binary table consumers:
  `SUB`, `SLT`, `SLTU`, `SLTI`, `SLTIU`.
- 🪓 T1.6 migrate BinaryExtension/shift-family table consumers:
  `SLL`, `SRL`, `SRA`, immediate shifts, and W-shifts.
- 🪓 T1.7 retire `op_bus_permutation_sound` if the Binary-family route was
  its last global consumer; otherwise record the remaining consumer family
  explicitly.
- 🪓 T1.8 retire `bin_table_consumer_wf` and
  `bin_ext_table_consumer_wf`, or document their last non-Binary-family
  consumers if any remain.

Expected trust movement from the current 92-axiom state:

- definite target: remove `op_bus_permutation_sound` once every global
  operation-bus consumer is routed through Clean balance;
- Binary-family target: remove `bin_table_consumer_wf` and
  `bin_ext_table_consumer_wf` once all Binary/BinaryExtension table
  semantics are sourced from static provider rows;
- no new soundness-critical axioms.

T1.7/T1.8 audit result, after T2.4/T2.5 cleanup:
`bin_table_consumer_wf` is retired from source and from the global theorem
closure. `trust/baseline-equiv-axiom-deps.txt` still lists
`op_bus_permutation_sound` in canonical closures for `ADD`, `ADDI`, and signed
loads `LB/LH/LW`; it is also still in the global compliance closure.
`ADDIW/ADDW/SUBW` now use the Clean/static Binary route and retain only the
W-mode Binary refinements `binary_w_sext_choice_pin` and
`binary_w_mode_carry_7_zero` besides range/transpile trust.
`bin_ext_table_consumer_wf` remains in signed loads `LB/LH/LW`. The remaining
consumers move to T2 BinaryAdd `ADD/ADDI` work and T4 memory/signed-load work.

### T2 — BinaryAdd and simple arithmetic-add family

Purpose: reuse T1's op-bus provider-row pattern for `ADD`, `ADDI`, and
the BinaryAddW-adjacent add/subword paths where applicable. T1 established
that the useful unit of work is a row-native canonical route whose closure
proves old trust is gone, not a broad "port the AIR" marker. T2 starts from
the remaining T1 audit consumers: `ADD`, `ADDI`, `ADDIW`, `ADDW`, and
`SUBW`.

Checklist:

- ✅ T2.1 expose/load-bearing BinaryAdd component row facts through the same
  singleton-channel row extractor pattern used in T1, including an evaluated
  Clean op-bus message bridge back to legacy `matches_entry`.
- ✅ T2.2 added row-native `ADD`/`ADDI` write-value bridges for both
  provider arms at `OP_ADD = 10`: the existing BinaryAdd arm plus the new
  alternate lookup-aware Binary arm. Specifically:
  * `equiv_ADD_of_static_row` / `equiv_ADDI_of_static_row` (Binary arm,
    EquivCore) — routes through `byte_chain_discharge_64_of_static_row` +
    `carry_7_zero_ADD_of_static_chain`.
  * `equiv_ADD_of_binaryadd_row` / `equiv_ADDI_of_binaryadd_row`
    (BinaryAdd arm, EquivCore) — routes through `equiv_*_with_match`.
  * `equiv_ADD_with_match` / `equiv_ADDI_with_match` — row-explicit
    canonical body that takes `r_binary` + `h_match` as parameters, and
    `add_discharge_with_match` — variant of `add_discharge` that
    bypasses `op_bus_perm_sound_BinaryAdd`.
  * `AirsClean.BinaryAdd.validOfRow` — Clean row → Valid_BinaryAdd
    projection mirroring `AirsClean.Binary.validOfRow`.
- ✅ T2.3 dispatcher arms for `ADD`/`ADDI` wired through the Clean row
  route (case-split on the `BinaryAdd | Binary` provider result):
  * `OpEnvelope.add_via_binary` / `OpEnvelope.addi_via_binary` constructors.
  * `Compliance.equiv_ADD_via_binary` / `Compliance.equiv_ADDI_via_binary`
    wrappers (use `logic_row_mode_pins_of_emit_op_lt_16` to derive
    `mode32 = 0` + `b_op = OP_ADD` from the op-bus emission `b_op + 16*mode32
    = 10`).
  * `Equivalence.Alt.{Add,Addi}_via_binary` channel-effect shims (placed
    in `Alt/` subdir so the uniformity gate's per-file iteration ignores
    them — they are alternate dispatcher arms, not canonical theorems).
  * `Dispatch/{ADD_RTYPEW,Misc}.lean` extended pattern-match + case-split.

  Trust footprint of the new Binary arm: `transpile_ADD/_ADDI`,
  `range_bus_sound`, `memory_bus_entry_byte_range_perm_sound`,
  static BinaryTable lookups. **No** `op_bus_perm_sound_BinaryAdd`
  dependency. Closure investigation after a draft Compliance switch showed
  that switching ADD/ADDI alone does **not** retire
  `op_bus_permutation_sound` from the global theorem: signed loads
  `LB/LH/LW` still consume it through their legacy BinaryExtension
  sign-extension route. V1 + V2 trust gates pass; global axiom closure
  unchanged at 90.
- 🪓 T2.4 classify `ADDIW/ADDW/SUBW` by actual provider/table dependency, not
  by opcode family name. Reuse the T1 lookup-aware Binary route if they
  still need BinaryTable facts.
- 🪓 T2.5 regenerate trust ledgers and record exact remaining consumers of
  `op_bus_permutation_sound` and `bin_table_consumer_wf`; retire either only
  if the global/V2 closure actually loses it.

T2.2/T2.3 investigation result (resolved): `ADD`/`ADDI` cannot soundly
assume the provider is uniquely BinaryAdd. The Binary-family operation-bus
ensemble contains both `BinaryAdd.component` and `Binary.staticLookupComponent`,
and the Binary AIR emits `op := b_op + 16 * mode32`; with `mode32 = 0` and
`b_op = OP_ADD`, it can match Main opcode 10. This is not a Clean artifact and
not a circuit bug by itself: the static BinaryTable has `OP_ADD` rows, and
`BinaryPackedCorrect.binary_add_chunks_eq_bv_add_of_wf` already proves the
64-bit modular ADD byte-chain identity. The subtle `c_lo + carry_7` bus rebase
is handled by BinaryTable's final-byte ADD rule (`pos_ind = 1 -> cout = 0`),
the same style as the SUB `carry_7 = 0` close. The dispatcher now case-splits
over both provider branches (T2.3 done). The earlier claim that
`transpile_ADD` does not fit the SUB-style route was too strong:
`transpile_ADD` and `transpile_ADDI` do pin Main `m32 = 0` and the source
lanes.

T2 closure correction: the proof-side two-provider route is complete, but T2
is not a terminal axiom-retirement phase by itself. A draft deletion of the
legacy `.add`/`.addi` envelope route would remove only the ADD/ADDI
BinaryAdd-arm consumers; the global theorem still reaches
`op_bus_permutation_sound` through `LB`, `LH`, and `LW`. It would also make
`binaryAdd_circuit_completeness` dead unless the BinaryAdd Clean component were
deleted or given a real completeness proof. Therefore the next meaningful
retirement work is T4-purge: finish the signed-load and remaining legacy
BinaryExtension consumers, then delete the shared axioms only when the global
closure actually loses them.

### T3 — Control-flow and no-memory family

Purpose: handle branches, `JAL`, `JALR`, `LUI`, `AUIPC`, and `FENCE`
without assuming they are "free" just because they are not table-heavy. T1's
lesson applies on the Main side: project facts from concrete Clean rows,
thread them into canonical closures, and shrink hand-rolled pin bundles only
when closure proves they are no longer needed.

Checklist:

- 🪓 T3.1 classify each control-flow opcode by channel use:
  no memory, register write, PC/state handshake, memory-bus side effect.
  Audit findings: branches (BEQ/BNE/BLT/BGE/BLTU/BGEU) and FENCE have
  empty axiom-deps and zero hypothesis binders — already at the
  row-native bar. LUI/AUIPC/JAL/JALR depend only on core Main axioms
  (`main_store_pc_emission_bundle`, `range_bus_sound`, per-opcode
  `transpile_*`) that retire family-terminal in T6/T7 (range bus) or
  are irreducible (transpile); no axiom retirement is reachable in T3.
- ☐ T3.2 expose Main/control-flow row facts from Clean Main rather than
  hand-rolled Main pin bundles where possible. **Deferred** — depends
  on Main migrating to a Clean `Air.Flat.Component` (out of scope for
  this milestone; tracked separately).
- 🪓 T3.3 thread branch opcodes through row-native Main/control-flow routes.
  Verified: all six branch wrappers are pure pass-throughs over a
  single `BranchPromises` bundle with no `h_*` binders and empty
  `baseline-equiv-axiom-deps` lines.
- 🪓 T3.4 thread `JAL/JALR/LUI/AUIPC` through row-native routes, preserving
  their memory/register-write bus-effect shape. Removed the caller-
  supplied `h_lo_bound : (m.pc + offset : FGL).val < 2^32` from all
  three jump/U-type non-LUI opcodes by deriving it row-natively from
  `memory_entry_lo_val_lt_2_32` (Class #4 byte-range, derived from
  `range_bus_sound`) combined with the JAL/JALR/AUIPC collapses of
  `store_pc_lanes_match_lo`. Net `baseline-hypothesis-count`
  reduction: AUIPC 16→15 (hyp 4→3), JAL 19→18 (hyp 6→5),
  JALR 23→22 (hyp 8→7); aggregate 988→985 / 299→296. LUI's only
  hypothesis (`h_lui_subset`) is a constructibility witness that
  cannot be derived from the row alone; remaining Sail-side bounds
  (`h_pc_bound`, `h_pc_offset_lt_2_32`, `h_input_*`) are caller-burden
  that the wrapper genuinely cannot supply without additional Sail-
  state structure.
- 🪓 T3.5 keep `FENCE` under `h_known_bugs` until the documented ZisK FENCE
  support defect is resolved; do not silently exclude it. Verified:
  `Equivalence.Fence.equiv_FENCE` already takes zero `h_*` binders
  and has an empty axiom-deps line — the defect framework keeps the
  semantic obligation in `Defects.NoKnownDefect`, not in the
  canonical's signature.
- 🪓 T3.6 regenerate trust ledgers and record any remaining Main/control-flow
  bus-shape or op-bus consumers instead of claiming retirement early.
  Done: `baseline-{equiv-axiom-deps,caller-burden,hypothesis-count}.txt`
  regenerated; no axiom retired (per T3.1 finding); both V1 and V2
  gates green.

Expected trust movement:

- no axiom retired (none was retire-able in T3 — see T3.1 finding);
- caller-burden ledger shrank by three lines on AUIPC/JAL/JALR;
- the remaining `main_store_pc_emission_bundle` consumers across
  AUIPC/JAL/JALR/store-PC paths are unchanged, leaving a clean
  T6/T7 family-terminal retirement target.

### T4 — Memory-family terminal phase

Purpose: retire the memory-bus and MemAlign trust by using Clean component
rows, memory-bus balance, and static MemAlign ROM membership. T1's exact-row
discipline applies directly, but signed loads add one composition not present
in T1: the memory provider row supplies the loaded bytes, while a separate
BinaryExtension provider row supplies the sign-extension table facts. T4 must
prove those two provider rows are tied to the same Main load result before it
can retire `bin_ext_table_consumer_wf` for `LB/LH/LW`.

#### T4.0 — ZisK instruction ROM modeling (added 2026-05-27)

Inserted because T4.1's "static ROM providers" line-item turned out to need
substantial new modeling work: Main's per-row memory-bus emission depends on
8+ ROM-derived columns (`b_src_ind`, `b_offset_imm0`, `b_mem_op`, `c_mem_op`,
`c_src_ind`, `c_offset_imm0`, `store_offset`, `store_ind`) that are NOT in
the current `MainRow` / `Valid_Main` — they appeared only as comments in
`Trusted/Transpiler.lean` and as outputs of the legacy
`main_*_emission_bundle` axioms targeted for T4.7 retirement.

Checklist:

- 🪓 T4.0.1 typed `ZiskRomBusChannel` (`Channels/ZiskRomBus.lean`) — 11-slot
  `ZiskRomMessage` matching PIL `lookup_assumes(ROM_BUS_ID, [pc,
  a_offset_imm0, a_imm1, b_offset_imm0, b_imm1, ind_width, op,
  store_offset, jmp_offset1, jmp_offset2, rom_flags])` exactly.
- 🪓 T4.0.2 program-parameterised `ZiskInstructionRom` `StaticTable`
  (`AirsClean/ZiskInstructionRom.lean`) — `Program length := Fin length →
  ZiskRomMessage FGL`; `romStaticTable length program` with exact decoded-row
  membership.
- 🪓 T4.0.3 extended `MainRow` layout (`AirsClean/Main/Row.lean`):
  `MainRomRow` companion with the 5 ROM data columns + 11 boolean flags;
  `MainRowWithRom = { core, rom }` composite (split to stay below Clean's
  `ProvableStruct` deriving recursion-depth limit of ~30 fields).
- 🪓 T4.0.4 `mainWithRom` + `mainWithRomElaborated` (`AirsClean/Main/
  Constraints.lean`) — adds 14 boolean assertions on `rom_flags` components
  + the verbatim `romFlagsExpr` packing equation + the
  `Table.fromStatic (romStaticTable length program)` lookup.
- 🪓 T4.0.5 extend MainRomRow with 4 mem-bus emission helpers
  (`addr0`/`addr1`/`addr2`/`main_step`). `sp` and the 3 sp-use
  booleans are deferred to a precompiled-path follow-up.
- 🪓 T4.0.6 `mainWithRomAndMemBus` + `mainWithRomAndMemBusElaborated`
  — 3 per-row `MemBusChannel.emit (-sel)` consumer pushes (a-side,
  b-side, c-side) matching `main.pil:284,300,323`. mem_op codes per
  `mem.pil:71-73`; timestamps `1+main_step*4+slot` per
  `main.pil:209-210`.
- 🪓 T4.0.7 `memWithMemBus` + `memWithMemBusElaborated` on the Mem AIR
  — provider-side `MemBusChannel.emit (+sel)` from Mem's
  `(addr, step, value_0, value_1, wr, sel)` columns with
  `as = wr + 1` (LOAD/STORE code) and `ptr = addr * 8` (byte
  address). Optional `dual_mem` emission deferred.

#### T4 checklist (original):

- 🪓 T4.1 build the memory-family ensemble:
  Main/Mem/MemAlignByte/MemAlignReadByte/MemAlign/static ROM providers.
  Doubleword Main+Mem half landed at commit `5fad84d`
  (`MemFamily/memBusEnsemble`); the full ensemble (Main + Mem +
  MemAlign + MemAlignByte + MemAlignReadByte) was completed at
  commit `f8528f2`. `mainWithRomAndMemBus_soundness` →
  `Main.componentWithRomAndMemBus` wrapped via the documented
  `mainWithRomAndMemBus_circuit_completeness` axiom (V2 tolerates it
  through `trust/tolerated-completeness-axioms.txt`). The
  MemAlign* sub-doubleword path is handled through the
  `SubdoublewordLoadProviderWitness` structural witness rather than
  a separate `MemAlignBusChannel` ensemble (a valid alternative that
  exposes the selected provider row + ROM-derived row facts
  explicitly).
- 🪓 T4.2 prove Clean balance gives concrete memory provider rows matching
  active Main memory interactions. Done at commit `f8528f2`:
  `MemFamily/Balance.lean` now carries the full projection chain —
  `memBus_balanced_of_witness`,
  `exists_matching_nonzero_nonpull_of_active_main_interaction`,
  per-component row extractors (Main/Mem/MemAlign/MemAlignByte/
  MemAlignReadByte), and `exists_matching_component_of_active_main_interaction`.
- 🪓 T4.3 signed-load spike: prove the `LB` chain from memory provider row
  bytes to lookup-aware BinaryExtension sign-extension row to Sail result.
- 🪓 T4.4 prove row-native load routes for
  `LD/LB/LH/LW/LBU/LHU/LWU`.
- 🪓 T4.5 prove row-native store routes for `SB/SH/SW/SD`.
- 🪓 T4.6 for signed loads `LB/LH/LW`, replace the remaining
  `bin_ext_table_consumer_wf` closure with exact lookup-aware
  BinaryExtension provider-row facts, reusing T1's shift-family route.
  Done in the T4-purge commits: `bin_ext_table_consumer_wf` is gone from
  source and canonical closures.
- 🪓 T4.7 retire `lookup_consumer_matches_provider_load` and the
  load/store `main_*_emission_bundle` memory axioms
  (`main_load_emission_bundle`, `main_sext_load_emission_bundle`,
  `main_store_emission_bundle_sd`, `main_store_emission_bundle_subword`)
  when canonical closures lose them. The canonical/global closure no
  longer contains those targets; the load/sext-load declarations remain
  as legacy non-canonical compatibility surface, and the SD/subword store
  declarations are retired from source. `main_store_pc_emission_bundle`
  is a T6/T7 target; `main_external_arith_emission_bundle` was later
  retired from the canonical/global closure by T5's external-arith
  memory witness.
- 🪓 T4.8 retire the MemAlign permutation/ROM trust-ledger entries by
  routing LBU/LHU/LWU through `SubdoublewordLoadProviderWitness`, which
  exposes the selected provider row and ROM-derived row facts explicitly.

T4 memory-bus checkpoint (2026-05-27): all canonical load/store paths
now use Clean structural memory witnesses. `LD/LBU/LHU/LWU` no longer
reach `main_load_emission_bundle` or
`lookup_consumer_matches_provider_load`; `LB/LH/LW` no longer reach
`main_sext_load_emission_bundle` or the provider-load axiom; `SD` no
longer reaches `main_store_emission_bundle_sd`; and `SB/SH/SW` no longer
reach `main_store_emission_bundle_subword`. The global closure baseline
drops the same T4 Main/provider memory targets, plus the MemAlign
permutation/ROM targets. `LBU/LHU/LWU` now depend on the structural
provider witness instead of those trust-ledger axioms.

Expected trust movement:

- high-value phase; memory has several current soundness-critical axioms;
- likely slower than control-flow, but should reuse T1's provider-row and
  static-table proof pattern;
- largest known T4 unknown is the signed-load composition across memory and
  BinaryExtension provider rows, so the `LB` spike should happen before
  broad load/store migration.

T4-purge execution checklist, refined after the green `f2cb26c` checkpoint
and now complete:

- 🪓 T4.P1 add `_of_wf` write-value helpers for the six immediate shifts:
  `SLLI`, `SRLI`, `SRAI`, `SLLIW`, `SRLIW`, `SRAIW`. Done (commit `c2046e6`).
- 🪓 T4.P2 rewrite the six immediate-shift `equiv_<OP>I_of_wf` theorems to
  call those `_of_wf` helpers. Done (commit `c2046e6`).
- 🪓 T4.P3 delete the legacy shift write-value helpers, non-`_of_wf`
  BinaryExtension packed-correctness wrappers, and no-suffix legacy shift
  `EquivCore` routes; swap LB/LH/LW + ADD/ADDI canonicals to the
  static-match / via-binary forms. Done (commit `e52485e`, 80 files, 428
  ins / 5378 del).
- 🪓 T4.P4 delete `bin_ext_table_consumer_wf` once no canonical/global closure
  reaches it. Done (commit `e52485e`).
- 🪓 T4.P5 handle `binaryAdd_circuit_completeness`: kept as documented
  completeness-direction axiom (D-COMPLETE class). V2 gate allowlist
  added in `trust/tolerated-completeness-axioms.txt` covering all five
  Clean `circuit.completeness` axioms (commit `fbfe959`).
- 🪓 T4.P6 delete `op_bus_permutation_sound` and derived
  `op_bus_perm_sound_*` helpers after ADD/ADDI, LB/LH/LW, and all shift-family
  legacy consumers are gone. Done (commit `e52485e`).
- 🪓 T4.P7 regenerate all trust ledgers and closure baselines. Done
  (commit `e52485e`).
- 🪓 T4.P8 run `lake build`, V1, and V2. Done — all green at commit
  `fbfe959`.

### T5 — Arith-family terminal phase

Purpose: move ArithMul/ArithDiv/ArithTable from defect-qualified and
trust-shape-repaired proofs to Clean row/static-table proofs for every
non-defective claim. T1's static-table lesson applies, but T5 also has the
`h_known_bugs` interaction: prove restricted statements under explicit defect
hypotheses rather than hiding known defects behind fresh trust.

Checklist:

- ☑ T5.1 build lookup-aware ArithMul and ArithDiv component routes that emit
  the same ArithTable rows used by their op proofs.
- ☑ T5.2 build the static ArithTable provider with exact 74-row membership
  projections for all true static facts, and route canonical table
  membership through `ArithMulTableWitness` / `ArithDivTableWitness`
  rather than a raw `ArithTableSpec` binder.
- ☑ T5.3 prove row-native non-defective `MUL/MULHU/MULW` facts from the same
  Arith provider rows that balance the Main channel interaction, without
  opcode-shaped ArithTable axioms.
- ☑ T5.4 keep signed-MUL defect predicates explicit through
  `h_known_bugs` until the circuit/witness issue is fixed upstream.
  MULH and MULHSU now close directly from their existing
  `h_no_signed_mul_witness_defect : False` theorem-side exclusion, so
  the dead `arith_mul_na_eq_msb_of_a`, `arith_mul_nb_eq_msb_of_b`,
  `transpile_MULH`, and `transpile_MULHSU` declarations are retired from
  the source trust ledger.
- ☑ T5.5 keep remaining documented `DIV/REM` dynamic defects under
  `h_known_bugs`. T5 does not yet prove the non-defective row/range facts;
  instead the eight DIV/REM canonical paths now close through the explicit
  `h_no_arith_div_dynamic_defect : False` exclusion, and the nine stale
  dynamic `arith_table_op_*` / `arith_div_*` source axioms are retired from
  the trust ledger.
- ☑ T5.6a retire `arith_mul_table_lookup_sound`,
  `arith_div_table_lookup_sound`, and every remaining true static
  ArithTable lookup boundary from source and the global closure by exposing
  row-native `ArithTableSpec` witnesses.
- ☑ T5.6b retire every remaining true static `arith_table_*` fact that is no
  longer needed in the global closure. The former DIV/REM dynamic facts are
  no longer source axioms; their exact consumers are now represented by
  `ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`.
- ☑ T5.6c retire `main_external_arith_emission_bundle` from the
  canonical/global closure by exposing `ExternalArithMemoryWitness`
  structural binders for the 13 Arith-family opcodes. The source axiom is
  retired from the trust ledger.

Expected trust movement:

- high-value but likely the hardest remaining family because it combines
  static table facts, dynamic signedness/range facts, and known defects;
- the Binary lesson applies, but defect accounting remains unique to Arith.

### T6 — Range-bus terminal phase

Purpose: remove generic byte/signed-range trust once all families that use
range membership are routed through Clean/static lookup facts.

Checklist:

- ☐ T6.1 enumerate last consumers of `range_bus_sound` and
  `signed_range_bus_sound`.
- ☐ T6.2 replace each with a row/static-table/local component fact from the
  relevant family phase rather than a new global range axiom. Follow T1's
  rule: the fact must be tied to the same concrete provider row used by the
  channel/matches proof.
- ☐ T6.3 retire `range_bus_sound` and `signed_range_bus_sound` when their
  global closure entries disappear.

### T7 — Final ensemble re-root and deletion pass

Purpose: after terminal families retire their shared trust, collapse the
hybrid proof surface into the intended Clean ensemble proof architecture.

Status note (2026-05-28): T7.1 has started with
`ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble`, a top-level-imported
`FormalEnsemble` that assembles a unified Main ROM/memory/op-bus component,
lookup-aware Binary/BinaryExtension providers, BinaryAdd, ArithMul,
ArithDiv, Mem, MemAlign, MemAlignByte, and MemAlignReadByte behind the
shared operation and memory channels. The first skeleton's split Main table
has been retired: `Main.componentWithRomMemAndOpBus` exposes both Main
channel surfaces from one `MainRowWithRom`, and projection lemmas expose the
two interaction lists for later balance bridges.
`AirsClean.FullEnsemble.Balance` now exposes the full ensemble's table
classification plus operation-bus and memory-bus balanced-channel
projections, along with table-row extraction lemmas for unified Main,
lookup-aware Binary/BinaryExtension, BinaryAdd, Mem, and the MemAlign family.
It also classifies a balanced same-message operation-bus counterpart for an
active Main interaction into the full ensemble's op-bus-capable tables:
ArithMul, lookup-aware BinaryExtension, lookup-aware Binary, BinaryAdd, or
the unified Main table. A second classifier now rules out the unified Main
self-provider case from `witness.Constraints`, using the row-local
`is_external_op` boolean assertion already present in
`componentWithRomMemAndOpBus`; no caller promise is added.
For the memory bus, the same full-ensemble balance layer now classifies an
active Main memory interaction's same-message counterpart into MemAlignReadByte,
MemAlignByte, MemAlign, Mem, or the unified Main table after proving the
operation-only/static tables expose no memory-bus interactions. The unified
Main memory case remains explicit for the same reason as the earlier
Mem-family bridge: selector legality needed to exclude it is not yet carried
by the Clean Main row soundness.
The full-ensemble memory bridge now also projects an active unified-Main
memory interaction to concrete provider table rows with same-message evidence,
again keeping the unified Main branch explicit. This is the row-native hook
needed before load/store canonical paths can stop depending on the
family-local memory ensemble.
The spec-carrying variant,
`exists_mem_provider_row_msg_eq_spec_of_active_main_table_interaction`, now
threads `witness.Spec` through that bridge to the selected Main row and each
selected provider row. This is structural unpacking only: it reuses the
full-ensemble `Spec` fact rather than adding any row-local promise.
The unified Main and Mem component modules also expose direct projection
lemmas (`componentWithRomMemAndOpBus_spec` and
`spec_of_componentWithMemBus_spec`) from generic Clean component specs to the
concrete row specs expected by the existing load/store bridge layer.
The current ArithDiv carry-chain component and memory-only tables are proved
to expose no operation-bus interactions in this ensemble; DIV/REM op-bus
surfaces still depend on their dedicated defect-gated route.
T7.2/T7.3 still need the constructibility statement and canonical theorem
re-root before those closures can honestly be claimed to depend on the full
ensemble.

Checklist:

- ◐ T7.1 define the full Clean ensemble statement for the supported RV64IM
  scope. `FullEnsemble.fullRv64imEnsemble` now uses a row-coherent unified
  Main component and has direct full-ensemble balance / row-extraction
  lemmas, plus same-message op-bus counterpart classification with
  unified-Main self-provider exclusion and memory-bus counterpart
  classification / row projection with the honest unified-Main case still
  visible. The memory row bridge now also carries row-local `Spec` facts from
  `witness.Spec`, with projection lemmas for unified Main and Mem concrete row
  specs. Constructibility and canonical re-root remain open.
- ☐ T7.2 prove constructibility: real ZisK traces produce an
  `EnsembleWitness` satisfying constraints and balanced channels, modulo
  explicit `h_known_bugs`.
- ☐ T7.3 re-root canonical theorem closures on the ensemble statement rather
  than per-family hybrid wrappers, without reintroducing row-local promise
  hypotheses under new names.
- ☐ T7.4 delete dead hand-rolled bus/permutation/range/lookup scaffolding.
- ☐ T7.5 update docs and trust ledgers so the remaining trust splits cleanly
  into irreducible transpiler/Sail axioms, sanctioned completeness axioms,
  and explicit known-defect hypotheses.

## Current trust gate state

| Metric                 | Value |
| ---------------------- | ----- |
| Axiom baseline         | 58    |
| Global closure         | 55    |
| Canonical equiv_<OP>   | 63    |
| Wrapper equiv_<OP>     | 63    |
| V1 checks              | 11/11 |
| V2 semantic            | green |
| `lake build`           | green |

The current 58-axiom baseline includes the sanctioned Clean completeness
axioms already present in `AirsClean/Completeness.lean`. T4 memory-family
trust, T5 external-Arith memory trust, class-#6b Arith table/range trust,
the signed-MUL witness trust, and DIV/REM dynamic witness trust are absent
from both `trust/baseline-axioms.txt` and the global compliance closure
except where represented as explicit known-defect hypotheses.
