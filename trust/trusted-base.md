# Trusted Base

This is the narrative source of truth for zisk-fv's current trust boundary.
The generated machine ledgers live under [`generated/`](generated/).

## Claim

The intended soundness claim is:

> Assuming the Sail-to-Lean extraction and ZisK RV64IM circuit-to-Lean
> extraction are trusted, every state transition accepted by the modeled ZisK
> RV64IM circuits is a valid RISC-V state transition.

The global Lean theorem is:

```text
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

Current generated counts:

| Surface                                                                | Count | Ledger                                                                                       |
| ---                                                                    | ---:  | ---                                                                                          |
| Source Lean trust declarations                                         | 0     | [`generated/baseline-axioms.txt`](generated/baseline-axioms.txt)                             |
| Transitive project-axiom closure of `zisk_riscv_compliant_program_bus` | 0     | [`generated/baseline-zisk-riscv-compliant.txt`](generated/baseline-zisk-riscv-compliant.txt) |

The source trust ledger currently contains no project axioms. The global theorem
also has no transitive project-axiom closure. The former Aeneas row-lowering and
memory-state load bridge axioms are now visible conditional inputs:
`env.aeneasBridgeTrust` and `env.memoryTimelineEvidence` on the global theorem.

The extraction assumptions are part of the project premise but outside the
Lean axiom ledger:

- Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
- ZisK RV64IM circuit-to-Lean extraction from flake-pinned ZisK/PIL inputs.

## Current Classes

| Class                         | Declarations | In global closure | Removability                                                                                             |
| ---                           | ---:         | ---:              | ---                                                                                                      |
| Aeneas row-lowering condition | 0            | 0                 | Discharge `env.aeneasBridgeTrust` by importing generated Aeneas Lean into main Lake.                      |
| Sail memory timeline          | 0            | 0                 | Load arm reduced to the memory-only `RowTraceCoherence` trace-coherence floor (#76 Fold-B; see below). Discharge by the #100 whole-execution memory replay/timeline induction. |
| Clean completeness            | 0            | 0                 | Retired from source trust; false/circular fields are visible non-claims.                                  |


## Retired Row-Shape Bridge

The former RV64-to-ZisK hand-written row-shape axiom surface has been removed from the
active Lean trust ledger. The live opcode literals, lane helpers,
register-pointer decoding helper, and row/state helper structures live in
`ZiskFv/RowShape/Contract.lean`.

Canonical per-opcode theorem closures no longer mention any retired
row-shape bridge names. The route obligations that used to be hidden behind
that contract are now explicit caller/envelope facts or are derived from row
provenance and provider rows: static mode/control pins from provenance,
runtime source/data lanes from caller facts, and jump/PC facts from explicit
route obligations.

## Aeneas Row-Lowering Bridge

The production-backed Aeneas extraction is checked by the repository test path.
As of eth-act/zisk-fv#111 (PR #160), the generated Aeneas Lean **is** imported
into the main Lake proof (`ZiskFv.lean` → `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/`),
and the per-opcode **static** decode/row-mode pins (`op` / `is_external_op` /
`m32` / `set_pc` / `store_pc`) are proven in-build, kernel-soundly (axioms
`{propext, Classical.choice, Quot.sound}`, no `native_decide`), from the real
lowerer (`trust/aeneas/ProductionM2.lean`). Those proven pins are **standalone**:
they are not yet wired to discharge `h_bridge`. Doing so requires binding the
committed circuit row to the lowering of the committed program word
(RomImageBinding, eth-act/zisk-fv#159) plus the dynamic per-arm conjuncts
(immediates / lanes / byte-chains). The generated Aeneas Lean still does not yet
derive every row-provenance, source-lane, immediate, PC, and link bridge fact
consumed by the compliance wrappers, so until that wiring lands the gap is still
represented by a visible global theorem hypothesis:

```text
h_bridge : env.aeneasBridgeTrust
```

The existing wrapper and `OpEnvelope` signatures still expose those fields
because the dispatch proofs pass them to the current wrapper layer. The wrapper
and canonical theorem signatures themselves are the inventory for the later
refactor that removes those parameters after generated Aeneas Lean supplies
proofs inside Lake (the generated caller-burden ledgers that previously tracked
this were retired with the anti-laundering metric — see "Active Caller Burden").

First proof-slice progress: the staged Aeneas harness now checks that
`extract_lui_from_inst` computes the LUI row-shape constants needed for
`MainRowProvenance.LuiRowMode`, and main Lake contains
`MainRowProvenance.luiRowMode_of_extracted_shape`, which states that those
constants discharge the `OpEnvelope.lui` row-mode field. Main Lake also
contains `OpEnvelope.luiOfExtractedShape` and
`OpEnvelope.aeneasBridgeTrust_luiOfExtractedShape`, which construct the LUI
envelope with the derived row-mode field and prove the LUI branch of this
bridge predicate. Generated Aeneas Lean remains staged under `build/`, so this
does not eliminate the remaining caller-burden bridge fields.

Second proof-slice progress: the same row-mode pattern now covers AUIPC. The
staged Aeneas harness checks the `extract_auipc_from_inst` row-shape constants,
and main Lake contains `MainRowProvenance.auipcRowMode_of_extracted_shape`,
`OpEnvelope.auipcOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_auipcOfExtractedShape`.

Third proof-slice progress: the same row-mode pattern now covers the JAL
rd-write route. The staged Aeneas harness checks the `extract_jal_from_inst`
row-shape constants, and main Lake contains
`MainRowProvenance.jalRowMode_of_extracted_shape`,
`OpEnvelope.jalOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_jalOfExtractedShape`.

Fourth proof-slice progress: JALR now has the matching final-row control-pin
slice. The staged Aeneas harness checks the `extract_jalr_from_inst` external
`OP_AND` and control-pin constants, and main Lake contains
`MainRowProvenance.jalrPins_of_extracted_shape`,
`MainRowProvenance.jalrControl_of_extracted_shape`,
`OpEnvelope.jalrOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_jalrOfExtractedShape`.

Fifth proof-slice progress: FENCE now has the matching activation/opcode pin
slice. The staged Aeneas harness checks the `extract_fence_from_inst` internal
`OP_FLAG` constants, and main Lake contains
`MainRowProvenance.fencePins_of_extracted_shape`,
`OpEnvelope.fenceOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape`.

Sixth proof-slice progress: ADD, ADDI, and ADDW now cover the first Binary
provider-route pins. The staged Aeneas harness checks that regular ADD and ADDI
lower to external `OP_ADD` rows and ADDW lowers to an external `OP_ADD_W` row,
and main Lake contains `MainRowProvenance.addPins_of_extracted_shape`,
`MainRowProvenance.addwPins_of_extracted_shape`,
`OpEnvelope.addViaBinaryOfExtractedShape`,
`OpEnvelope.addiViaBinaryOfExtractedShape`,
`OpEnvelope.addwOfExtractedShape`, and the matching
`OpEnvelope.aeneasBridgeTrust_*OfExtractedShape` theorems. The provider-row
source-lane equalities are still explicit envelope fields.

Seventh proof-slice progress: SUB, SUBW, and ADDIW now cover the remaining
initial BinaryAdd/BinaryAddW provider-route shape. The staged Aeneas harness
checks the external `OP_SUB`, `OP_SUB_W`, and `OP_ADD_W` row-shape constants,
and main Lake contains `MainRowProvenance.subPins_of_extracted_shape`,
`MainRowProvenance.subwPins_of_extracted_shape`,
`OpEnvelope.subOfExtractedShape`, `OpEnvelope.subwOfExtractedShape`,
`OpEnvelope.addiwOfExtractedShape`, and the matching
`OpEnvelope.aeneasBridgeTrust_*OfExtractedShape` theorems.

Generated extraction and bridge manifest: the canonical production-backed
Aeneas extraction is tracked at
[`aeneas/ProductionM2.lean`](aeneas/ProductionM2.lean), and CI regenerates it
from the pinned inputs and fails on any non-zero diff. The maintained trust-gate
artifact [`aeneas-generated-bridge-manifest.txt`](aeneas-generated-bridge-manifest.txt)
is checked by `trust/scripts/check-aeneas-generated-bridge-manifest.sh` and by
`trust/scripts/check-all.sh`; it keeps the generated row-shape predicates and
Lean examples aligned with the generator template. Temporary generated LLBC and
harness modules such as `GeneratedChecks.lean` remain reproducible output under
`build/aeneas-production-extraction`.

Remaining path: export provider-row values, selected memory rows, and
full-ensemble same-message facts into the main proof boundary. Those artifacts
are needed to remove the remaining caller-burden bridge, row-shape, and
promise fields from wrapper and `OpEnvelope` boundaries. The `bus_shape`
category is already zero after the W-shift structural cleanup.

## Sail Memory Timeline

The former per-load byte-agreement promise has been replaced by a visible global
timeline-evidence hypothesis:

```text
h_memory_timeline : env.memoryTimelineEvidence
```

For load `OpEnvelope` arms, `env.memoryTimelineEvidence` requires
`Nonempty (MemoryTimelineEvidence state bus.e1)`; non-load arms require no
memory evidence. Generated full-witness sidecar artifacts can construct that
timeline evidence through `FullWitnessGeneratedTimelineEvidence`, while
dispatch consumes only the public `MemoryTimelineEvidence state e1` API before
reconstructing canonical `LoadPromises`. The `OpEnvelope` load constructors
themselves carry only `LoadStructuralPromises`, so they no longer accept a
per-load byte oracle.

`FullWitnessGeneratedTimelineEvidence` wraps `FullWitnessMemoryTimelineEvidence`
as a checked generated producer and makes the generated ProverData sidecar
source explicit: it carries
`FullWitnessMemAirSourceProverDataWitnessFacts` and records that the stored
sidecars are exactly the sidecars packaged from those witness facts. The inner
`FullWitnessMemoryTimelineEvidence` contains the concrete full-ensemble witness,
the `FullWitnessMemAirSourceRawSidecars` callback for the witness-selected
mutable Mem table, and only the residual Sail-memory timeline fact. A derived
Mem AIR source accessor selects the `FullWitnessMemReplayBridge`, which derives
the `AcceptedMemoryReplayEvidence` sub-object used by
`MemoryTimelineEvidence`, including prefix-read soundness for the accepted Mem
rows.

The accepted Mem table is sorted by address and step, not by execution time
(`zisk/state-machines/mem/pil/mem.pil` line 9: "Memory is sorted by address and
step"). The residual timeline boundary therefore does **not** claim whole Sail
state equality after replaying the accepted Mem-table prefix. It states only:
the accepted rows split around the selected read, the selected row is a read,
and the selected Sail state agrees with
`replayMemoryAfterBusRows acceptedReplay.initialMemory priorRows` on the
selected entry's eight byte lanes (`ReplayMemoryAgreementOnBytes ... entry.ptr.toNat`).
The canonical load proofs derive `LoadByteAgreement` from that byte-local
timeline evidence plus the circuit-side prefix-read agreement.

Generated/full-ensemble Mem facts target
`FullWitnessMemAirSourceProverDataWitnessFacts`: Clean assertion/lookup
witnesses plus named `witness.data` sidecar keys for raw split generated
constraints, row range facts, segment range facts, and the stage-2 source
columns for each mutable Mem table. The reproducible generated wrapper
`Extraction.MemGeneratedArtifact` exposes `buildWitnessFacts`, which assembles
that target from the three per-table callback families, plus
`buildRawFacts` and `buildWitnessFactsFromRawParts`, which assemble/adapt raw
ProverData fact callbacks to the same witness target. It also exposes
`buildTimelineEvidence`, which passes the assembled facts to
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`. The top-level
`nix run .#test` gate compiles the generated `Extraction.Circuit` shim,
`Extraction.Mem` constraint source, and
`Extraction.MemGeneratedArtifact` wrapper directly under the generated
`build/extraction` root. It also compiles
`Extraction.MemGeneratedConstraintBridge`, which binds those extracted Mem
constraints to the ProverData-backed source view used by the wrapper, so this
surface stays synchronized with the checked Lean API.
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts` packages that
target into a checked generated producer of the public timeline boundary. Lean
packages the resulting sidecar callback into the witness-selected
`FullWitnessMemAirSource` via
`fullWitnessMemAirSourceOfRawSidecars`, and
`fullWitnessMemoryTimelineEvidence_of_rawSidecars` combines it with only the
byte-local residual Sail timeline field above. `FullWitnessMemAirSourceRawFacts` and
`fullWitnessMemoryTimelineEvidence_of_rawFacts` remain compatibility adapters
for lower-level generated modules that still produce the raw sigma callback;
`fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts` is the checked
adapter for raw ProverData facts.

Retirement path: emit/prove the extractor/full-ensemble
`FullWitnessMemAirSourceProverDataWitnessFacts`, then prove the whole-execution
induction showing that, for each selected load, Sail memory at the selected
entry's eight bytes equals the last same-address accepted write in step order
(including the preload/first-read base case). The table/list-position part of
the bridge is named as `MemTableGeneratedRowsBridge`, which connects Clean
`table.table` positions to `rowAt mem idx` and the row-indexed
`generated_every_row` constraints. `FullWitnessMemReplayBridge` packages the
concrete full-ensemble Mem table, generated-row/range/fixed-column facts,
active-row equality, and nonempty segment evidence; its constructor derives the
accepted replay subobject, so `AcceptedMemoryReplayEvidence.prefixReadSound` is
no longer a bare global-boundary assumption. The semantic trust gate includes a
two-address witness with an addr-sorted/time-reversed prefix (write at byte
address 0 with later timestamp, selected read at byte address 8 with earlier
timestamp) so the old whole-state boundary shape cannot return silently.

### Trace-coherence floor (`RowTraceCoherence`) — #76 Fold-B load reduction

The load-arm memory residual of the global theorem
`zisk_riscv_compliant_program_bus` has been reduced from a **whole-`SailState`**
identity to a **memory-map-only** trace-coherence floor.

* **Before (retired):** `LoadMemoryTimelineConstructionEvidence` carried
  `MemoryPrefixStateAlignment initialState state priorRows`, i.e.
  `state = stateAfterMemoryBusRows initialState priorRows` — a closed-form
  identity that pins **every** field of the load Sail `state` (regs,
  choiceState, mem, tags, cycleCount, sailOutput) to a replay of the prefix.
  This def is kept in `ZiskFv/Compliance/OpEnvelope.lean` marked **RETIRED**
  for the audit diff only; nothing in the live closure references it.
* **After (live):** `LoadMemoryTimelineCoherenceEvidence` carries an opaque
  cursor-indexed state assignment `stateAt`, the segment seed
  `stateAt [] = initialState`, the load-state pin `stateAt priorRows = state`,
  and the chain
  `RowTraceCoherence stateAt [] priorRows`
  (`ZiskFv/ZiskCircuit/MemTimeline/Spike.lean`). Each `RowTraceCoherence`
  conjunct constrains **only the `.mem` field** at one consumed prefix row:
  the row's memory transition takes any replay map agreeing with the current
  cursor's Sail memory to one agreeing with the next cursor's Sail memory
  (stores via `writeMemoryOfEntry`; reads / inactive / non-memory rows leave
  it unchanged). `regs` / PC / `cycleCount` / `tags` / `sailOutput` are
  **free**.

**Trust class.** `RowTraceCoherence` is the *trace-coherence* premise — at each
consumed prefix row the Sail state at the next execution cursor is the memory
transition of the Sail state at the current cursor. `ProgramBinding.stateAt`
carries no field for it, so it stands as **external trust, the same class as
channel-balance**: a per-step chaining fact about the execution timeline that
the row-local equivalence layer does not establish. It is dischargeable in
principle by the #100 whole-trace / execution-bus induction (which proves the
Sail successor relation across the trace). It is **not** an axiom — it is a
named binder carried on the load `OpEnvelope` residual and the load
`RowData_<op>` of the strong export; the global theorem's closure contains **no
new `ZiskFv.*` axiom** (kernel axioms only).

**What is DERIVED, not assumed.** The byte-local agreement the load consumer
actually needs — `stateBytesAtPrefix` of `MemoryTimelineEvidence`, i.e.
`ReplayMemoryAgreementOnBytes state (replayMemoryAfterBusRows … priorRows)
entry.ptr.toNat` — is **folded out** of the per-store steps via the store-driven
Fold-B (`replayAgreement_of_rowTraceCoherence` →
`stateBytesAtPrefix_of_rowTraceCoherence`), combined with the circuit-side
`prefixReadSound` (`memoryTraceAgreement_of_rowTraceCoherence`). The replay
engine only *transports* the seed agreement through the memory transitions; it
never manufactures agreement. See `loadMemoryTimelineEvidence_of_coherenceEvidence`
in `OpEnvelope.lean` for the live discharge bridge from the coherence residual
to the legacy `MemoryTimelineEvidence` API.

**Strict shrink (non-degeneracy proof).** The reduction is real, not a rename:
`RowTraceCoherence` never constrains `regs` / `cycleCount` / `choiceState` /
`sailOutput`, so it admits load states the old whole-state identity forbids.
`ZiskFv.ZiskCircuit.MemTimeline.Spike.witness_nondegenerate` exhibits a
store-then-read model whose load state's `regs` **and** `cycleCount` differ from
the initial state's, with the full selected-load `MemoryTraceAgreement` still
derived end-to-end (`witness_memoryTraceAgreement`) — impossible under the
frozen `MemoryPrefixStateAlignment` route. Both witnesses depend on kernel
axioms only.

**Scope note (stores).** The sub-doubleword store RMW byte residuals
(`h_m1..h_m7` of `RowData_sb/sh/sw`) are byte-local facts of the *same* class
and reduce by the *same* `memoryTraceAgreement_of_rowTraceCoherence` +
`byte_facts_of_event_agreement` machinery, but they are positional fields of the
`OpEnvelope.sb/sh/sw` **constructors** (not a keyed `@[reducible] def` consumed
only inside dispatchers, as the load residual is). Reducing them requires an
`OpEnvelope` inductive refactor of the store arms and re-derivation inside the
store cores, which touches the caller-burden / hypothesis-count baselines for
the store opcodes. They are therefore **deferred** to a follow-up; only the load
residual is reduced here.

## Platform Profile

There are no project axioms for the current platform profile. PMP, PMA,
CLINT, and Zicfilp branches are discharged by ordinary Lean theorems in
`ZiskFv/SailSpec/Auxiliaries.lean`, using the global RISC-V profile
hypotheses carried by opcode proofs: machine mode, PMP disabled by the Sail
configuration, one ZisK physical-memory PMA region, aligned accesses, no HTIF,
C disabled in `misa`, and `mseccfg` readability.

These facts still define the verification target, but they are no longer in
the trusted axiom ledger.

## Clean Completeness

Clean component completeness placeholders have been retired from the source
trust ledger. The false or circular Clean completeness fields now set
`ProverAssumptions := False` and prove the field by ex falso, making the
mandatory Clean field a visible non-claim rather than trusted constructibility.
The push-only BinaryExtension base circuit remains honestly trivial and
axiom-free.

The Clean integration gate still keeps this boundary explicit: any future
`ZiskFv.AirsClean.*circuit_completeness` axiom must not enter the global
compliance theorem's project-axiom closure.

## ArithTable And DIV/REM Audit Conclusions

The opcode-shaped ArithTable axiom family has been retired from the active
trust shape. `generated/baseline-arith-table-op-axioms.txt` remains as a
guardrail so new `arith_table_op_*` trust facts cannot be added silently.

Active conclusions:

- True finite-table projections are now derived from row-native
  `ArithTableSpec` witnesses rather than trusted as opcode-shaped facts.
- False static claims such as unconditional W-mode `sext = 0` or static
  `np_xor` cannot be reintroduced; they must be replaced by dynamic proofs or
  explicit defect gates.
- `DIVU`, `REMU`, `DIVUW`, and `REMUW` are retired from the broad dynamic
  witness defect by deriving unsigned range, W high-chunk, nonzero-divisor,
  quotient high-zero, and remainder-bound facts from Clean ArithDiv/Binary
  evidence plus the unsigned Euclidean identity.
- Signed full-64 `DIV` and `REM` are now **narrowed and non-vacuously proved**:
  the `Defects.ArithDivDynamicWitnessShape` `.div`/`.rem` exclusion is the EXACT
  `op2 ≠ 0 ∧ |r| = |op2|` false-positive shape (`op2.toInt ≠ 0 ∧
  (signedRemainderInt v r_a).natAbs = op2.toInt.natAbs`), not the opcode-wide
  `True` — narrowed to the nonzero-divisor path so the divisor-zero branch is
  discharged separately (see the #114 bullet below). The canonical `equiv_DIV` /
  `equiv_REM` are real (no `False.elim`); they carry the WEAK signed remainder
  bound `h_r_le : |r| ≤ |op2|` plus the signed operand bridges / `h_nr_pin` /
  `h_r_sign` as caller residuals and DERIVE the STRICT `|r| < |op2|` from the
  narrowed-defect exclusion (`lt_of_le_of_ne`). Anti-vacuity is gate-checked by
  `Defects.honest_{div,rem}_witness_not_forge`. 0 `ZiskFv.*` axioms (the
  per-theorem `collectAxioms` closure is unchanged).
- Signed W-mode `DIVW` and `REMW` are now **narrowed and non-vacuously proved**
  (2026-06-20): the `Defects.ArithDivDynamicWitnessShape` `.divw`/`.remw`
  exclusion is the EXACT W false-positive shape on the nonzero-divisor path
  (`extractLsb op2 31 0 ≠ 0#32 ∧ (signedRemainderIntW v r_a).natAbs =
  (extractLsb op2 31 0).toInt.natAbs`), not the opcode-wide `True`. The missing mid-level W discharge infrastructure
  was built: `div_w_chain_witnesses` (the m32=1 W carry chain) +
  `h_rd_val_mdrs_{divw,remw}_chunked` (composing it with the existing low-level
  W bridges `abs_euclidean_to_signed_euclidean_div_rem_w`,
  `fgl_{div,rem}_w_signed_to_bv64`, `signed_t{div,mod}_unique`). The canonical
  `equiv_DIVW` / `equiv_REMW` are real (no `False.elim`); they carry the WEAK W
  bound `h_r_le : |r₃₂| ≤ |op2₃₂|` plus the W operand pins
  (`a_2=a_3=b_2=b_3=d_2=d_3=0`, `c_2=c_3=0`) / `h_nr_pin` / `h_r_sign` as caller
  residuals and DERIVE the STRICT `|r₃₂| < |op2₃₂|` from the narrowed-defect
  exclusion (`lt_of_le_of_ne`). Anti-vacuity is gate-checked by
  `Defects.honest_{divw,remw}_witness_not_forge`. 0 `ZiskFv.*` axioms (the
  per-theorem `collectAxioms` closure is unchanged).
- **Signed remainder-bound residual (DIV/REM only).** The WEAK bound
  `h_r_le : |r| ≤ |op2|`, the signed operand bridges (`na = MSB`-form
  `r.toInt = packed4 - sign·2^64`), and the sign-correctness witness `h_r_sign`
  are caller hypotheses, NOT axioms — same EXTRACTION-FIDELITY residual class as
  the MULH/MULHSU sign-range residual below. The real ZisK ArithDiv circuit
  enforces the weak bound via the `LT_ABS_NP`/`LT_ABS_PN` byte-chain comparison
  (`arith.pil:274`), but the FV model cannot derive it in-model without exposing
  the `LT_ABS_NP` false positive (`ltAbsNpByteChain_falsePositive_eqAbs256`); the
  narrowed `|r| = |op2|` defect exclusion upgrades the carried weak bound to the
  strict bound Sail requires. Visible in the canonical/wrapper caller-burden
  ledgers; details in [`defects.md`](defects.md)
  (`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`).
- **Divisor-zero / signed-overflow boundary discharge (DIV/DIVW/REM/REMW,
  #114, 2026-06-22).** The canonical theorems previously carried caller
  promises `h_op2_ne` (`op2 ≠ 0`) and `h_no_overflow` (¬`INT_MIN`/−1); both are
  now removed. The divisor-zero and signed-overflow branches are discharged
  in-model: `DIV`/`DIVW` consume the exposed ArithDiv boundary constraints
  `Airs.ArithDiv.div_boundary_constraints` — row-local div-by-zero/overflow
  flag machinery (forces divisor chunks `b = 0` / quotient `a = 0xffff` on
  div-by-zero, `b = −1` / dividend `c = INT_MIN` on overflow, plus the
  inverse-sum detector), faithful named-column mirrors of `arith.pil`
  constraints 0–30 now rendered by the uncurated `--skip-unsupported`
  extraction (65 defs, 0 stubs) — while `REM`/`REMW` derive the divisor-zero
  remainder from the carry-chain identity (`b = 0 ⟹ d = c`) plus chunk ranges.
  `ArithDivDynamicWitnessShape` is narrowed to the nonzero-divisor path
  accordingly. Net anti-laundering metric shrinks (8 `[bridge]` caller binders
  removed, 2 `[row]` `h_boundary` added; hypothesis-count 356 → 350);
  per-theorem `collectAxioms` closure still 0 `ZiskFv.*` axioms.
- Signed `MUL`, `MULH`, and `MULHSU` have their malicious-witness defect
  **narrowed** to the exact exceptional product-sign forge shape (`(na=1,nb=0,
  np=0)` / `(na=0,nb=1,np=0)`); the honest cases are proved non-vacuously
  (`equiv_MUL` / `equiv_MULH` / `equiv_MULHSU`, gate-checked by the
  `Defects.honest_{mul,mulh,mulhsu}_witness_not_malicious` anti-vacuity guards).
- **Sign-range residual (MULH/MULHSU only).** The high-half signed proof carries
  `na = MSB(op1)` / `nb = MSB(op2)` as explicit caller hypotheses (`h_sign_a` /
  `h_sign_b`), NOT axioms — the per-theorem `Lean.collectAxioms` closure of
  `equiv_MULH`/`equiv_MULHSU` is unchanged (0 `ZiskFv.*` axioms). The real ZisK
  ArithMul circuit enforces these via the indexed `range_ab` POS/NEG range lookup
  on `a[3]` (`zisk/state-machines/arith/pil/arith.pil:286/289/303`), but the FV
  extraction collapses that indexed lookup to the full `rangeTable16`, so the
  facts are unprovable in-model and are carried. This is an EXTRACTION-FIDELITY
  residual of the same class as the Aeneas row-lowering and Sail memory-timeline
  residuals above: satisfiable for every real trace, dischargeable-in-principle
  by composing the indexed `ArithRangeTable` lookup into balance. The new binders
  are visible in the canonical and wrapper caller-burden ledgers; details in
  [`defects.md`](defects.md) (`ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`).

The active defect boundaries and retirement criteria are in
[`defects.md`](defects.md).

## Active Caller Burden

The live per-canonical-theorem trust footprint is the axiom-closure ledger:

- [`generated/baseline-equiv-axiom-deps.txt`](generated/baseline-equiv-axiom-deps.txt)

> **Retired (2026-06):** the generated anti-laundering ledgers
> (`baseline-hypothesis-count.txt`, `baseline-caller-burden.txt`,
> `baseline-wrapper-caller-burden.txt`) and the DEEP
> construction-binder baseline were removed once the discharge campaign
> concluded at 0 project axioms. They measured per-binder churn that no
> longer tracks a real trust change; the axiom-closure baselines above
> (plus `baseline-zisk-riscv-compliant.txt`) remain the mechanically
> gated audit surface. Promise discharge should still visibly reduce
> caller-supplied promise hypotheses, but this is now authoring/review
> guidance rather than a gated metric.

For historical context, at retirement the canonical ledger held 1100 binder
rows and the wrapper ledger 1135, with `bridge` (122) and `row_shape`
(18 canonical / 22 wrapper) the dominant remaining categories — documented as
generated or full-ensemble integration boundaries, not hidden global axioms.

## Accepted-Trace Certificates (non-axiom obligations on `AcceptedZiskTrace`)

These are **not** Lean axioms (none appears in `generated/baseline-axioms.txt`;
the per-theorem axiom closures are unchanged) and **not** derived from
`constraints_hold` + `channels_balanced` (so they are not folded into
`AcceptedZiskTrace.spec_holds`). They are explicit **structure fields** on
`AcceptedZiskTrace` — verifier-checked facts a real ZisK proof certifies about
the committed trace, but which the single-row Clean `Air.Flat` model cannot
itself express. Each is PIL-faithful and constructible (real ZisK traces satisfy
it). They are documented here precisely because they add to the accepted-trace
trust surface even though they add no axiom.

| Field (`Compliance/AcceptedZiskTrace.lean`) | PIL source | What it certifies |
|---|---|---|
| `main_height` (pre-existing) | — | the Main table has a row for every instruction (`i < length`) |
| `transitions_hold` (**#100**) | `main.pil:409-410` | the cross-row PC-handshake transition holds on every consecutive Main-row pair (a *polynomial* constraint the single-row per-row `Constraints` dropped) |
| `segment_l1_fixed` (**#100**) | `main.pil:19` | the `SEGMENT_L1` fixed column is `[1,0,0,…]` (row 0 = boundary, all later rows within-segment) |

**#100 trust-surface change (honest accounting — a SHIFT, documented as such).**
The next-PC discharge does **not** derive `h_nextPC_matches` from the existing
`constraints_hold`. It **removes** the 63 per-opcode cross-world
`h_nextPC_matches` promises (each asserting *circuit next-PC = Sail next-PC*, the
worst, conclusion-adjacent class) and in their place adds:
- the **two accepted-trace certificates above** (`transitions_hold`,
  `segment_l1_fixed`) — `main_height`-class, declared on the Main component via
  `Air.Flat.Component.transition`, carried once for the whole trace; and
- per-opcode **decode pins** (`set_pc`/`jmp_offset…`, the sailTrace-free
  `rowDecode` bucket, dischargeable via #74) and the **PC-provenance bridge**
  (`h_pc_bridge`/`h_pc_bound`, the same class JAL/AUIPC already carried).

So a cross-world output promise is replaced by an in-circuit polynomial
certificate plus dischargeable decode + the existing provenance class, with the
per-op flag/target/cast content **proven** (0 new `ZiskFv.*` axioms). The Clean
`Air.Flat.Component.transition` field is *inert* (no Clean soundness theorem
consumes it — see `docs/clean-fork-divergences.md` D1); the obligation lives
entirely at the `AcceptedZiskTrace` layer, which is why it is in `main_height`'s
class rather than `constraints_hold`'s.

**Within-segment boundary (explicit).** `mainTransition_to_next_pc`
(`Compliance/MainTransition.lean`) requires `i + 1 < mainTable.table.length` — a
*successor* Main row must exist — surfaced as the per-opcode `h_idx`. `main_height`
only gives `i < length`, so for the final instruction this needs
`numInstructions < length` (a real ZisK segment is padded to its fixed power-of-two
row count, so a successor row exists). When the segment is exactly full
(`numInstructions = length`) the final instruction has no within-segment successor;
its next-PC is the cross-segment continuation (`main.pil:501-529`), which is
**out of #100 scope = #103**. This is an applicability boundary, not an
unsoundness: where `h_idx` holds the discharge is exact; where it does not, the
final-row next-PC is a named #103 residual.

## Raw-Program Binding (#159 — decode derived from the committed RISC-V program)

#159 makes the per-opcode **decode** load-bearing on the committed raw RISC-V
program, via the **additive** endpoint `root_soundness_rawProgram`
(`ZiskFv/Soundness.lean`). It does **not** change `root_soundness`,
`AcceptedZiskTrace`, or any `equiv_<op>` (all byte-for-byte unchanged; the
endpoint's axiom closure is **identical** to `root_soundness`'s — 0 new
`ZiskFv.*` axioms, verified by `#print axioms`). It is a separate, stronger
statement a caller may use in place of `root_soundness`.

**What it derives.** Where `root_soundness` takes `rowDecodes` (per row, the
caller asserts the committed ROM's decode COLUMNS — op/flags/jmp_offset/ind_width),
`root_soundness_rawProgram` takes a **thinner** `RawRowDecode` bundle and
*computes* those columns through the **real Aeneas transpile pipeline**
`extract_transpile_rv64im_raw` (`trust/aeneas/ProductionM2.lean`):
`rawProgram(pc) → decode (#164) → lower (#111 + #159 block-2) → serialize → committed
ROM message`. So the decode columns move from **assumed** to **derived** (kernel-only:
the 63 `Decode_<op>_from_rawProgram` are `{propext, Classical.choice, Quot.sound}`).

**The two new caller premises (non-axiom, additive):**

| Premise (`Compliance/TraceLevelExport/RawProgramBinding.lean`) | What it is | Class |
|---|---|---|
| `rawProgram : Fin n → BitVec 32` | the committed raw RISC-V program (32-bit words) | a verifier-attached image, same epistemic class as `transitions_hold` — a real ZisK proof commits to a concrete program |
| `ProgramBinding trace rawProgram` | `∀ k, trace.program k = romMessageOfRaw (trace.program k).line (rawProgram k)` — the committed ROM holds exactly the serialized real-lowering of the raw program. **Op-agnostic** (one pipeline per word; per-op decode is derived through it, not baked in) | a property of any honestly-generated witness (the prover builds `trace.program` by running exactly this pipeline); not an axiom, not a `constraints_hold` consequence |

**The boot premise (irreducible, document-only).** "`rawProgram` *is* the intended
RISC-V binary" is the spec↔binary correspondence every verified-binary claim
carries. It is **not** a Lean hypothesis — it is the meaning attached to
`rawProgram`, not Lean-provable (the compile/commitment boundary). Documented here
so it is not silently assumed away.

**Honest reduction.** Per row, `RawDecode_<op>` carries the structural `h_idx`, the
**same** non-ROM operand witnesses block-1's `Decode_<op>` already carried
(signed-load `BinaryExtension`, shift `h_b_lo_t`, M-ext arith, JALR/LUI/FENCE), and
**one** op-shaped raw-word fact (`rawProgram(pc) = rawShape …`) — replacing the
several ROM-column-correctness facts (now computed). None of the operand witnesses
is new, split, or multiplied. Non-vacuous: a real trace inhabits each bundle
(`rawProgram` the actual binary; `ProgramBinding` holds because the ROM is its
serialized lowering; the raw-word fact holds because the binary at that pc is that
instruction). The lowering-totality obligation #111 / block-2 *assumed* (the lowerer
succeeds) is **proven** here (`Extraction/Totality.lean`: register overflow branches
unreachable via the 5-bit decode bound).

**Scope (honest).** The decode columns are derived — this is the #159 decode goal.
NOT yet via this endpoint: tying the Sail-side instruction to `rawProgram` (the
`W → Sail decode` bridge, a further grounding) and the full operand-field
MirrorFidelity (only the decode-relevant ROM fields are pinned). Those are
follow-ups; the operand witnesses remain caller premises exactly as before. Depends
on #164 (the in-build `W → fields` decoder).

## Not In This Ledger

The trust ledger does not enumerate the Lean kernel, mathlib,
LeanZKCircuit, the Sail-to-Lean compiler output, or flake-pinned upstream
inputs. Their audit surface is the Lake/Nix configuration and `flake.lock`,
not `generated/baseline-axioms.txt`.
