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
| Sail memory timeline          | 0            | 0                 | Discharge `env.memoryTimelineEvidence` by proving whole-execution memory replay/timeline induction.       |
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

The production-backed Aeneas extraction is checked by the repository test path,
but the generated Aeneas Lean is not yet imported by the main Lake proof to
derive every row-provenance, row-mode, source-lane, immediate, PC, and link
bridge fact consumed by the compliance wrappers. Until those generated facts
are imported and used inside main Lake, the gap is represented by a visible
global theorem hypothesis:

```text
h_bridge : env.aeneasBridgeTrust
```

The existing wrapper and `OpEnvelope` signatures still expose those fields
because the dispatch proofs pass them to the current wrapper layer. The
generated caller-burden ledgers remain the mechanical inventory for the later
refactor that removes those parameters after generated Aeneas Lean supplies
proofs inside Lake.

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
  `|r| = |op2|` false-positive shape (`(signedRemainderInt v r_a).natAbs =
  op2.toInt.natAbs`), not the opcode-wide `True`. The canonical `equiv_DIV` /
  `equiv_REM` are real (no `False.elim`); they carry the WEAK signed remainder
  bound `h_r_le : |r| ≤ |op2|` plus the signed operand bridges / `h_nr_pin` /
  `h_r_sign` as caller residuals and DERIVE the STRICT `|r| < |op2|` from the
  narrowed-defect exclusion (`lt_of_le_of_ne`). Anti-vacuity is gate-checked by
  `Defects.honest_{div,rem}_witness_not_forge`. 0 `ZiskFv.*` axioms (the
  per-theorem `collectAxioms` closure is unchanged).
- Signed W-mode `DIVW` and `REMW` remain opcode-wide defect-gated: their
  EquivCore signed-W discharge (`h_rd_val_mdrs_{divw,remw}_chunked`,
  `div_w_chain_witnesses`) is not yet built (the low-level W bridges
  `fgl_{div,rem}_w_signed_to_bv64`, `abs_euclidean_to_signed_euclidean_div_rem_w`,
  `signed_tmod_unique` exist; the mid-level glue does not).
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

The generated anti-laundering ledgers are:

- [`generated/baseline-hypothesis-count.txt`](generated/baseline-hypothesis-count.txt)
- [`generated/baseline-caller-burden.txt`](generated/baseline-caller-burden.txt)
- [`generated/baseline-wrapper-caller-burden.txt`](generated/baseline-wrapper-caller-burden.txt)
- [`generated/baseline-equiv-axiom-deps.txt`](generated/baseline-equiv-axiom-deps.txt)

Promise discharge must visibly reduce caller burden, unless a documented
structural-unpacking exception explains why added structural witnesses collapse
into shared global-theorem evidence.

Current caller-burden summary:

- Canonical total rows: 1100 (was 1082; +18 from the DIV/REM vacuous→real
  signed-remainder-bound residual binders, see `defects.md`; the prior +20 was
  the MULH/MULHSU sign-range residual).
- Wrapper total rows: 1135 (was 1130; +5 net from the DIV/REM real-discharge
  wrappers replacing the `False` binder with structural residuals).
- `bridge`: 122 in both ledgers.
- `row_shape`: 18 canonical, 22 wrapper.
- `bus_shape`: 0 in both ledgers.

The remaining `bridge` and `row_shape` entries are documented as generated or
full-ensemble integration boundaries, not as hidden global axioms.

## Not In This Ledger

The trust ledger does not enumerate the Lean kernel, mathlib,
LeanZKCircuit, the Sail-to-Lean compiler output, or flake-pinned upstream
inputs. Their audit surface is the Lake/Nix configuration and `flake.lock`,
not `generated/baseline-axioms.txt`.
