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
| Source Lean trust declarations                                         | 6     | [`generated/baseline-axioms.txt`](generated/baseline-axioms.txt)                             |
| Transitive project-axiom closure of `zisk_riscv_compliant_program_bus` | 0     | [`generated/baseline-zisk-riscv-compliant.txt`](generated/baseline-zisk-riscv-compliant.txt) |

The source trust ledger contains six Clean completeness declarations. The global
theorem currently has no transitive project-axiom closure. The former Aeneas
row-lowering and memory-state load bridge axioms are now visible conditional
inputs: `env.aeneasBridgeTrust` and `env.memoryTimelineEvidence` on the global
theorem.

The extraction assumptions are part of the project premise but outside the
Lean axiom ledger:

- Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
- ZisK RV64IM circuit-to-Lean extraction from flake-pinned ZisK/PIL inputs.

## Current Classes

| Class                         | Declarations | In global closure | Removability                                                                                             |
| ---                           | ---:         | ---:              | ---                                                                                                      |
| Aeneas row-lowering condition | 0            | 0                 | Discharge `env.aeneasBridgeTrust` by importing generated Aeneas Lean into main Lake.                      |
| Sail memory timeline          | 0            | 0                 | Discharge `env.memoryTimelineEvidence` by proving whole-execution memory replay/timeline induction.       |
| Clean completeness            | 6            | 0                 | Completeness-only placeholders; removable by proving each Clean circuit completeness theorem internally. |


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

Generated-bridge manifest: generated Aeneas Lean remains reproducible build
output under `build/aeneas-production-extraction`. The maintained trust-gate
artifact is [`aeneas-generated-bridge-manifest.txt`](aeneas-generated-bridge-manifest.txt),
checked by `trust/scripts/check-aeneas-generated-bridge-manifest.sh` and by
`trust/scripts/check-all.sh`. It keeps the generated row-shape predicates and
Lean examples aligned with the generator template, and checks generated output
when present, without committing generated Lean.

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
`Nonempty (FullWitnessGeneratedTimelineEvidence state bus.e1)`; non-load arms
require no memory evidence. Dispatch coerces that generated full-witness source to
`MemoryTimelineEvidence state e1` and reconstructs canonical `LoadPromises`
with `LoadPromises.memory_timeline` before calling the load theorems. The
`OpEnvelope` load constructors themselves carry only `LoadStructuralPromises`,
so they no longer accept a per-load byte oracle.

`FullWitnessGeneratedTimelineEvidence` wraps `FullWitnessMemoryTimelineEvidence`
and makes the generated ProverData sidecar source explicit: it carries
`FullWitnessMemAirSourceProverDataWitnessFacts` and records that the stored
sidecars are exactly the sidecars packaged from those witness facts. The inner
`FullWitnessMemoryTimelineEvidence` contains the concrete full-ensemble witness,
the `FullWitnessMemAirSourceRawSidecars` callback for the witness-selected
mutable Mem table, and only the residual whole-execution memory-timeline facts.
A derived Mem AIR source accessor selects the `FullWitnessMemReplayBridge`,
which derives the
`AcceptedMemoryReplayEvidence` sub-object used by `MemoryTimelineEvidence`,
including prefix-read soundness for the accepted Mem rows. The residual
timeline facts state that those rows split around the selected read, the
selected row is a read, the initial Sail memory agrees with the replay memory,
and the selected Sail state is the state reached by replaying the accepted
prefix. The canonical load proofs derive `LoadByteAgreement` from the resulting
timeline evidence and the memory replay relation.

Generated/full-ensemble Mem facts target
`FullWitnessMemAirSourceProverDataWitnessFacts`: Clean assertion/lookup
witnesses plus named `witness.data` sidecar keys for raw split generated
constraints, row range facts, segment range facts, and the stage-2 source
columns for each mutable Mem table. The reproducible generated wrapper
`Extraction.MemGeneratedArtifact` exposes `buildWitnessFacts`, which assembles
that target from the three per-table callback families, plus
`buildWitnessFactsFromRawFacts`, which adapts raw ProverData fact callbacks to
the same witness target. It also exposes `buildTimelineEvidence`, which passes
the assembled facts to
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`. The top-level
`nix run .#test` gate compiles
`build/extraction/Extraction/MemGeneratedArtifact.lean` directly so this
orphaned generated wrapper stays synchronized with the checked Lean API.
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts` packages that
target into the load-facing boundary. Lean packages the resulting sidecar
callback into the witness-selected `FullWitnessMemAirSource` via
`fullWitnessMemAirSourceOfRawSidecars`, and
`fullWitnessMemoryTimelineEvidence_of_rawSidecars` combines it with only the
residual Sail timeline fields above. `FullWitnessMemAirSourceRawFacts` and
`fullWitnessMemoryTimelineEvidence_of_rawFacts` remain compatibility adapters
for lower-level generated modules that still produce the raw sigma callback;
`fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts` is the checked
adapter for raw ProverData facts.

Retirement path: emit/prove the extractor/full-ensemble
`FullWitnessMemAirSourceProverDataWitnessFacts`, then prove the whole-execution induction
connecting accepted Mem rows, initial Sail memory agreement, and selected Sail
state without assuming `env.memoryTimelineEvidence`. The table/list-position
part of the bridge is named as `MemTableGeneratedRowsBridge`, which connects
Clean `table.table` positions to `rowAt mem idx` and the row-indexed
`generated_every_row` constraints. `FullWitnessMemReplayBridge` packages the
concrete full-ensemble Mem table, generated-row/range/fixed-column facts,
active-row equality, and nonempty segment evidence; its constructor derives the
accepted replay subobject, so `AcceptedMemoryReplayEvidence.prefixReadSound` is
no longer a bare global-boundary assumption.

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

The Clean component completeness placeholders are explicit source-ledger trust
declarations again:

```text
ZiskFv.AirsClean.BinaryAdd.binaryAdd_circuit_completeness
ZiskFv.AirsClean.MemAlignByte.memAlignByte_circuit_completeness
ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByte_circuit_completeness
ZiskFv.AirsClean.ArithMul.arithMul_circuit_completeness
ZiskFv.AirsClean.ArithDiv.arithDiv_circuit_completeness
ZiskFv.AirsClean.Main.mainWithRomAndMemBus_circuit_completeness
```

These are completeness-direction placeholders for Clean circuits, not
per-opcode output-equality soundness axioms. The Clean integration gate keeps
them out of the global compliance theorem's project-axiom closure.

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
- Signed `DIV`, `DIVW`, `REM`, and `REMW` remain defect-gated because the
  signed remainder-bound route exposes an `LT_ABS_NP` byte-chain mismatch.
- Signed `MUL`, `MULH`, and `MULHSU` remain defect-gated for signed witness
  soundness under malicious witness construction.

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

- Canonical total rows: 1062.
- Wrapper total rows: 1117.
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
