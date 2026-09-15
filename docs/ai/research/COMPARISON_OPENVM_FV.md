# zisk-fv vs openvm-fv: trust surface and proof coverage

Updated: 2026-08-21.

This report replaces the 2026-07-17 comparison. It keeps the same OpenVM target and updates ZisK to the merged #359 tree.

## Audit targets

- `openvm-fv`: `/home/cody/openvm-fv`, `main` at `8f067fd56465d2e9fc6f56ea6a3ecdd2e55ee508`.
- `zisk-fv`: `origin/main` at `08db164596bfdedb3be284f7b53960d60b3bbdd8`.
- OpenVM proof content did not change since the July report.
- ZisK advanced through the raw-program root, extraction gates, PC simulation, and register simulation.

The four June reports in `/home/cody/openvm-fv` remain useful for OpenVM source detail. Their ZisK measurements are obsolete.

## Verdict

Both projects prove Lean theorems that connect circuit constraints to Sail RISC-V semantics. They now expose different proof boundaries.

OpenVM proves 45 independent RV32IM row theorems. Each theorem assumes its row constraints, bus facts, platform facts, and Sail read agreement.

ZisK proves one RV64IM trace theorem for all 63 operation families. The theorem starts from an accepted multi-AIR witness and a committed raw program.

ZisK has the broader and more integrated soundness claim. It also has the larger unfinished premise-discharge program. The remaining `InputsAgreeCore` premise prevents an unconditional machine-simulation reading.

## Headline comparison

| Item | openvm-fv | zisk-fv |
|---|---|---|
| ISA | 45 RV32IM operations | 63 RV64IM operations |
| Main theorem form | 45 independent row theorems | One theorem over every step of an accepted trace |
| Public soundness entrypoint | Per-operation `equiv_<OP>` theorems | `ZiskFv.Compliance.root_soundness` |
| Raw-program binding | Hand-written transpiler model enters through program-bus assumptions | `ProgramRowsBinding` plus per-step `RawProgramDecode` |
| Cross-row PC relation | Not aggregated | Generated chained Sail trace plus one `pcBoot` premise |
| Register simulation | Register reads remain inside each theorem's bus premise | Proved from `regBoot` by #330 and #359 |
| Memory simulation | Memory reads remain inside each theorem's bus premise | Partly derived, with `bootSeed` and operation facts remaining |
| Project trust declarations | One unused `opaque undefined : Prop` | Zero source trust declarations |
| Concrete root use | No theorem instantiation | Two direct `root_soundness` calls |
| Checked witness modules | No `example` declarations | 31 files under `trust/consistency`; 10 root-instantiation gate modules |
| Known target defects | No defects reported by the project | Six active theorem-side defect IDs plus one JALR model gap |
| Trust gates | No equivalent repository gate | 20 syntactic checks and 20 semantic checks |
| Input pinning | The tracked tree does not pin an OpenVM source revision | `flake.lock` pins Sail, ZisK, PIL tools, Clean, and Nix inputs |
| Lean size | 83,366 lines in the local repository | 296,580 lines in the audited archive |
| Completeness | No acceptance theorem | One proven Sail-to-shape theorem plus a conditional five-obligation endpoint |

Line counts include all Lean files outside generated build directories. They measure repository size, not proof quality.

## OpenVM theorem surface

`OpenvmFv/Equivalence/Equivalence.lean` contains 45 `equiv_<OP>` theorems. A representative theorem accepts these facts:

- A valid AIR wrapper and a row index.
- All extracted constraints for that row.
- A selector fact that marks the row as active.
- Per-row bus axioms and well-formedness assumptions.
- The proposition half of `bus_effect` for the current Sail state.

The proposition half of `bus_effect` contains the important cross-world facts. It states that register and memory reads equal values in the supplied Sail state.

OpenVM therefore proves a strong local implication. It does not prove that all active rows in one accepted trace satisfy those cross-world premises together.

### OpenVM strengths

- The 45 proofs use a uniform family structure and compact tactic macros.
- The named AIR mirrors connect to extracted constraints through hundreds of checked bridge uses.
- The project proves useful memory-consistency lemmas in `Fundamentals/MemoryConsistency.lean`.
- The public report states the environment, specification, and infrastructure assumptions.

### OpenVM limits

- No theorem aggregates the 45 operation theorems into one trace theorem.
- No checked example constructs a complete theorem hypothesis bundle.
- The memory-consistency theorems do not feed the 45 operation theorems.
- Lookup and range guarantees enter through per-row well-formedness assumptions.
- The hand-written Lean transpiler enters through `ProgramBusEntry.operand_properties`.
- The tracked repository does not pin the OpenVM circuit source revision.
- Six passive `Constraints/*.lean` files are empty.
- The extraction comments out constraints that depend on permutation challenges.

The July report incorrectly said `wf_propertiesToAssertPerRow` was never proved. The `Spec/*.lean` files prove it for active operation families. The corrected point is narrower: the top-level development does not compose those local guarantees into a closed trace argument.

## ZisK theorem surface

`root_soundness` now accepts:

- An `AcceptedZiskTrace`.
- An initial Sail state.
- One operation classification for each executed step.
- A committed raw program and its exact row binding.
- One `RawProgramDecode` proof for each step.
- One `InputsAgreeCore` bundle for each step.
- The explicit `pcBoot`, `rowsAligned`, `bootSeed`, `regBoot`, and defect premises.

It constructs `ProgramDecode` from the raw program. It constructs the Sail trace by executing and retiring each selected instruction. It proves `StepSound` for every accepted step.

The semantic result states that Sail execution equals the state effect of the committed bus rows. This result is substantially stronger than 63 unrelated row implications.

## Progress since the July report

### Raw-program root

The public root now takes `ProgramRowsBinding` and `RawProgramDecode`. It no longer accepts arbitrary per-step `ProgramDecode` bundles.

The production Aeneas path checks decode and lowering facts against the pinned ZisK Rust source. The main proof constructs all operation decode bundles from that committed program surface.

The Sail decoder is not yet tied to the same raw word. Issue #172 tracks that connection.

### PC simulation

#343 removed the caller-supplied Sail trace and per-row PC bridge. `root_soundness` builds `chainedSailTrace` from the initial state.

The root retains one `pcBoot` equation. It also retains `rowsAligned` because a multi-row unaligned JALR does not fit the current step-to-row index model.

### Register simulation

#330 and #359 removed the four register-lane field families from all operation structures. The proof derives register agreement from `regBoot`, channel balance, register-write coverage, and Sail writeback.

This work removed 116 per-row register assumptions. It did not remove the complete `InputsAgreeCore` bundle.

### Extraction and composition gates

The repository now has these independent checks:

- A pilout-to-generated-Lean round-trip gate.
- A generated-constraint-to-hand-written-mirror gate.
- A consumed-check that detects generated constraints with no proof consumer.
- Column-map pins for 12 registered AIR welds.
- A snapshot for all declared channel metadata.
- A production Aeneas extraction and delegation gate.

These gates cover more of the extraction chain than the July report described. They do not prove that all compile-time bus emitters are modeled. Issue #354 records that separate class.

### Trust enforcement

The source trust ledger contains zero entries. The public theorem's project axiom closure also contains zero project declarations.

The fast gate runs 20 syntactic checks. The semantic gate runs 20 elaborated checks. The merged #359 tree passed `lake build`, both trust gates, the Rust tests, and the extracted-Lean build before merge.

### Defect handling

The theorem exposes six active defect IDs:

- Signed multiplication witness soundness.
- Signed division remainder-bound soundness.
- Signed division quotient-sign soundness.
- MemAlign narrow-load lane soundness.
- MemAlign skippable-prove soundness.
- FENCE acceptance incompleteness.

The JALR expansion index problem remains a separate explicit `rowsAligned` premise. The defect ledger classifies it as a model gap instead of a per-operation defect ID.

## Premise mapping

| OpenVM premise class | Current ZisK counterpart | Current ZisK status |
|---|---|---|
| Row constraints | `AcceptedZiskTrace.constraints_hold` | One accepted-trace certificate |
| Cross-table lookup facts | `channels_balanced` plus provider proofs | Derived for many routes; incomplete for some memory and operation facts |
| Register reads equal Sail | `regBoot` plus `RegAgree` induction | Derived by #330 and #359 |
| Memory reads equal Sail | `bootSeed`, memory replay, and operation input facts | Partly derived; full memory simulation remains open |
| PC relation | `pcBoot` plus `chainedSailTrace` | Derived after boot, subject to `rowsAligned` |
| Program decode | `ProgramRowsBinding` plus `RawProgramDecode` | Derived into all 63 `ProgramDecode` bundles |
| Sail decode of the same word | No completed root connection | Open as #172 |
| Platform assumptions | Fields inside operation input bundles | Still caller-supplied in several families |
| Known implementation defects | `hAvoidKnownBugs` | Explicit, narrow theorem exclusions |
| Proof-system soundness | `channels_balanced` certificate semantics | Outside Lean in both projects |

## The current `InputsAgreeCore` gap

The name is now broader than its original cross-machine role. It dispatches to 63 operation structures containing:

- 356 proof fields.
- 127 data and witness fields.
- 483 fields in total.

The proof fields include Sail input facts, platform facts, provider matches, range witnesses, memory messages, and arithmetic conditions. Some fields are derivable from the accepted trace. Some fields must become explicit boot or platform premises.

Issue #360 owns the complete removal of this aggregate premise. It must not reopen or expand completed #330.

## Concrete witness correction

The July report claimed three direct `root_soundness` instantiations. The current tree has two direct calls:

- `AddFaithfulPaddedRootSoundness.lean`, with one executed step.
- `MemoryRawRootSoundness.lean`, with zero executed steps.

The semantic gate has 10 files named as root-instantiation checks. Several files check interior multi-step theorems or supporting raw-program facts instead of calling `root_soundness`.

No direct root witness reaches Sail state index one. Issue #353 tracks this coverage gap.

## Completeness status

ZisK has two checked endpoints:

- `sail_executable_within_supported_decode_shape` proves that a Sail-executable RV64IM word has a supported raw shape.
- `skeletal_root_completeness` proves acceptance only after five ZisK obligations are supplied.

The second theorem remains conditional. The Aeneas harness checks related production obligations in a separate generated workspace, but the main Lake theorem does not import that result.

Therefore, ZisK has a real completeness framework that OpenVM lacks. It does not yet have an unconditional end-to-end completeness theorem.

## Remaining ZisK boundaries

1. `InputsAgreeCore` remains a per-step aggregate premise. Issue #360 owns its removal.
2. `bootSeed` remains the single-segment memory seed.
3. `rowsAligned` excludes a non-final two-row JALR lowering.
4. Six defect IDs narrow the claim around known ZisK defects.
5. Cross-segment continuation remains outside the root theorem.
6. Compile-time bus emitters are not fully welded to generated artifacts.
7. The Sail decoder does not yet connect to the committed raw word.
8. The completeness endpoint remains conditional on five ZisK obligations.
9. Proof-system soundness, Sail extraction, PIL compilation, and the Lean kernel remain external trust.

## Final assessment

OpenVM remains a clean and useful reference for per-operation AIR proofs. Its proof architecture is smaller and more uniform.

ZisK now goes farther on trace aggregation, raw-program binding, PC simulation, register simulation, extraction checks, defect evidence, and trust enforcement. These additions explain most of its larger code size.

The comparison must not overstate ZisK's result. `root_soundness` still depends on `InputsAgreeCore`, a memory seed, platform facts, alignment, and defect exclusions. The proof is a strong conditional trace theorem, not a complete verifier-to-Sail refinement theorem.

## Provenance

OpenVM facts were checked directly at `8f067fd` from:

- `OpenvmFv/Equivalence/Equivalence.lean`.
- `OpenvmFv/RV32D/BusEffect.lean`.
- `OpenvmFv/Fundamentals/MemoryConsistency.lean`.
- `OpenvmFv/Fundamentals/Interaction.lean`.
- `OpenvmFv/Spec/*.lean` and `OpenvmFv/Constraints/*.lean`.
- `REPORT.pdf` and the four local June audit files.

ZisK facts were checked from the `origin/main` archive at `08db1645`:

- `ZiskFv/Soundness.lean`.
- `ZiskFv/Compliance/AcceptedZiskTrace.lean`.
- `ZiskFv/Compliance/TraceLevelExport/Dispatcher.lean`.
- `ZiskFv/Completeness.lean`.
- `trust/README.md`, `trust/trusted-base.md`, and `trust/defects.md`.
- `trust/generated/baseline-axioms.txt` and `baseline-strong-export-binders.txt`.
- `trust/scripts/check-all.sh` and `check-all-semantic.sh`.
- The files under `trust/consistency/`.

No build ran for this documentation update. The report uses the full gates recorded on the merged #359 commit.
