# 01 — Architecture map (as-is)

All line counts and file counts below are measured from the tree at the reviewed
revision. Treat them as orientation, not contract; re-measure before citing.

## 1.1 Mass distribution

`ZiskFv/` is ~218k lines across 619 `.lean` files. By top-level area:

| Area | files | lines | role |
| --- | ---: | ---: | --- |
| `Compliance/` | 158 | 76.7k | per-opcode wrappers, constructions, `OpEnvelope`, trace-level export, dispatch — **the bulk** |
| `AirsClean/` | 87 | 38.5k | the Clean-native circuit model (components, ensembles) |
| `EquivCore/` | 96 | 37.5k | per-opcode equivalence "core" + shared bridges + write-value proofs |
| `Airs/` | 32 | 17.9k | **legacy** record model (`Valid_<AIR>`), still load-bearing |
| `Completeness/` | 17 | 12.3k | completeness skeleton + Sail decode shape + aspirational route |
| `ZiskCircuit/` | 66 | 10.0k | circuit-side semantics per opcode |
| `SailSpec/` | 65 | 8.7k | Sail-side bridges per opcode |
| `Bits/` | 10 | 6.6k | packed bit-vector arithmetic |
| `Equivalence/` | 63 | 5.4k | per-opcode *canonical* `equiv_<OP>` (thin over `Compliance`) |
| `Tactics/`, `Channels/`, `Field/`, `RowShape/` | 22 | ~4.4k | shared infra |

Two observations jump out: (a) `Compliance/` is a third of the project and is
almost entirely per-opcode glue; (b) `Airs/` (legacy) and `AirsClean/` (Clean)
are two models of the same circuits, together ~56k lines.

## 1.2 The pipeline (data flow)

```
 Sail RV64 spec (LeanRV64D)            ZisK PIL / pilout            ZisK Rust (Aeneas)
        │                                    │                            │
   SailSpec/<op>.lean               tools/pil-extract → Extraction   trust/aeneas/ProductionM2
   (pure execute bridges)                     │                            │
        │                          ┌──────────┴───────────┐               │
        │                          │                       │               │
        │                    Airs/ (Valid_<AIR>      AirsClean/<Op>   AeneasBridgeTrust
        │                    record model, legacy)   (Clean GFC + FlatComponent)
        │                          │                       │
        │                          │   AirsClean/<Op>/Bridge.lean  (rowAt, spec_of_valid)
        │                          │◄──────────────────────┘
        │                          ▼
        │                    ZiskCircuit/<Op>.lean  (compositional circuit semantics)
        │                          │
        └────────────►  EquivCore/<Op>.lean  (Sail execute == bus_effect of circuit rows)
                                   │
                          Equivalence/<Op>.lean  (canonical equiv_<OP>; thin re-export)
                                   │
                       Compliance/Wrappers/<Op>.lean  (discharge "promise" hypotheses)
                                   │
             Compliance/Construction<Op> + OpEnvelope arm  (build the per-arm bundle)
                                   │
              Compliance.lean : zisk_riscv_compliant_program_bus  (per-arm channel balance)   ◄── OLD root
                                   │
        Compliance/TraceLevelExport/StepStrong* : construct OpEnvelope.<op>, invoke old thm
                                   │
                 Compliance/AcceptedZiskTrace (Clean FormalEnsemble witness)
                                   │
                     ZiskFv/Soundness.lean : root_soundness  (per-step StepSound)             ◄── NEW root
```

The **Clean-native** part is the right column plus `AcceptedZiskTrace`:
`AirsClean/FullEnsemble.fullRv64imEnsemble : FormalEnsemble FGL unit`, and
`AcceptedZiskTrace` is an `Air.Flat.EnsembleWitness` with `constraints_hold` and
`channels_balanced`. `witness_spec_of_constraints` lifts per-table specs from
constraints + balance via `Ensemble.tableSoundness_of_soundChannels`. **This
seam is idiomatic.** Everything to its left (the two circuit models, the equiv
stack, the `OpEnvelope` dispatch) is bespoke.

## 1.3 The two stacked root theorems

There are two distinct top-level soundness statements, and the "new" one is
literally implemented by calling the "old" one.

### Old: `ZiskFv.Compliance.zisk_riscv_compliant_program_bus`
`ZiskFv/Compliance.lean`. Signature (paraphrased):

```lean
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope state m r_main)
    (h_bridge : env.aeneasBridgeTrust)
    (h_memory_construction : env.memoryTimelineConstructionEvidence)
    (h_known_bugs : Defects.NoKnownDefect env) :
    env.exec_eq
```

where `OpEnvelope` is a **63-arm inductive** (one arm per opcode, each carrying
that opcode's inputs + `Promises` bundle + row/provenance facts), and
`env.exec_eq` is a **12-way conjunction** of per-family `exec_eq_<family>` Props
in which *exactly one* conjunct is the real `= state_effect_via_channels …`
statement and the other eleven are `True`.

### New: `ZiskFv.Compliance.root_soundness`
`ZiskFv/Soundness.lean`. Signature (paraphrased):

```lean
theorem root_soundness
    (numInstructions : Nat)
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (sailTrace : SailTrace numInstructions)
    (ziskStep      : ∀ i, ZiskStep ziskTrace i)
    (programDecodes: ∀ i, ProgramDecode ziskTrace i (ziskStep i))
    (inputsAgree   : ∀ i, InputsAgree ziskTrace sailTrace i (ziskStep i))
    (bootSeed      : BootSegmentMemorySeed ziskTrace sailTrace ziskStep)
    (hAvoidKnownBugs : ∀ i, RowOutsideDefectRegion ziskTrace i (ziskStep i)) :
    ∀ i, StepSound ziskTrace sailTrace i (ziskStep i)
```

The per-step proof (`stepSound_of_evidence` → `TraceLevelExport/StepStrong*`)
constructs an `OpEnvelope.<op>` and calls `zisk_riscv_compliant_program_bus`.
E.g. `StepStrongAluArith.lean` builds `OpEnvelope.sub …` and extracts
`(zisk_riscv_compliant_program_bus env …).2.2.2.2.1`.

**Consequence for the audit surface (corrected):** the "headline" theorem is
*stacked* on the internal one, but its trust surface is **not** split.
`aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`, and the `Promises` are
hypotheses of the *internal* `zisk_riscv_compliant_program_bus`; the
`StepStrong*` steps **discharge** them from accepted-trace data when constructing
each `OpEnvelope` arm (e.g. `StepStrongAluArith.lean:223` proves
`env.aeneasBridgeTrust`; `memoryTimelineConstructionEvidence` is `trivial` on
non-load arms and `bootSeed`-derived on load arms). The frozen
`#print axioms root_soundness` in `ZiskFv/Audit.lean` (Sail primitives + standard
axioms only) confirms nothing unproven hides there. So `root_soundness`'s TCB is
exactly its *visible* binders (chiefly `inputsAgree`, `bootSeed`) plus the
proof-system trust inside `AcceptedZiskTrace` and the two extraction assumptions.
The remaining readability gap `03` addresses is only that these existing binders
are loose — it bundles them, and must **not** lift the discharged fields.

## 1.4 The per-opcode multiplicity

For a single opcode (say `ADD`) the current tree has, at minimum:

| Layer | File | What it holds |
| --- | --- | --- |
| Sail bridge | `SailSpec/add.lean` | `execute_RTYPE_add_pure` etc. |
| Circuit semantics | `ZiskCircuit/Add.lean` | `add_compositional` |
| Legacy record | `Airs/Binary/BinaryAdd.lean` | `Valid_BinaryAdd` |
| Clean component | `AirsClean/BinaryAdd/{Spec,Row,Constraints,Circuit,Soundness,Bridge}.lean` | `GeneralFormalCircuit` + bridge |
| Equiv core | `EquivCore/Add.lean` | `execute … = bus_effect …` |
| Canonical equiv | `Equivalence/Add.lean` | `equiv_ADD` (thin re-export of `Compliance.equiv_ADD`) |
| Compliance wrapper | `Compliance/Wrappers/Add.lean` | `Compliance.equiv_ADD` (discharges promises) |
| Construction + arm | `Compliance/ConstructionAdd.lean`, `OpEnvelope.add` | builds the bundle |
| Trace step | `Compliance/TraceLevelExport/StepStrong*` | constructs `OpEnvelope.add` |

That is **7–9 files per opcode × ~63 opcodes**. Much of the content is
mechanical repetition differing only in an input record name and an
`instruction`/`rop`/`bop` constructor. This is the core extensibility tax:
supporting a new instruction, or changing a shared convention, is an O(opcodes)
edit across O(layers) directories.

Note also the naming near-collision: `EquivCore/<Op>.lean` and
`Equivalence/<Op>.lean` are *different* files with *different* theorems (core
`execute = bus_effect` vs canonical channel-balance form), and the `README.md`
inside `EquivCore/` actually describes `Equivalence/` (see `05`). Two directories
one letter apart, each with a per-opcode file, is a standing source of confusion.

## 1.5 Dependency direction is inverted relative to the docs

`EquivCore/README.md` and `Compliance/README.md` describe the chain as
"`Wrappers/<Op>` wraps the canonical `Equivalence/<Op>`". The code is the other
way: `Equivalence/Add.lean` `import`s `Compliance.Wrappers.Add` and its
`equiv_ADD` is `exact ZiskFv.Compliance.equiv_ADD …`. So `Equivalence/` is a thin
*re-export layer on top of* `Compliance/Wrappers/`, not the base the wrappers
build on. Either the docs or the layering should change; today they disagree,
which is exactly the kind of thing that erodes auditor trust.

## 1.6 Summary of structural problems

- **S1** Two root soundness statements, stacked; TCB split across a statement
  and the internal `OpEnvelope` fields.
- **S2** Two circuit models (`Airs` records vs `AirsClean` Clean), bridged
  per-opcode; the idiomatic model is the *tributary*, not the spine.
- **S3** 7–9 near-parallel per-opcode layers; O(opcodes×layers) edits to extend.
- **S4** Bespoke promise/trust-ledger discipline standing in for Clean's
  ensemble soundness.
- **S5** Doc/code drift (dependency direction, counts, "sum type" vs conjunction,
  headline theorem identity).
