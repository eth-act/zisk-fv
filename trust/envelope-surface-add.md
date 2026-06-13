# ADD envelope surface and LD survey

This note records the concrete surface used by
`trust/consistency/global_theorem_instantiation_add.lean` and the adjacent
LD audit requested by issue #74.

## ADD concrete instantiation

| Surface | Concrete evidence |
|---------|-------------------|
| `OpEnvelope` arm | `OpEnvelope.add_via_binary` |
| Pure input | `r1_val = 0#64`, `r2_val = 0#64`, `rd = 0`, `PC = 0#64` |
| Sail registers | Default state with `PC` inserted as `0#64`; `x0` sources read as zero |
| Main row pins | `is_external_op = 1`, `op = OP_ADD`, `m32 = 0`, `store_pc = 0` |
| Main value lanes | `a_0/a_1/b_0/b_1/c_0/c_1/flag = 0` |
| Binary provider | `staticLookupComponent`, one table row backed by `binaryAddZeroRow` |
| Binary table indices | `block10` for bytes 0-6 and `block10 + 2^16` for byte 7 |
| Binary row facts | `Binary.Spec`, eight `StaticBinaryTableSpecFacts`, `binaryRowA64 = 0#64`, `binaryRowB64 = 0#64` |
| Operation bus | Main row matches Binary row message at multiplicity `1` |
| Execution bus | Consumer `(multiplicity = -1, pc = 0, timestamp = 0)`, producer `(1, 4, 1)` |
| Memory bus | Register reads `e0/e1` are consumers in address space `1`; register write `e2` is producer in address space `1` |
| R-type promises | Source reads, `rd`, `PC`, next-PC, bus lengths, multiplicities, address spaces, and write-register index close by reduction |
| Global theorem gates | `aeneasBridgeTrust`, non-load `memoryTimelineEvidence`, and `Defects.NoKnownDefect` close for this envelope |

The checked theorem is:

```lean
theorem global_theorem_instantiation_add :
    addZeroEnv.exec_eq
```

It is obtained by applying
`ZiskFv.Compliance.zisk_riscv_compliant_program_bus` to the concrete ADD
envelope and the three theorem-side gates above. The file uses explicit finite
row reductions (`rfl`, `simp`, `norm_num`) and does not introduce a new axiom,
`sorry`, or `native_decide`.

## ADD bucket findings

| Bucket | Finding |
|--------|---------|
| (a) Reducible constants and constructors | The concrete ADD envelope is constructible from existing row builders, `validOfRow`, `Environment.fromArray`, and the global theorem constructor surface. |
| (b) Explicit table and bus evidence | The Binary static table membership and Main/Binary operation-bus match are explicit checked facts in the witness file. |
| (c) Blockers | No ADD-specific blocker was found. The ADD arm is non-load, outside the signed multiplication, signed division/remainder, and FENCE defect predicates, and its memory-timeline gate reduces to `True`. |

## LD survey

| Surface | Required LD evidence |
|---------|----------------------|
| `OpEnvelope` arm | `OpEnvelope.ld` plus the `ldOfExtractedShape` wrapper route |
| Main row pins | Load opcode pins, address lanes, destination lanes, and `m32`/mode facts for the selected LD row |
| Mem provider | A concrete `Valid_Mem` row linked to the Main memory messages, including `mem.sel = 1` and `mem.wr = 0` |
| Load promises | `LoadStructuralPromises`, `ModeRegsFull`, source register read, PC, next-PC, bus length and multiplicity facts |
| Memory bus | Read and write entries must match the Main row/provider row interaction and the selected load byte/doubleword lanes |
| Timeline gate | A nonempty `MemoryTimelineEvidence state bus.e1`, not `True` |
| Existing witness | `trust/consistency/load_byte_agreement_witness.lean` proves the accepted replay/timeline shape for one selected read, but it is not yet wired into an `OpEnvelope.ld` constructor. |

LD bucket-(c) finding: unlike ADD, the load route cannot close the global
theorem's memory-timeline gate by reduction. A concrete LD instantiation needs
accepted replay rows plus a concrete Mem provider row linked to the Main
operation and memory messages before `OpEnvelope.ld` can be built. This is the
remaining LD surface for the follow-on instantiation PR.
