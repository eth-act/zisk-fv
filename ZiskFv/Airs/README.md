# `ZiskFv/Airs/`

The **per-AIR layer**. ZisK's circuit is a collection of AIRs
(Algebraic Intermediate Representations) — `Main`, `Binary`,
`BinaryAdd`, `BinaryExtension`, `Arith`, `Mem`,
`MemAlign{,Byte,ReadByte,WriteByte}`. The pilout-extracted constraint
definitions live in the **separate** `Extraction` Lake library under
`build/extraction/Extraction/<AIR>.lean` (anonymous
`constraint_N_every_row` predicates over witness columns). This layer
wraps them with human-readable named bridges and proves single-AIR
correctness facts.

For each AIR, this directory provides:

- a **`Valid_<AIR>` structure** naming each column (so `m.cout_1 row`
  instead of `Circuit.main circ (column := 9) (row := row) (rotation := 0)`),
  with `_def` lemmas tying the names back to the anonymous accessors
  in `Extraction.<AIR>`;
- **iff-bridges** that turn each anonymous `constraint_N_every_row`
  into a meaningfully-named predicate (e.g. `core_every_row` for
  BinaryAdd's carry chain);
- **single-AIR correctness theorems** — proofs that one AIR's
  constraints imply the BitVec relation they claim. The heaviest
  files: `Binary/BinaryPackedCorrect.lean` (~2,100 lines),
  `Binary/BinaryExtensionPackedCorrect.lean` (~2,800).

## Layout

```
Airs/
├── Main/, Binary/, Arith/             named wrappers + correctness theorems per AIR
├── Mem.lean, MemAlign*.lean
├── MemoryBus/, OperationBus/          bus-protocol soundness (permutation arguments)
├── Bus/                               bus-emission ADT + generic Interaction structure
├── Tables/                            Binary + BinaryExtension lookup-table soundness
├── BusShape.lean, BusHypotheses.lean  Main operation-bus shape + structural hypotheses
└── OpBusEffect.lean, OpBusHypotheses.lean   bus-effect shape on the operation bus
```

Files are organised **by ZisK constraint table**, not by RISC-V
instruction — a single AIR (e.g. `Binary`) covers many opcodes (ADD,
SUB, AND, OR, XOR, branches, …). To find which AIR backs a given
opcode, read the matching `ZiskCircuit/<Op>.lean` and follow its
imports.

## Historical axiom-bearing files

Most AIR-side soundness axioms have been retired by the Clean/static routes.
Use `trust/generated/baseline-axioms.txt` and `trust/generated/axiom-index.md` for the current
live ledger; this directory now mostly contains definitions and proved bridges.

There are currently no project source axioms in the generated live ledger.

The allowlist of files permitted to declare trust-surface constructs
is `trust/allowed-axiom-files.txt`; see `trust/trusted-base.md`
for the current per-class breakdown.
