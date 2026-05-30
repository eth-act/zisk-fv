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

## Axiom-bearing files (66 of the 72 axioms live under `Airs/`)

- **`Arith/Ranges.lean`** — 35 range / table-row / Euclidean-bound
  pins (class #6b)
- **`MemoryBus/MemBridge.lean`** — 9 memory-bus emission bundles
  + lookup soundness (class #4)
- **`Binary/BinaryRanges.lean`** — 9 Binary range / per-byte / carry
  / OR-AND-XOR / W-mode pins (class #6)
- **`Binary/BinaryExtensionRanges.lean`** — 3 BinaryExtension
  shift / SEXT pins (class #6)
- **`OperationBus/Bridge.lean`** — 3 operation-bus permutation
  soundness axioms (class #4)
- **`MemoryBus/MemAlignBridge.lean`** — 2 MemAlign ROM-lookup
  + permutation axioms (class #4)
- **`Tables/{BinaryTable,BinaryExtensionTable}.lean`** — 1 + 1
  lookup-table consumer-wf axioms (class #6)
- **`MemoryBus/EntryRanges.lean`** — 1 memory-bus byte-range
  axiom (class #5b)
- **`Main/Ranges.lean`** — 1 Main range-bus axiom (class #5b)
- **`Binary/BinaryAddRanges.lean`** — 1 BinaryAdd column-range
  axiom (class #5b)

(The remaining 14 axioms are 51 transpile contracts in
`Trusted/Transpiler.lean`, 1 memory-state load bridge in
`ZiskCircuit/MemModel.lean`, and 4 platform-scope axioms in
`SailSpec/Auxiliaries.lean` — not in this directory.)

The allowlist of files permitted to declare trust-surface constructs
is `trust/allowed-axiom-files.txt`. Each axiom's docstring cites the
PIL line / Rust function it mirrors; see `docs/fv/trusted-base.md`
for the full per-class breakdown.
