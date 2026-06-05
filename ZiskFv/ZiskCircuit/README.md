# `ZiskFv/ZiskCircuit/`

Per-opcode **lifted ZisK circuit semantics**. One file per RV64IM
opcode (62 files total — 63 opcodes plus shared infrastructure;
some opcodes share a file). Each file composes the relevant
`Airs/<AIR>` pieces via the operation-bus abstraction
(`Airs/OperationBus/OperationBus.lean::matches_entry`) and concludes
that the involved AIR rows together produce `f(inputs)` for some
`BitVec` function `f` matching the RISC-V semantics.

The math here stays in `Fin p` (the Goldilocks field); the BitVec-
to-Sail-state lift itself happens in `Equivalence/<Op>.lean`. Files
are organised **by RISC-V opcode**, not by AIR — `Add.lean` projects
out the Add behaviour from `Airs/Main/Main.lean` +
`Airs/Binary/BinaryAdd.lean`, both joined by their matching bus row.

## Notable shared files

- **`MemModel.lean`** — bridges byte-addressed Mem-AIR provider rows tagged
  `wr=0` to Sail's byte-addressable memory model by consuming explicit
  `MemTrace.MemoryTraceAgreement`. No source axiom is declared here.
- **`LoadDerivation.lean`** — per-byte equality between read-entry
  and rd-write-entry bytes for the copyb family (LD, LBU, LHU, LWU),
  derived from Main's `(1 - is_external_op) * op * (b - c) = 0`
  constraint. Pure Lean, no new axioms.
- **`SextLoadBridge.lean`** — sign-extension chain for the LB/LH/LW
  family. Composes `bin_ext_table_consumer_wf` (class #6) +
  `binary_extension_sext_{b,h,w}_chunks_eq_signextend_nat` (proved
  in `Airs/Binary/BinaryExtensionPackedCorrect.lean`).
- **`MulField.lean`, `DivFieldSigned.lean`** — shared field-side
  machinery for the MUL/DIV/REM families.

To audit one opcode's circuit-side: read the matching `<Op>.lean`
here, then follow its imports back into `Airs/`. The Sail side lives
in `SailSpec/<op>.lean` (lowercase); the join happens in
`Equivalence/<Op>.lean`.
