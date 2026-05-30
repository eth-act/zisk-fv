# `ZiskFv/Tactics/`

**Instruction-shape archetype tactics** that drive the per-opcode
`Equivalence/<Op>.lean` proofs. The RV64IM instruction set has only
a handful of structural *shapes* (R-type ALU, I-type immediate ALU,
branch, load, store, mul, shift, sign-extend-load, R-type-W, U-type,
arith state-machine). Each archetype packages the standard
`simp` / `rewrite` cascade that closes the equivalence for one shape;
each `Equivalence/<Op>.lean` mostly **instantiates** the matching
archetype with the opcode's specific Sail-side rewrite and
`ZiskCircuit/` compositional theorem.

The 11 archetypes:

| File                              | Covers                                       |
| --------------------------------- | -------------------------------------------- |
| `ALURTypeArchetype.lean`          | ADD, SUB, AND, OR, XOR, SLT, SLTU, SLL, SRL, SRA |
| `ALUITypeArchetype.lean`          | ADDI, ANDI, ORI, XORI, SLTI, SLTIU, SLLI, SRLI, SRAI |
| `BranchArchetype.lean`            | BEQ, BNE, BLT, BLTU, BGE, BGEU               |
| `LoadArchetype.lean`              | LD, LBU, LHU, LWU (copyb family)             |
| `SignExtendLoadArchetype.lean`    | LB, LH, LW (sign-extension family)           |
| `StoreArchetype.lean`             | SB, SH, SW, SD                               |
| `MulArchetype.lean`               | MUL, MULH, MULHSU, MULHU, MULW               |
| `ShiftArchetype.lean`             | SLLW, SLLIW, SRAW, SRAIW, SRLW, SRLIW        |
| `RTypeWArchetype.lean`            | ADDW, SUBW                                   |
| `UTypeArchetype.lean`             | LUI, AUIPC                                   |
| `ArithSMArchetype.lean`           | DIV, DIVU, REM, REMU, DIVW, DIVUW, REMW, REMUW |

This is what makes 63 individual equivalence proofs feasible without
writing 63 bespoke proof scripts. To audit one archetype, read it
once, then a handful of the opcodes that share the shape — they
should all look like the same proof modulo Sail rewrite.

JAL and JALR are handled directly in `ZiskCircuit/Jal.lean` and
`ZiskCircuit/Jalr.lean`; the old internal-copyb JALR archetype was
removed when production JALR moved to the final external `OP_AND` row.

Important: the archetype files contain some helper `theorem`
declarations whose leaf name (`equiv_<OP>`) collides with the
canonical equivs in `ZiskFv/Equivalence/<Op>.lean`. They live in the
`ZiskFv.Tactics.<Shape>Archetype` namespace and are separate
declarations — the V1 trust gate's uniformity check works on the
canonical-equiv namespace only, and the V2 binder-type walk skips
this directory. They are not part of the trusted base.
