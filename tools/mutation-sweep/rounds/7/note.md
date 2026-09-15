The Binary AIR discharges each byte of a 64-bit operation by looking the byte up
in `BinaryTable` with the tuple `[.., b_op, a_byte, b_byte, carry_in, c_byte, ..]`.
Transposing the `a` and `b` byte in the tuple makes the table answer the question
for the swapped operands. For every non-commutative operation — `SUB`, `LT`,
`MIN`, the shifts — that is a wrong result accepted as correct.

**Missed, and the boundary is one constraint wide.** The swap lands in `Binary`
constraint 11, which the extractor emits into both `Binary.lean` and
`LookupWiring.lean`. Round 4's mutation landed in constraint **10** and was caught,
because `ZiskFv/AirsClean/Binary/Wiring.lean` welds exactly c10's bus-125 tuple
(`derivedTuple_Binary_10_0`, `derivedTuple_Binary_10_1`, `link_Binary_10`).
`constraint_Binary_11` is named nowhere under `ZiskFv/`, so the byte lookup it
carries is unconstrained by any theorem.
