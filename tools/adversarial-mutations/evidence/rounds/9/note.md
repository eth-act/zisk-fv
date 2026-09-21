`b_op_or_sext` is the opcode the Binary byte lookups use for the high bytes: for
32-bit-mode operations it switches to a sign-extension opcode (`OP_SEXT_00` /
`OP_SEXT_FF`) so the upper half is filled from the sign bit. Replacing the
`OP_SEXT_00` base with `OP_ADD` makes the high-byte lookups ask the table about
an addition instead of a sign extension, which is exactly the class of bug that
silently corrupts `*W` instruction results.
