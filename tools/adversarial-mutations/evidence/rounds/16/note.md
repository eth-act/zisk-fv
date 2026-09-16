Same defect class as round 7, on the byte lookups that use the sign-extension
opcode: this time `free_in_b[i]` and `free_in_c[i]` are transposed, so the
lookup treats the *result* byte as the second operand and vice versa.

**Missed.** The swap changes `Binary` constraints 8 and 9. `BinaryMirrorWeld`
welds `Binary` constraints 0-6 and `Binary/Wiring.lean` covers constraint 10;
constraints 7-9 and 11-13 are named nowhere under `ZiskFv/`. Those six are the
byte-table lookup tuples, so the operand ordering the `BinaryTable` sees is
unconstrained by any theorem.
