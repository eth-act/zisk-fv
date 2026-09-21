`bus_res0` is the low half of the *result* ZisK publishes on the operation bus
for an Arith row: `secondary * (d[0] + d[1] * CHUNK_SIZE) + …`. Swapping `d[0]`
and `d[1]` transposes the two 16-bit limbs, so the value announced to the rest of
the machine is the byte-swapped remainder. Limb transposition in a bus tuple is a
classic silent-corruption bug.

**Missed.** The swap changes exactly `Arith` constraint 61, and `ArithMirrorWeld`
names 49 of Arith's 65 constraints — 61 is not among them. Constraint 61 is the
challenge-mixing constraint that carries Arith's operation-bus tuple, so the two
16-bit limbs of the result ZisK announces to the rest of the machine can be
transposed without any theorem objecting. Same family as round 32: the row
equations of an AIR are welded, the bus tuple it publishes is not.
