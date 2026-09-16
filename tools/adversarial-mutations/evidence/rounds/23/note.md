`cout` is the carry out of the whole 64-bit byte chain, and for the comparison
operations it *is* the result (`c = 0`, the answer is `cout`). Breaking its
booleanity lets a comparison return `p-1` where it should return 1.
