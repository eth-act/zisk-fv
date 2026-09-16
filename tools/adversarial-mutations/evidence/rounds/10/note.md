MemAlign proves an unaligned access by pairing a "prove" side and an "assume"
side of the same permutation with disjoint selectors, and `value[i]` is the
witness that carries whichever side is active into the memory-bus tuple. Swapping
`value[i]` and `assume_val[i]` re-points the emitted tuple at the wrong operand,
so the value the memory bus sees is no longer the value the alignment argument
established.
