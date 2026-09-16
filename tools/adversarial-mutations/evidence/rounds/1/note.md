`a_src_mem` selects "operand A comes from memory" in ZisK's Main state machine.
The identity is its booleanity. With `1 + a_src_mem` the admissible set becomes
`{0, p-1}` instead of `{0, 1}`, so a prover can pick `a_src_mem = p-1` and every
downstream expression that multiplies by it is scaled by `-1` rather than gated.
A flag that stops being boolean is the canonical soundness bug in an AIR.
