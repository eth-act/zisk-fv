This is the register-access ordering check: `b_mem_step - b_reg_prev_mem_step - 1`
must be in `0..MAX_RANGE`, which is what forces a register read to name the
*most recent* previous access rather than an arbitrary earlier one. Widening the
range by one weakens the ordering argument that the register-consistency proof
rests on.

**Missed — and this is the register-ordering argument.** Widening `MAX_RANGE` by one
changes nine constraints across four AIRs: `Main` 41 and 142, `MemAlign` 33-36 and
38, `MemAlignByte` 12, `MemAlignWriteByte` 10. (It reaches the MemAlign family
because widening one range renumbers the shared range-check ids that every AIR's
range lookups carry.) **None of the nine is named by any `ZiskFv` theorem** —
`Main` welds constraints 0-38, `MemAlign` 33 of 40, and the changed ones fall
outside every welded set.

The mutated identity is
`range_check(expression: b_mem_step - b_reg_prev_mem_step - 1, min: 0, max: MAX_RANGE, sel: b_src_reg)`,
which is what forces a register read to name the *most recent* previous access
rather than an arbitrary earlier one. That is the same ordering argument the
register-consistency work depends on, so this is the most load-bearing of the
missed rounds. It is in scope for single-segment RV64IM: `main.pil:334` is the **per-row**
register-ordering check, not `main.pil:447`'s per-register boundary check. What
blocks it is that the provider side does not exist — `SpecifiedRanges` is an
absent-AIR result in `LookupWiring`, with no extracted constraint family and no
component in the ensemble — so tying these tuples buys nothing until #19 lands.
`trust/trusted-base.md:896` disclaims the access-ordering *claim*; it does not
put the area out of scope.
