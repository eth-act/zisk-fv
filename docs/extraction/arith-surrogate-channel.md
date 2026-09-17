# Arith surrogate-channel ownership

W12 models bus 330 on the shared physical `Arith` AIR row, represented in the
Clean tree by `ArithMulRow`.  `ArithDivRow` is a second named view of those same
44 stage-1 columns, not a second PIL AIR and therefore not a second source of
range interactions.  The consumer wiring belongs to `ArithMul`; both operation
families continue to obtain their row facts through the shared full component.

The historical half-block candidate `92bbb1e3` is a false start as a branch: it
does not elaborate against the current Clean API and fails the semantic trust
gate.  Its useful data-side idea is already present in the maintained
`RangeTables.arithRangeTable`, with the upstream 68-half-block layout and carry
region represented constructively.  W12 reuses that maintained table through a
typed bus-330 provider model instead of reviving the historical branch.  This
workstream deliberately does not register bus 330 as a finished ensemble
channel: the shared Arith component does not yet expose those consumer
interactions, so doing so here would overstate composition.

`ArithMul.RangeWiring` retains the generated c49--c60 and c63 links as one
audited range packet, the existing c61 operation link, c62's direct generated
recurrence, and c64's final-row link.  c52 is deliberately mixed: its bus-330
range tuple uses the surrogate provider, while its bus-331 tuple is the
existing local `ArithTable` lookup.  The generated ledger therefore reports
Arith at 0 exposed-to-build and 0 exposed-to-root, while recording all 13
range-linked constraints as tied-not-composed.  The tie count is intentional:
it distinguishes kernel-checked extraction wiring from a future live consumer
composition.
