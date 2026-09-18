`eq[1] = fab*a[1]*b[0] + fab*a[0]*b[1] - c[1] …` is the second limb equation of the
Arith 64-bit multiplier. Swapping `a[1]` and `b[0]` turns the first cross term into
`fab*b[0]*a[1]` — the same product — so this is another commutativity control
rather than a defect, and a passing build is the correct outcome.
