Not a test. The swap turns `eq[2] = fab * a[2] * b[0]` into an assignment to the
witness column `a[2]`, which pil2-compiler rejects:
`Error on a,Zisk.a,Arith.a assignation: Invalid assignation at arith/pil/arith.pil:155`.
ZisK's own toolchain refuses the mutant, so it never reaches the extractor.
