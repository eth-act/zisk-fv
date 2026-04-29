● Sure. Skipping the formalism:

The core mismatch they fix

ZisK's circuit doesn't compute with regular numbers. It computes inside a finite field —
every operation is taken modulo a fixed huge prime called GL_prime (about 2⁶⁴, but slightly
less). RISC-V instructions, on the other hand, are specified using regular 64-bit integers
(with mod 2^64 for unsigned, or two's-complement sign tricks for signed).

Those two universes happen to agree for most operations as long as no quantity in the proof
ever overflows GL_prime. As soon as something does overflow, the field's mod GL_prime and
the integer's "regular math" disagree, and any proof that ignores this is wrong.

So we always need a bridge that says:

▎ "Even though the circuit computed in the field, here's why the answer the RISC-V spec
▎ wants is the same as what the field gave us."

That bridge is what the toolkits do.

The additive no-wrap toolkit (already shipped, in finishing1)

For addition, the bridge is easy. If you're adding two 64-bit chunks that are each below
2⁶⁴, their sum is below 2⁶⁵ — still way below GL_prime², well within "no wrap" territory. So
the toolkit's job is just to formally say:

▎ "The field tells you a + b = c (mod GL_prime). Each of a, b, c is bounded. Therefore the
▎ same equation holds as plain integers."

That's it. About 50 lines of Lean. It's been our workhorse for everything additive (ADD,
SUB, ADDW, SUBW, AND/OR/XOR, shifts, compares) — once you can lift one field equation to a
Nat equation, the rest is BitVec algebra.

The multiplicative no-wrap toolkit (finishing4 builds this)

For multiplication, "no wrap" is dead on arrival. Two 64-bit numbers can multiply to a
128-bit product, which wraps around GL_prime many billions of times over. You can't just say
"no wrap, use directly."

The fix: don't multiply in one shot. Break each input into four 16-bit chunks. Multiply
chunks pairwise (16 × 16 = at most 32 bits, stays small). Then do schoolbook long
multiplication as a carry chain — 16 small chunk-products feeding into 8 output chunks, with
carries between them.

So the toolkit says:

▎ "Here are the 16 individual chunk-product equations the field gave you. Here are the 8
▎ carry equations linking them. Each one stays small enough to be no-wrap. Stitch them
▎ together and you get the integer equation a × b = c (mod 2^64) + d · 2^64, with c being
▎ the low 64 bits and d being the high 64 bits."

It's about 10× more proof code than the additive case because the "stitching" — proving that
16 small no-wrap arguments compose into one big multiplication identity — is fiddly. But
mathematically it's the same idea: zoom in until everything stays inside the no-wrap zone,
then assemble.

After the toolkit lands, every multiplicative proof (MUL, MULHU, DIVU, REMU, MULW) becomes a
thin wrapper: "use the toolkit, then translate the integer equation into the BitVec
equation the RISC-V spec wants." Each opcode is then a couple hundred lines instead of
needing custom carry-chain reasoning per opcode.

The signed-BitVec.toInt extension (finishing4 also builds this)

So far we've talked about unsigned multiplication. RISC-V also has signed versions (MULH,
DIV, REM and their W-variants). For those, "negative" is encoded in two's complement: the
same 64 bits, but bit 63 means "subtract 2⁶³ from the natural-number reading." This is the
BitVec.toInt interpretation.

ZisK's circuit doesn't directly compute signed math — fields don't have signs. Instead it
carries three boolean witness columns alongside the result: na (was input A negative?), nb
(was input B negative?), np (was the product negative?). It then multiplies the absolute
values and uses these flags to decide whether to flip the sign at the end.

The signed-BitVec.toInt extension says:

▎ "Given the unsigned chunk identity from the multiplicative toolkit, plus the three sign
▎ witnesses, plus the four-quadrant case analysis (positive·positive, positive·negative,
▎ negative·positive, negative·negative), the answer agrees with the RISC-V signed-multiply
▎ spec."

It also has to handle one nasty edge case: INT_MIN / -1. In two's complement, INT_MIN =
-2⁶³, but +2⁶³ doesn't fit in 64 signed bits. RISC-V's spec says "in this case, return
INT_MIN." The proof needs to specifically catch and handle this overflow.

The bottom line

You can think of both toolkits as calculator chips for the proof:

- Additive toolkit (already shipped): "add two 64-bit numbers from the field, get the
  integer answer." Mounted into every additive opcode proof since finishing1.
- Multiplicative toolkit (finishing4 ships): "multiply two 64-bit numbers from the field,
  get the 128-bit integer answer split into low and high halves." Mounts into MUL/DIV/REM
  proofs.
- Signed extension (finishing4 ships): "given the unsigned answer plus sign witnesses, get
  the signed integer answer." Mounts into MULH/DIV/REM signed proofs.

Together they remove the last "the prover told us the right answer, take their word for it"
parameter from those 13 multiplicative opcodes. After that, the proof says "given the
circuit constraints + the toolkit, here is derived what the answer must be" — exactly the
same shape the additive opcodes have today.
