Not a test. `col witness bits(n)` does not emit a constraint: pil2-compiler turns
it into a `witness_bits` **hint** (`processor.js:1697-1707`), which is
witness-generation metadata. Widening it therefore cannot change the circuit, and
the polynomial normal form of every extracted AIR is unchanged. Range enforcement
in ZisK comes from explicit `range_check(...)` calls, which round 27 mutates
instead.
