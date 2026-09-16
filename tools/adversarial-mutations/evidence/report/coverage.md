
### How much of the extraction any theorem names

`constraint_<i>_every_row` is the generated form of pilout constraint `i`. This
counts, per AIR, how many of them appear anywhere under `ZiskFv/`.

| AIR | constraints emitted | named by a `ZiskFv` theorem | |
|-----|--------------------:|----------------------------:|--:|
| `Main` | 144 | 38 | 26% |
| `Arith` | 65 | 49 | 75% |
| `Binary` | 14 | 7 | 50% |
| `BinaryAdd` | 9 | 4 | 44% |
| `BinaryExtension` | 8 | 0 | 0% |
| `Mem` | 34 | 34 | 100% |
| `MemAlign` | 40 | 33 | 82% |
| `MemAlignByte` | 16 | 10 | 62% |
| `MemAlignReadByte` | 10 | 4 | 40% |
| `MemAlignWriteByte` | 15 | 7 | 46% |
| **total** | **355** | **186** | **52%** |

The unnamed 48 % are mostly the challenge-mixing (`gsum` / logUp) constraints that
carry the bus tuples, plus all of `BinaryExtension`. They are elaborated by
`lake build` — a syntax error in them would still break the build — but no theorem
relates them to anything, which is why a mutation inside one can be missed.
`Extraction.Buses` and `Extraction.MemoryBuses` are weaker still: `lakefile.toml`
does not even list them in the `Extraction` library's `globs`, so Lean never reads
them at all.
