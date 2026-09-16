
---

## Findings

**35 valid mutations reached `lake build`. 24 were caught. 11 were not.**
Three further rounds were commutativity controls, and 14 attempts never became a
test (block comment, prover-only hint, compiler-rejected, or compile-time-dead
branch). Every "missed" verdict below carries, in its round entry, the list of
modules Lean actually rebuilt, so none of them is a stale-cache artifact.

### What caught the 24

| module | rounds caught | in `root_soundness`'s closure? |
|--------|--------------:|-------------------------------|
| `AirsClean/MainMirrorWeld.lean` | 9 | no |
| `AirsClean/ArithMirrorWeld.lean` | 8 | no |
| `AirsClean/BinaryMirrorWeld.lean` | 2 | no |
| `AirsClean/MemAlignMirrorWeld.lean` | 2 | no |
| `AirsClean/Binary/Wiring.lean` | 2 | no |
| `AirsClean/Mem/RangeWiring.lean` | 2 | **yes** |
| `AirsClean/MemAlignByteMirrorWeld.lean` | 1 | no |
| `AirsClean/MemAlign/Bridge.lean` | 1 | **yes** |

Twenty-one of the 24 were caught by a module that only `ZiskFv.lean` imports. The
mirror welds do their job — a dropped identity, a flipped booleanity sign, an
ungated selector, a renumbered constraint list all turn the build red, usually
with a legible `Iff.rfl` type mismatch that prints the model's predicate against
the generated one. But they are audit modules: `root_soundness` does not depend on
them, so what they defend is the repository's build, not the theorem's statement.

### The 11 misses fall into four mechanisms

| # | mechanism | rounds | evidence |
|---|-----------|--------|----------|
| 1 | **The Arith ROM table is never compiled.** `Extraction.ArithTable` is absent from `lakefile.toml`'s `globs` and imported by nothing; it could not elaborate anyway, because `pil-extract` emits `import ZiskFv.Fundamentals.Goldilocks`, a module that has not existed since `84828e96`. The model's own 74 rows are a literal transcription whose "Verbatim from …" docstring nothing checks. | 5, 26, 33, 36 | build log shows no `Built Extraction.ArithTable` |
| 2 | **Binary's byte-table lookup tuples are unwelded.** `BinaryMirrorWeld` welds `Binary` constraints 0-6; `Binary/Wiring.lean` welds constraint 10. Constraints 7-9 and 11-13 — the remaining `BINARY_TABLE` lookups — are named nowhere under `ZiskFv/`. Transposing the two operand bytes in one of them is accepted. | 7, 16, 22 | rounds 4 and 25 hit constraint 10 and *were* caught |
| 3 | **An AIR's row equations are welded; the tuple it publishes on the operation bus is not.** `Arith` constraint 61 (the bus result) and `BinaryAdd` constraint 5 (the bus opcode) are both outside every welded set. BinaryAdd can advertise `OP_SUB` while computing `a + b`; Arith can transpose the two 16-bit limbs of its announced result. The model supplies these tuples itself — `BinaryAdd/Bridge.lean:62` hard-codes `op := 10`. | 32, 38, 46 | two independent draws (38, 46) hit the same constraint |
| 4 | **Range-check ids are unwelded.** Widening `MAX_RANGE` on the register-ordering check changes nine constraints across four AIRs and not one of them is named by a theorem. This is the check that forces a register read to name the most recent previous access. | 27 | the provider side does not exist: `SpecifiedRanges` has no extracted constraint family, no live Clean component, and no provider in the ensemble (#19) |

Mechanism 4 is blocked on a missing provider rather than on wiring — see the scope note below.
Mechanisms 1, 2 and 3 are the sharper result, because there the constraint *is* extracted, *is*
compiled, and the round-trip gate confirms it arrived faithfully — it simply has
no theorem attached. `Binary` constraint 10 being welded while 11 is not is the
whole gap in one line.

### The one-line summary

The mirror welds are a real, kernel-checked defence, and they cover the row
algebra of every modelled AIR. What they do not cover is the **interface** — the
lookup and bus tuples through which the AIRs talk to each other, and the ROM data
they consult. 186 of 355 extracted constraints are named by some theorem; the 169
that are not are almost exactly that interface layer.
