
---

## Should each miss have been caught?

“Missed” and “should have been caught” are different claims. A miss matters only
if the mutated element is something the **model asserts about ZisK** and that
`root_soundness` then leans on. The test below is mechanical: is the mutated
constraint represented in a module inside the import closure of
`ZiskFv.Soundness`, and is that representation tied to the extraction by anything?

The single number that organises the answer: `pil-extract` emits **124
`ValidatedLink`s** — lookup and bus templates it has already proved match the
generated constraint — plus **79 `constraintOnly`** entries for mixed constraints
it could not template. `ZiskFv/` consumes **6** of the 124 (`link_Binary_10`,
`link_MemAlign_36`, `link_Mem_29`–`32`) and **0** of the 79.

| AIR | mixed constraints | extractor linked | extractor could not link |
|-----|------------------:|-----------------:|-------------------------:|
| Main | 114 | 70 | 44 |
| Mem | 25 | 9 | 16 |
| Arith | 16 | 13 | 3 |
| BinaryExtension | 8 | 5 | 3 |
| MemAlignWriteByte | 8 | 3 | 5 |
| MemAlign / MemAlignByte | 7 / 7 | 6 / 6 | 1 / 1 |
| Binary | 7 | 5 | 2 |
| MemAlignReadByte | 6 | 5 | 1 |
| BinaryAdd | 5 | 2 | 3 |
| **total** | **203** | **124** | **79** |

### A · Should be caught, and the check already exists unwired — rounds 7, 16, 22

`ZiskFv/AirsClean/Binary/Circuit.lean` defines all eight byte-table messages
`lookupMessage0 … lookupMessage7`, and that module **is** in `root_soundness`’s
import closure — `ZiskFv/Soundness.lean` consumes them. So the model makes eight
concrete claims about ZisK’s `BINARY_TABLE` tuples.

`Binary/Wiring.lean` ties exactly one of them, `lookupMessage7`, to
`link_Binary_10`. The extractor **already emits** `link_Binary_7`,
`link_Binary_8`, `link_Binary_9` and `link_Binary_11` — the very constraints these
three rounds mutated — validated against its standard lookup template and consumed
by nothing.

The correspondence is exact and was not designed: rounds 4 and 25 landed on
constraint 10 and were caught; rounds 7, 16 and 22 landed on 8, 9 and 11 and were
not. **Verdict: a real fidelity gap, and the cheapest possible fix — one more
module shaped like the `Binary/Wiring.lean` that already exists.**

### B · Should be caught, but the extractor has to learn the template first — rounds 32, 38, 46

`BinaryAdd` constraint 5 and `Arith` constraint 61 are `proves_operation`
emissions on the 5000 bus. They are among the 79 the extractor emits as
`constraintOnly_*` with no validated template, and it says so in its own manifest:
`airStatus_BinaryAdd.unlinkedMixedConstraintCount = 3`,
`airStatus_Arith.unlinkedMixedConstraintCount = 3`.

Meanwhile the model supplies the tuple itself — `AirsClean/BinaryAdd/Bridge.lean:62`
hard-codes `op := 10`, and `ArithMul`/`ArithDiv` `Bridge.lean` build the Arith bus
message — and both modules are inside `root_soundness`’s closure.

Half of this is already written down: `docs/extraction/air-inventory.md` marks
`Buses.lean` and `MemoryBuses.lean` **“No consumer”**. What is not written down is
the consequence — that the model’s substitute tuple is therefore an unchecked
claim about ZisK. **Verdict: a real fidelity gap; closing it needs extractor work
(a `proves_operation` template) before a weld can exist.**

### C · Should be caught, and this one is a plain bug — rounds 5, 26, 33, 36

Three independent defects stack here.

1. `tools/pil-extract/src/arith_table.rs:109` emits
   `import ZiskFv.Fundamentals.Goldilocks`. That module has not existed since the
   directory restructure in `84828e96`; the correct path is
   `ZiskFv.Field.Goldilocks`, which the sibling `MemAlignRom.lean` uses.
   `Extraction.ArithTable` therefore **cannot elaborate**.
2. It is absent from `lakefile.toml`’s `Extraction` globs, which is why nobody has
   noticed. `trust/scripts/check-module-reachability.py` exists precisely to fail
   on modules `lake build` never compiles — but it walks `ZiskFv/` only and never
   looks at `build/extraction/`.
3. The data reaches the proof by hand transcription instead:
   `ZiskFv/AirsClean/ArithTable.lean:109` holds 74 literal `#v[…]` rows whose
   docstring says “Verbatim from `build/extraction/Extraction/ArithTable.lean`”.
   That module **is** in `root_soundness`’s closure, and `ArithTableProjections`
   is what the signed-MUL defect entry relies on to derive `na = MSB(op1)`.

`docs/extraction/air-inventory.md` describes `ArithTable.lean` as “the finite
state-machine table used by Arith lookup proofs”, which overstates it: the
generated module is used by nothing. **Verdict: not a scope decision at all — a
broken artifact plus a gate that does not cover the generated library. Fix the
import, add the module to the globs, prove `rows = arith_table` by `decide`, and
extend the reachability gate to `build/extraction/`.**

### D · Should be caught, but blocked on a provider that does not exist — round 27

I first recorded this as a documented scope exclusion. That was wrong, and the
correction matters.

The round mutates `main.pil:334` — the **per-row** register-ordering check
(`b_mem_step - b_reg_prev_mem_step - 1`), not `main.pil:447`, which is the
per-register boundary check. Per-row register ordering is single-segment RV64IM
and is squarely in scope.

`trust/trusted-base.md:896` does say *"This slice does **not** claim
register/memory access-ordering soundness."* That disclaims the **claim**, which
is a statement about what is currently proved. It does not put the area out of
scope. Register ordering is tracked as in-scope missing work at #330, #19 and
#348.

What genuinely blocks it is narrower and more concrete than a scope decision.
The mutation changes nine constraints across four AIRs, all of them range-check
lookups on buses 102, 103, 106 and 107. Tying those tuples buys nothing on its
own, because **the provider side is not in the ensemble**: `SpecifiedRanges` is
an explicit absent-AIR result in `LookupWiring`, with no extracted constraint
family and no live Clean component. Clean's `RawChannel.Consistent` applies only
once *both* interaction sides participate in a balanced ensemble, and
`PLAN_S3_LOOKUP_WIRING.md` records that a detached `Table.fromStatic` lookup
substituted for the missing provider would itself be laundering.

There is also a mechanical reason the mutation cannot move the proof today. The
Lean register-ordering argument comes from `Air.Flat.BalancedInteractions` being
**message-exact** plus timestamp separation mod 4
(`trust/trusted-base.md:784-816`), not from ZisK's range checks. No `MAX_RANGE`
and no `*_reg_prev_mem_step` ordering constraint appears anywhere under
`ZiskFv/`.

**Verdict: in scope, correctly missed today, and blocked on #19 rather than on
wiring.** Worth recording that proof and circuit establish ordering by
*different* mechanisms, so the Lean side offers no coverage of the circuit's.

### Summary

| disposition | rounds | count |
|---|---|--:|
| should be caught — check exists, unwired | 7, 16, 22 | 3 |
| should be caught — needs a `proves_operation` template first | 32, 38, 46 | 3 |
| should be caught — broken generated module + gate blind spot | 5, 26, 33, 36 | 4 |
| should be caught — blocked on a provider that is not modelled | 27 | 1 |

**All eleven misses are fidelity gaps that should close.** None of them is a false theorem: `root_soundness`
is true of the model it is stated over. What is unchecked is whether that model is
still ZisK — and for the bus and lookup tuples, the extractor has already done most
of the work needed to check it.
