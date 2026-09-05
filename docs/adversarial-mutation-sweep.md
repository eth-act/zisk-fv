# Adversarial mutation test of `zisk-fv`

**Question.** If ZisK's constraint system had a bug, would the Lean proof notice?

**Method.** Each round breaks one thing in the pinned ZisK sources, rebuilds ZisK's
own compiled artifact from that broken source, re-runs the extractor, installs the
result exactly where `nix run .#populate` installs it, and runs `lake build`. A
**caught** round is one where `lake build` fails. A **missed** round is one where the
whole proof still compiles against a ZisK that is now wrong.

## The pipeline under test

```
zisk/**/*.pil ──pil2-compiler──> zisk.pilout ──tools/pil-extract──> build/extraction/Extraction/*.lean
                                                                                  │
                                              ZiskFv/** (hand-maintained model) ──┴──> lake build
```

Mutations enter at the leftmost box, which is where a real ZisK bug would live.
Two of the twelve mutated files (`arith_table_data.rs`, `mem_align_rom.pil`) are read
by `pil-extract` straight from source rather than through the pilout, because the AIRs
they describe are virtual and absent from the pilout; those rounds skip the recompile.

## Harness and its control

* Pinned inputs: `zisk-src` @ `b632745` (flake `zisk-src`, ZisK v0.17.0),
  `pil2-compiler` v0.9.0, `pil2-proofman` v0.17.0 — the same store paths
  `nix/zisk-pilout.nix` uses.
* The three `FrequentOps` `extern_fixed_file` payloads are regenerated as zero-filled
  files of the exact declared shape instead of being rebuilt from the ZisK Rust
  workspace. `FrequentOps` is a virtual lookup table that contributes no polynomial
  identity to any extracted AIR.
* **Control (round 0).** Compiling the *unmutated* pinned tree with those stub payloads
  and re-extracting yields Lean output that is **byte-identical** to the pinned
  `nix run .#populate` extraction. So any Lean delta a round reports is caused by the
  mutation and by nothing else in the harness.
* **Control 2.** `zisk.pilout` is *not* byte-reproducible: two compiles of the identical
  pinned source differ in 4.3 M of 4.4 M bytes and even in length. Both of them extract
  to the same byte-identical Lean, and the polynomial normal form of every constraint in
  the ten extracted AIRs agrees. So pilout bytes are not evidence of a circuit change,
  and the report never uses them as such — it uses the polynomial normal form instead.
* Baseline: `lake build` at `c031ac03` is green (9172 jobs, 6m33s).
* Each round also runs the repository's own extraction gate,
  `tools/pilout-roundtrip/check.py`, which decides for every polynomial identity in the
  pilout whether the emitted Lean is the same polynomial. It passing on a mutated round
  is the statement *"the extractor faithfully carried the bug into Lean"* — it is not a
  soundness check, and it is the reason a missed round cannot be blamed on the extractor.

## Mutation operators

Sites are enumerated mechanically from the twelve in-scope ZisK source files and
sampled uniformly (seed `20260904` for rounds 1-32, seed `20260905` for the
replacement rounds 33-44). The operators are the ways a
constraint system silently goes wrong:

| operator | what it does |
|----------|--------------|
| `DROP_CONSTRAINT` | deletes one polynomial identity |
| `CONST_PERTURB` | wrong limb weight `2**k`, wrong witness width `bits(n)`, wrong hex mask |
| `SIGN_FLIP` | flips one additive sign inside an identity |
| `OPERAND_SWAP` | transposes two indexed column reads |
| `SELECTOR_WEAKEN` | ungates a conditional identity |
| `ROW_OFFSET` | reads the current row where ZisK reads the next |
| `RANGE_WIDEN` | widens a declared range by one |
| `OPCODE_SWAP` | tags an operation-bus tuple with the wrong opcode |
| `TABLE_ROW_EDIT` | corrupts one row of a lookup table read from Rust source |

## How a round is judged

A round only tests the proof if the mutation actually changed ZisK. Three
mechanical checks decide that, before any verdict is given:

1. **Polynomial normal form.** `harness/semdiff.py` reuses the repository's own
   `pilout_wire` / `pilout_atoms` / `poly` modules to expand every constraint of the ten
   extracted AIRs, in the pilout's own algebra, and compares the base and mutated
   pilouts monomial by monomial. `a*b -> b*a` is *not* a change; a flipped sign is.
2. **Extraction delta.** Whether any generated Lean file changed at all.
3. **The extractor's own gate.** `tools/pilout-roundtrip/check.py`, run on the mutated
   pair, so a missed round cannot be blamed on a lossy extractor.

Rounds that fail check 1 are reported as controls or as non-tests, never as findings.

**On the `lake build` times in the table.** Rounds are chained: each installs its
own extraction over the previous round's and rebuilds incrementally, so a round
that follows a failing round starts from a partly-unbuilt tree and finishes in
seconds. The times measure the harness, not the mutation. Only the exit code is
evidence.


## Scoreboard

| | |
|---|---|
| rounds attempted | 52 |
| **valid mutations** (ZisK's compiled circuit or an extractor-read table really changed) | **35** |
| of those, tested against `lake build` | 35 |
| **caught** — `lake build` fails | **24** |
| **missed** — `lake build` still succeeds | **11** |
| commutativity controls (polynomial unchanged; a pass is correct) | 3 |
| not a test (block comment, prover hint, compiler-rejected, equivalent) | 14 |

| # | AIR | operator | site | mutation | class | extraction delta | round-trip | `lake build` | verdict |
|--:|-----|----------|------|----------|-------|------------------|-----------|--------------|---------|
| 1 | Main | `SIGN_FLIP` | `main.pil:468` | '-' -> '+' at col 19 | VALID | Main | pass | exit 1 (212s) | **CAUGHT** |
| 2 | Binary | `CONST_PERTURB` | `binary.pil:44` | mask 0x18 -> 0x17 | INVALID | none | — | — | not a test |
| 3 | Arith | `CONST_PERTURB` | `arith.pil:18` | witness width bits(16) -> bits(17) | INVALID | none | — | — | not a test |
| 4 | Binary | `CONST_PERTURB` | `binary.pil:156` | mask 0x10 -> 0xf | VALID | Binary, Buses, LookupWiring | pass | exit 1 (562s) | **CAUGHT** |
| 5 | ArithTable | `TABLE_ROW_EDIT` | `arith_table_data.rs:105` | table row last field 2 -> 3 | VALID | ArithTable | pass | exit 0 (517s) | **MISSED** |
| 6 | Arith | `OPERAND_SWAP` | `arith.pil:170` | swap a[1] <-> b[3] | SYNTACTIC | Arith | pass | exit 1 (15s) | control |
| 7 | Binary | `OPERAND_SWAP` | `binary.pil:115` | swap free_in_a[0] <-> free_in_b[0] | VALID | Binary, LookupWiring | pass | exit 0 (613s) | **MISSED** |
| 8 | MemAlignRom | `OPERAND_SWAP` | `mem_align_rom.pil:231` | swap tsize[1] <-> tsize[3] | EQUIVALENT | none | — | — | not a test |
| 9 | Binary | `OPCODE_SWAP` | `binary.pil:111` | opcode OP_SEXT_00 -> OP_ADD | VALID | Binary | pass | exit 1 (540s) | **CAUGHT** |
| 10 | MemAlign | `OPERAND_SWAP` | `mem_align.pil:187` | swap value[i] <-> assume_val[i] | VALID | MemAlign | pass | exit 1 (20s) | **CAUGHT** |
| 11 | Arith | `OPERAND_SWAP` | `arith.pil:145` | swap eq[2] <-> a[2] | REJECTED | none | — | — | not a test |
| 12 | Main | `DROP_CONSTRAINT` | `main.pil:473` | delete the identity | VALID | LookupWiring, Main | pass | exit 1 (536s) | **CAUGHT** |
| 13 | Main | `CONST_PERTURB` | `main.pil:95` | witness width bits(32) -> bits(33) | INVALID | none | — | — | not a test |
| 14 | MemAlign | `DROP_CONSTRAINT` | `mem_align.pil:142` | delete the identity | VALID | LookupWiring, MemAlign | pass | exit 1 (114s) | **CAUGHT** |
| 15 | MemAlignByte | `SIGN_FLIP` | `mem_align_byte.pil:37` | '-' -> '+' at col 20 | VALID | MemAlignByte, MemAlignReadByte, MemAlignWriteByte | pass | exit 1 (115s) | **CAUGHT** |
| 16 | Binary | `OPERAND_SWAP` | `binary.pil:122` | swap free_in_b[i] <-> free_in_c[i] | VALID | Binary, LookupWiring | pass | exit 0 (499s) | **MISSED** |
| 17 | Mem | `CONST_PERTURB` | `mem.pil:365` | witness width bits(40) -> bits(41) | INVALID | none | — | — | not a test |
| 18 | BinaryExtension | `CONST_PERTURB` | `binary_extension.pil:65` | mask 0x77 -> 0x76 | INVALID | none | — | — | not a test |
| 19 | MemAlign | `CONST_PERTURB` | `mem_align.pil:96` | witness width bits(3) -> bits(4) | INVALID | none | — | — | not a test |
| 20 | Arith | `DROP_CONSTRAINT` | `arith.pil:98` | delete the identity | VALID | Arith, LookupWiring | pass | exit 1 (488s) | **CAUGHT** |
| 21 | Arith | `OPERAND_SWAP` | `arith.pil:207` | swap eq[index] <-> carry[index-1] | SYNTACTIC | Arith | pass | exit 1 (496s) | control |
| 22 | Binary | `OPERAND_SWAP` | `binary.pil:122` | swap free_in_a[i] <-> free_in_b[i] | VALID | Binary, LookupWiring | pass | exit 0 (512s) | **MISSED** |
| 23 | Binary | `SIGN_FLIP` | `binary.pil:83` | '-' -> '+' at col 14 | VALID | Binary | pass | exit 1 (528s) | **CAUGHT** |
| 24 | Arith | `SIGN_FLIP` | `arith.pil:216` | '-' -> '+' at col 12 | VALID | Arith | pass | exit 1 (11s) | **CAUGHT** |
| 25 | Binary | `OPERAND_SWAP` | `binary.pil:124` | swap free_in_a[i] <-> carry[i] | VALID | Binary, LookupWiring | pass | exit 1 (536s) | **CAUGHT** |
| 26 | ArithTable | `TABLE_ROW_EDIT` | `arith_table_data.rs:150` | table row last field 16 -> 17 | VALID | ArithTable | pass | exit 0 (689s) | **MISSED** |
| 27 | Main | `RANGE_WIDEN` | `main.pil:334` | range max MAX_RANGE -> MAX_RANGE + 1 | VALID | LookupWiring, Main, MemAlign, MemAlignByte, MemAlignWriteByte | pass | exit 0 (738s) | **MISSED** |
| 28 | Mem | `DROP_CONSTRAINT` | `mem.pil:375` | delete the identity | VALID | LookupWiring, Mem | pass | exit 1 (196s) | **CAUGHT** |
| 29 | Main | `SIGN_FLIP` | `main.pil:473` | '-' -> '+' at col 18 | VALID | Main | pass | exit 1 (681s) | **CAUGHT** |
| 30 | Main | `DROP_CONSTRAINT` | `main.pil:404` | delete the identity | VALID | LookupWiring, Main | pass | exit 1 (656s) | **CAUGHT** |
| 31 | BinaryExtension | `CONST_PERTURB` | `binary_extension.pil:60` | mask 0xFF -> 0xfe | EQUIVALENT | none | — | — | not a test |
| 32 | BinaryAdd | `OPCODE_SWAP` | `binary_add.pil:25` | opcode OP_ADD -> OP_SUB | VALID | BinaryAdd, Buses, LookupWiring | pass | exit 0 (632s) | **MISSED** |
| 33 | ArithTable | `TABLE_ROW_EDIT` | `arith_table_data.rs:157` | table row last field 15 -> 16 | VALID | ArithTable | pass | exit 0 (619s) | **MISSED** |
| 34 | Arith | `OPERAND_SWAP` | `arith.pil:168` | swap eq[4] <-> b[1] | REJECTED | none | — | — | not a test |
| 35 | Main | `DROP_CONSTRAINT` | `main.pil:469` | delete the identity | VALID | LookupWiring, Main | pass | exit 1 (608s) | **CAUGHT** |
| 36 | ArithTable | `TABLE_ROW_EDIT` | `arith_table_data.rs:148` | table row last field 12 -> 13 | VALID | ArithTable | pass | exit 0 (604s) | **MISSED** |
| 37 | MemAlignRom | `OPERAND_SWAP` | `mem_align_rom.pil:20` | swap tsize[0] <-> tsize[1] | EQUIVALENT | none | — | — | not a test |
| 38 | Arith | `OPERAND_SWAP` | `arith.pil:253` | swap d[0] <-> d[1] | VALID | Arith, Buses, LookupWiring | pass | exit 0 (609s) | **MISSED** |
| 39 | MemAlign | `OPERAND_SWAP` | `mem_align.pil:180` | swap prove_val[rc_index] <-> sel[_offset] | REJECTED | none | — | — | not a test |
| 40 | Main | `DROP_CONSTRAINT` | `main.pil:479` | delete the identity | VALID | LookupWiring, Main | pass | exit 1 (603s) | **CAUGHT** |
| 41 | Arith | `DROP_CONSTRAINT` | `arith.pil:77` | delete the identity | VALID | Arith, LookupWiring | pass | exit 1 (604s) | **CAUGHT** |
| 42 | Main | `SELECTOR_WEAKEN` | `main.pil:393` | selector is_external_op -> 1 | VALID | Main | pass | exit 1 (603s) | **CAUGHT** |
| 43 | Arith | `SIGN_FLIP` | `arith.pil:217` | '-' -> '+' at col 12 | VALID | Arith | pass | exit 1 (13s) | **CAUGHT** |
| 44 | Arith | `DROP_CONSTRAINT` | `arith.pil:64` | delete the identity | VALID | Arith, LookupWiring | pass | exit 1 (604s) | **CAUGHT** |
| 45 | Mem | `DROP_CONSTRAINT` | `mem.pil:215` | delete the identity | VALID | LookupWiring, Mem | pass | exit 1 (179s) | **CAUGHT** |
| 46 | Arith | `OPERAND_SWAP` | `arith.pil:254` | swap c[0] <-> c[1] | VALID | Arith, Buses, LookupWiring | pass | exit 0 (610s) | **MISSED** |
| 47 | MemAlign | `SIGN_FLIP` | `mem_align.pil:127` | '-' -> '+' at col 12 | VALID | MemAlign | pass | exit 1 (605s) | **CAUGHT** |
| 48 | Main | `SIGN_FLIP` | `main.pil:476` | '-' -> '+' at col 16 | VALID | Main | pass | exit 1 (20s) | **CAUGHT** |
| 49 | Main | `SIGN_FLIP` | `main.pil:393` | '-' -> '+' at col 11 | VALID | Main | pass | exit 1 (19s) | **CAUGHT** |
| 50 | MemAlignRom | `OPERAND_SWAP` | `mem_align_rom.pil:124` | swap OFFSET[i+1] <-> WIDTH[i+1] | EQUIVALENT | none | — | — | not a test |
| 51 | Arith | `OPERAND_SWAP` | `arith.pil:138` | swap a[1] <-> b[0] | SYNTACTIC | Arith | pass | exit 1 (13s) | control |
| 52 | Main | `SIGN_FLIP` | `main.pil:182` | '+' -> '-' at col 50 | EQUIVALENT | none | — | — | not a test |

---

## Where the generated constraints actually enter the Lean build

This is measured from the tree, and it explains every verdict above.

`lakefile.toml` compiles fourteen of the eighteen generated modules. **Four are
generated and never compiled at all**: `Buses.lean`, `MemoryBuses.lean`,
`BinaryExtension.lean` is compiled but unread, and `ArithTable.lean` /
`MemAirFacts.md` sit outside the `globs` list. Nothing downstream can react to a
change in an artifact Lean never elaborates.

Thirteen `import Extraction.*` lines exist in the whole `ZiskFv` tree, in ten
modules. Seven of those ten — the six `*MirrorWeld.lean` files and
`Binary/Wiring.lean` — are imported **only** by the root aggregator `ZiskFv.lean`.
Three are load-bearing: `Mem/RangeWiring.lean`, `MemAlign/Bridge.lean` and
`MemAlignRomTable.lean`.

The import closure of `ZiskFv.Soundness` (where `root_soundness` lives) is 637
modules and reaches exactly two generated modules: `Extraction.LookupWiring` and
`Extraction.MemAlignRom`.

Two consequences, both visible in the rounds:

1. **`lake build` is the gate, not the theorem.** A mutation to a `Main`, `Binary`,
   `Arith`, `Mem` or `MemAlign` polynomial identity is caught by a `*MirrorWeld`
   module, so the repository build goes red — which is what CI checks. But those
   welds are outside `root_soundness`'s dependency graph, so the theorem itself is
   not stated *modulo* the extraction. Deleting a weld would not change what
   `root_soundness` proves; it would only stop anyone noticing that the model had
   drifted from ZisK.
2. **Coverage is per-constraint, and the repository says so.** `BinaryMirrorWeld`
   states plainly that the Binary family emits 31 constraints and welds 11 of them;
   the other 20 are the challenge-mixing (`gsum`/logUp) constraints that carry the
   bus tuples. A mutation inside one of those 20 lands in a file the build
   elaborates but no theorem constrains.

### Two things the rounds turned up that are not about any single constraint

**`Extraction.ArithTable` cannot elaborate, and nothing notices.**
`tools/pil-extract/src/arith_table.rs:109` writes `import ZiskFv.Fundamentals.Goldilocks`
into the generated module. No such module exists — the file has been
`ZiskFv/Field/Goldilocks.lean` since the directory restructure in `84828e96`, and
`Extraction/MemAlignRom.lean` (the other generated module that needs it) imports the
correct path. `Extraction.ArithTable` is absent from `lakefile.toml`'s `globs`, so
Lean never opens it and the stale import has never surfaced. Meanwhile the model's
own copy of the same data, `ZiskFv/AirsClean/ArithTable.lean:109`, is 74 rows of
literal `#v[…]` whose docstring says "Verbatim from
`build/extraction/Extraction/ArithTable.lean`" — a claim no compiled declaration
checks, because that module is not imported anywhere either.

**`pil-extract mem-align-rom` re-implements ZisK's ROM builder rather than
extracting it.** For the virtual `MemAlignRom` AIR the extractor reads only the
`OFFSET`/`WIDTH` fixed columns, three integer constants, and a regex check on the
`lookup_proves` tuple shape; the `pc`, `delta_pc`, `delta_addr` and `flags` of all
256 rows are then computed by `build_rows` in Rust
(`tools/pil-extract/src/mem_align_rom.rs`). A defect in ZisK's own row builder
therefore cannot reach Lean — round 50 changes the access-window test in that
builder and `MemAlignRom.lean` comes out byte-identical.

### The welds are definitional, not semantic

Rounds 6 and 21 were meant as controls: each rewrites one term of an Arith identity
into a commutative image of itself (`fab*a[1]*b[3]` → `fab*b[3]*a[1]`,
`eq[i] + carry[i-1]` → `carry[i-1] + eq[i]`). The project's own polynomial normal
form says nothing changed. **Both fail the build anyway**, at
`ArithMirrorWeld.lean:372` and `:330`.

That is the welds working as designed: they are `Iff.rfl` / structure-instance
equalities against the generated term, so they pin the *syntactic form* of each
constraint, which is strictly stronger than pinning the polynomial. The practical
consequence is that a benign refactor of ZisK's PIL — reordering a product, or
re-associating a sum — turns the repository red and needs the mirrors updated by
hand. That is a maintenance cost, not a soundness gap, and it is the price of
having the mirrors checked by the kernel rather than by a comment.


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
| 4 | **Range-check ids are unwelded.** Widening `MAX_RANGE` on the register-ordering check changes nine constraints across four AIRs and not one of them is named by a theorem. This is the check that forces a register read to name the most recent previous access. | 27 | consistent with the repository's own note that `SpecifiedRanges` is not composed |

Mechanisms 1 and 4 are documented scope limits of the extraction; mechanisms 2 and
3 are the sharper result, because there the constraint *is* extracted, *is*
compiled, and the round-trip gate confirms it arrived faithfully — it simply has
no theorem attached. `Binary` constraint 10 being welded while 11 is not is the
whole gap in one line.

### The one-line summary

The mirror welds are a real, kernel-checked defence, and they cover the row
algebra of every modelled AIR. What they do not cover is the **interface** — the
lookup and bus tuples through which the AIRs talk to each other, and the ROM data
they consult. 186 of 355 extracted constraints are named by some theorem; the 169
that are not are almost exactly that interface layer.


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

### D · Known out of scope — round 27

This one is already in the ledger, twice over.

`trust/trusted-base.md:896` states plainly: *“This slice does **not** claim
register/memory access-ordering soundness.”* The same section analyses
`main.pil:447`’s `MAX_RANGE` margin down to the zero-margin case at
`main_segment = 0` and concludes: *“`447` remains genuinely unmodelled and is still
an extraction-fidelity gap.”*

There is also a mechanical reason the mutation cannot move the proof. The Lean
register-ordering argument does not come from ZisK’s range checks at all: it comes
from `Air.Flat.BalancedInteractions` being **message-exact** (`∀ msg, balanceOf
interactions msg = 0`, not a challenge-mixed sum) plus timestamp separation mod 4
(`trust/trusted-base.md:784-816`). No `MAX_RANGE`, and no
`*_reg_prev_mem_step` ordering constraint, appears anywhere under `ZiskFv/`.

**Verdict: expected miss, correctly scoped.** Worth recording, though, that the
proof and the circuit establish access ordering by *different* mechanisms — the
circuit by range check, the model by exact multiset balance — so the Lean side
offers no coverage of the circuit’s, and the ledger’s own “closed-world” caveat
(`trusted-base.md:801-806`) is what carries the weight.

### Summary

| disposition | rounds | count |
|---|---|--:|
| should be caught — check exists, unwired | 7, 16, 22 | 3 |
| should be caught — needs a `proves_operation` template first | 32, 38, 46 | 3 |
| should be caught — broken generated module + gate blind spot | 5, 26, 33, 36 | 4 |
| known out of scope, documented in the trust ledger | 27 | 1 |

**Ten of the eleven misses are fidelity gaps that should close. One is a
documented scope exclusion.** None of the ten is a false theorem: `root_soundness`
is true of the model it is stated over. What is unchecked is whether that model is
still ZisK — and for the bus and lookup tuples, the extractor has already done most
of the work needed to check it.


---

## What a passing build does and does not mean

A missed round does not mean the mutated circuit was re-verified and found sound.
Nothing read it.

**The two obligations.** A green `lake build` attests two things, and only one of
them is a Lean theorem.

1. **`model ⟹ Sail`.** This is `ZiskFv.Compliance.root_soundness`. It is proved,
   and no mutation touches it.
2. **`ZisK ⟹ model`.** This is not a theorem. It is the mirror welds, the wiring
   modules, the trust ledger and human review. **All eleven misses are in
   obligation 2.**

Mutating ZisK changes `build/extraction/Extraction/*.lean`. It does not change
`ZiskFv/**`. `root_soundness` is stated over the hand-written model, so after a
mutation it proves exactly what it proved before, from inputs that never included
the mutated constraint.

**Which way the failure runs.** The theorem does not become false — it silently
stops applying. `root_soundness` takes an `AcceptedZiskTrace`, and the model keeps
demanding the original constraint after ZisK has stopped enforcing it. So traces
the mutated machine accepts are no longer `AcceptedZiskTrace`s, the hypothesis is
unfulfillable for exactly the behaviour the mutation introduced, and the theorem
says nothing about it while continuing to look like it does. Loss of
applicability, not a false conclusion, and no signal either way.

**The narrow sense in which the mutant is “still a validly constrained circuit”.**
The model remains a coherent constraint system that implies Sail. But no new
circuit was verified: the *old* circuit kept being verified while the deployed one
drifted away from it. That distinction is the entire content of obligation 2.

**Worked example — round 32.** Mutated ZisK's `BinaryAdd` rows announce `OP_SUB`
on the 5000 bus while computing `a + b`, so a prover could discharge a `SUB`
request with an addition — and the `Binary` AIR is a second, correct `SUB`
provider, so this is an extra wrong provider for a live opcode rather than merely
an unsatisfiable circuit. On the Lean side `AirsClean/BinaryAdd/Bridge.lean:62`
still reads `op := 10`, the channel-balance argument still matches Main's `SUB`
against the `Binary` AIR, and `root_soundness` goes through — describing a machine
that no longer exists.

**What was demonstrated, and what was not.** Each missed round demonstrates that
the model stopped describing ZisK: the polynomial normal form of the named
constraint changed, `tools/pilout-roundtrip/check.py` confirms the extractor
carried that change into Lean faithfully, the build log shows Lean re-elaborated
the affected modules, and the build stayed green. **No forged proof was built
against a mutated ZisK.** That needs the prover, the way
`ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS` was demonstrated end to end under
Docker. The unsoundness of each mutant here is an argument from its constraint
change, not an executed forgery.

**The controls invert the point.** Rounds 6, 21 and 51 rewrite one term into a
commutative image of itself. The polynomial is identical — the project's own
normal form says so — and all three turn the build **red**, because the welds are
`Iff.rfl` equalities against the generated term. So the build's sensitivity
currently tracks *syntactic identity of a 52 % subset* of the extracted
constraints, not soundness. Both directions of that mismatch are worth closing:
the false negatives cost fidelity, the false positives cost maintenance every time
ZisK reorders a product.


---

## Round detail

### Round 1 — Main / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:468` — '-' -> '+' at col 19

```diff
- a_src_mem * (1 - a_src_mem) === 0;
+ a_src_mem * (1 + a_src_mem) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [24].

`a_src_mem` selects "operand A comes from memory" in ZisK's Main state machine.
The identity is its booleanity. With `1 + a_src_mem` the admissible set becomes
`{0, p-1}` instead of `{0, 1}`, so a prover can pick `a_src_mem = p-1` and every
downstream expression that multiplies by it is scaled by `-1` rather than gated.
A flag that stops being boolean is the canonical soundness bug in an AIR.

**Where it lands in the generated Lean.**

* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 212s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 2 — Binary / `CONST_PERTURB` — not a test

`zisk/state-machines/binary/pil/binary.pil:44` — mask 0x18 -> 0x17

```diff
- │ GT_W      │   0x18   │   0x08   │   X   │       X            │         │
+ │ GT_W      │   0x17   │   0x08   │   X   │       X            │         │
```

**Is this a reasonable thing to break?** the sampled line sits inside a `/* … */` block comment.

Not a test. `binary.pil:44` is a row of the ASCII opcode table inside a
`/* … */` block comment. The site enumerator was later taught to skip block
comments; rounds 33-44 are drawn from the filtered pool.

### Round 3 — Arith / `CONST_PERTURB` — not a test

`zisk/state-machines/arith/pil/arith.pil:18` — witness width bits(16) -> bits(17)

```diff
- col witness bits(16) a[CHUNKS_INPUT];
+ col witness bits(17) a[CHUNKS_INPUT];
```

**Is this a reasonable thing to break?** `bits(n)` compiles to a `witness_bits` *hint* (pil2-compiler `processor.js:1697-1707`), not a constraint.

Not a test. `col witness bits(n)` does not emit a constraint: pil2-compiler turns
it into a `witness_bits` **hint** (`processor.js:1697-1707`), which is
witness-generation metadata. Widening it therefore cannot change the circuit, and
the polynomial normal form of every extracted AIR is unchanged. Range enforcement
in ZisK comes from explicit `range_check(...)` calls, which round 27 mutates
instead.

### Round 4 — Binary / `CONST_PERTURB` — **CAUGHT**

`zisk/state-machines/binary/pil/binary.pil:156` — mask 0x10 -> 0xf

```diff
- proves_operation(op: b_op + 0x10 * mode32, a:, b:, c:, flag:cout);
+ proves_operation(op: b_op + 0xf * mode32, a:, b:, c:, flag:cout);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [10].

`b_op + 0x10 * mode32` is how the Binary AIR names the operation it proves on the
5000 bus: the 32-bit variant of an operation is its 64-bit opcode plus `0x10`.
With `0x0f` every 32-bit operation advertises the opcode of a *different*
operation (`MINU_W` 0x12 becomes 0x11, and so on), so Main's request for one
operation can be discharged by a Binary row computing another. This is the
operand-bus analogue of a mislabelled function pointer.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`
* `Buses.lean` — **not in the Lake globs; never compiled**
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 562s):

Failing module(s): `ZiskFv.AirsClean.Binary.Wiring` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/Binary/Wiring.lean:55:2: Unknown identifier `derivedTuple_Binary_10_0.slots.map`
error: ZiskFv/AirsClean/Binary/Wiring.lean:84:10: Unknown identifier `link_Binary_10`
error: ZiskFv/AirsClean/Binary/Wiring.lean:85:17: Unknown identifier `derivedTuple_Binary_10_0`
error: ZiskFv/AirsClean/Binary/Wiring.lean:86:20: Unknown identifier `derivedTuple_Binary_10_1`
error: ZiskFv/AirsClean/Binary/Wiring.lean:93:19: Type mismatch
error: Lean exited with code 1
```

### Round 5 — ArithTable / `TABLE_ROW_EDIT` — **MISSED**

`zisk/state-machines/arith/src/arith_table_data.rs:105` — table row last field 2 -> 3

```diff
- [180, 2584, 5, 2],
+ [180, 2584, 5, 3],
```

**Is this a reasonable thing to break?** lookup-table data read straight from ZisK source by the extractor.

`arith_table_data.rs` is the 74-row lookup table that tells the Arith state
machine which flag combination is legal for each opcode; the extractor parses it
straight from ZisK's Rust source into `ArithTable.lean`. Changing the last field
of a row changes the flags admitted for that opcode.

**Missed, and `Extraction.ArithTable` is never even opened.** The only generated
file that changes is `ArithTable.lean`, and `lakefile.toml` does not list
`Extraction.ArithTable` in the `Extraction` library's `globs`, so Lean never
elaborates it — the build log shows `Extraction.LookupWiring`, `Extraction.Main`
and the two Mem modules rebuilt, and no `Extraction.ArithTable`. It could not
elaborate anyway: `tools/pil-extract/src/arith_table.rs:109` emits
`import ZiskFv.Fundamentals.Goldilocks`, a module that does not exist.

The model's own copy of the same table, `ZiskFv/AirsClean/ArithTable.lean:109`, is
74 rows of literal `#v[…]` whose docstring claims they are "Verbatim from
`build/extraction/Extraction/ArithTable.lean`". Nothing compiled checks that
claim, so ZisK's table and the modelled table can drift apart silently.

**Where it lands in the generated Lean.**

* `ArithTable.lean` — **not in the Lake globs; never compiled**

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 517s).

Not a stale-cache artifact: the run rebuilt 408 jobs, among them `Extraction.LookupWiring`, `Extraction.Main`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridge`.

### Round 6 — Arith / `OPERAND_SWAP` — control

`zisk/state-machines/arith/pil/arith.pil:170` — swap a[1] <-> b[3]

```diff
- + fab * a[1] * b[3]
+ + fab * b[3] * a[1]
```

**Is this a reasonable thing to break?** the expression tree changed but the polynomial did not (commutativity) — a passing build is the correct outcome here.

This is a commutativity control, not a defect injection: `fab * a[1] * b[3]`
became `fab * b[3] * a[1]`, which is the same polynomial. The pilout expression
tree changes and so does the emitted Lean text, so the round still exercises the
whole pipeline — but the circuit is unchanged and `lake build` must pass.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 15s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:372:4: Application type mismatch: The argument
error: Lean exited with code 1
error: build failed
```

### Round 7 — Binary / `OPERAND_SWAP` — **MISSED**

`zisk/state-machines/binary/pil/binary.pil:115` — swap free_in_a[0] <-> free_in_b[0]

```diff
- lookup_assumes(BINARY_TABLE_ID, [2*use_first_byte, b_op, free_in_a[0], free_in_b[0], 0, free_in_c[0], carry[0] + 2*result_is_a + 4*use_first_byte]);
+ lookup_assumes(BINARY_TABLE_ID, [2*use_first_byte, b_op, free_in_b[0], free_in_a[0], 0, free_in_c[0], carry[0] + 2*result_is_a + 4*use_first_byte]);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [11].

The Binary AIR discharges each byte of a 64-bit operation by looking the byte up
in `BinaryTable` with the tuple `[.., b_op, a_byte, b_byte, carry_in, c_byte, ..]`.
Transposing the `a` and `b` byte in the tuple makes the table answer the question
for the swapped operands. For every non-commutative operation — `SUB`, `LT`,
`MIN`, the shifts — that is a wrong result accepted as correct.

**Missed, and the boundary is one constraint wide.** The swap lands in `Binary`
constraint 11, which the extractor emits into both `Binary.lean` and
`LookupWiring.lean`. Round 4's mutation landed in constraint **10** and was caught,
because `ZiskFv/AirsClean/Binary/Wiring.lean` welds exactly c10's bus-125 tuple
(`derivedTuple_Binary_10_0`, `derivedTuple_Binary_10_1`, `link_Binary_10`).
`constraint_Binary_11` is named nowhere under `ZiskFv/`, so the byte lookup it
carries is unconstrained by any theorem.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 613s).

Not a stale-cache artifact: the run rebuilt 410 jobs, among them `Extraction.Arith`, `Extraction.Binary`, `Extraction.LookupWiring`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.BinaryMirrorWeld`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`.

### Round 8 — MemAlignRom / `OPERAND_SWAP` — not a test

`zisk/state-machines/mem/pil/mem_align_rom.pil:231` — swap tsize[1] <-> tsize[3]

```diff
- else if (line < 1+tsize[0]+tsize[1]+tsize[2]+tsize[3]) // RWVWR
+ else if (line < 1+tsize[0]+tsize[3]+tsize[2]+tsize[1]) // RWVWR
```

**Is this a reasonable thing to break?** the mutation leaves the extracted Lean byte-identical.

Not a test. The swap is inside `line < 1+tsize[0]+tsize[1]+tsize[2]+tsize[3]`,
a sum of the same four terms in a different order, so the mutated source is the
same program. The extracted `MemAlignRom.lean` is byte-identical.

### Round 9 — Binary / `OPCODE_SWAP` — **CAUGHT**

`zisk/state-machines/binary/pil/binary.pil:111` — opcode OP_SEXT_00 -> OP_ADD

```diff
- b_op_or_sext === mode32 * (c_is_signed * (OP_SEXT_FF - OP_SEXT_00) + OP_SEXT_00 - b_op) + b_op;
+ b_op_or_sext === mode32 * (c_is_signed * (OP_SEXT_FF - OP_SEXT_00) + OP_ADD - b_op) + b_op;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [5].

`b_op_or_sext` is the opcode the Binary byte lookups use for the high bytes: for
32-bit-mode operations it switches to a sign-extension opcode (`OP_SEXT_00` /
`OP_SEXT_FF`) so the upper half is filled from the sign bit. Replacing the
`OP_SEXT_00` base with `OP_ADD` makes the high-byte lookups ask the table about
an addition instead of a sign extension, which is exactly the class of bug that
silently corrupts `*W` instruction results.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 540s):

Failing module(s): `ZiskFv.AirsClean.BinaryMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/BinaryMirrorWeld.lean:287:2: Type mismatch
error: ZiskFv/AirsClean/BinaryMirrorWeld.lean:308:2: Type mismatch
error: ZiskFv/AirsClean/BinaryMirrorWeld.lean:310:0: maximum recursion depth has been reached
error: Lean exited with code 1
error: build failed
```

### Round 10 — MemAlign / `OPERAND_SWAP` — **CAUGHT**

`zisk/state-machines/mem/pil/mem_align.pil:187` — swap value[i] <-> assume_val[i]

```diff
- value[i] === sel_prove * prove_val[i] + sel_assume * assume_val[i];
+ assume_val[i] === sel_prove * prove_val[i] + sel_assume * value[i];
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `MemAlign` constraint(s) [31, 32].

MemAlign proves an unaligned access by pairing a "prove" side and an "assume"
side of the same permutation with disjoint selectors, and `value[i]` is the
witness that carries whichever side is active into the memory-bus tuple. Swapping
`value[i]` and `assume_val[i]` re-points the emitted tuple at the wrong operand,
so the value the memory bus sees is no longer the value the alignment argument
established.

**Where it lands in the generated Lean.**

* `MemAlign.lean` — read by `ZiskFv/AirsClean/MemAlignMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 20s):

Failing module(s): `ZiskFv.AirsClean.MemAlignMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:425:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:431:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:465:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:538:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 11 — Arith / `OPERAND_SWAP` — not a test

`zisk/state-machines/arith/pil/arith.pil:145` — swap eq[2] <-> a[2]

```diff
- eq[2] = fab * a[2] * b[0]
+ a[2] = fab * eq[2] * b[0]
```

**Is this a reasonable thing to break?** ZisK's own PIL compiler refuses the mutated source.

Not a test. The swap turns `eq[2] = fab * a[2] * b[0]` into an assignment to the
witness column `a[2]`, which pil2-compiler rejects:
`Error on a,Zisk.a,Arith.a assignation: Invalid assignation at arith/pil/arith.pil:155`.
ZisK's own toolchain refuses the mutant, so it never reaches the extractor.

### Round 12 — Main / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:473` — delete the identity

```diff
- store_pc * (1 - store_pc) === 0;
+ //    store_pc * (1 - store_pc) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142], dropped [143].

`store_pc` selects "write the program counter to the destination", which is what
makes `JAL`/`JALR` save a return address. Deleting its booleanity lets a prover
choose any field element for it. The dropped constraint also renumbers every
later Main constraint, so this round doubles as a test of whether the model is
pinned to constraint *indices* as well as to constraint *content*.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 536s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:562:14: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:740:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 13 — Main / `CONST_PERTURB` — not a test

`zisk/state-machines/main/pil/main.pil:95` — witness width bits(32) -> bits(33)

```diff
- col witness bits(32) b[RC];
+ col witness bits(33) b[RC];
```

**Is this a reasonable thing to break?** `bits(n)` compiles to a `witness_bits` *hint* (pil2-compiler `processor.js:1697-1707`), not a constraint.

Not a test. `col witness bits(n)` does not emit a constraint: pil2-compiler turns
it into a `witness_bits` **hint** (`processor.js:1697-1707`), which is
witness-generation metadata. Widening it therefore cannot change the circuit, and
the polynomial normal form of every extracted AIR is unchanged. Range enforcement
in ZisK comes from explicit `range_check(...)` calls, which round 27 mutates
instead.

### Round 14 — MemAlign / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/mem/pil/mem_align.pil:142` — delete the identity

```diff
- delta_addr === (addr - 'addr) * (1 - reset);
+ //    delta_addr === (addr - 'addr) * (1 - reset);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `MemAlign` constraint(s) [29, 30, 31, 32, 33, 34, 35, 36, 37, 38], dropped [39].

`delta_addr === (addr - 'addr) * (1 - reset)` is the link between consecutive
MemAlign rows: it forces the address delta fed to the `MEMORY_ALIGN_ROM` lookup
to be the real difference between this row's address and the previous row's.
Deleting it frees `delta_addr` entirely, so a prover can present any address
progression to the ROM.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `MemAlign.lean` — read by `ZiskFv/AirsClean/MemAlignMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 114s):

Failing module(s): `ZiskFv.AirsClean.MemAlign.Bridge`, `ZiskFv.AirsClean.MemAlignMirrorWeld` — **inside** `root_soundness`'s import closure.

```
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:413:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:419:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:425:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:427:0: maximum recursion depth has been reached
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:465:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:538:2: Type mismatch
```

### Round 15 — MemAlignByte / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/mem/pil/mem_align_byte.pil:37` — '-' -> '+' at col 20

```diff
- sel_high_b * (1 - sel_high_b) === 0;
+ sel_high_b * (1 + sel_high_b) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `MemAlignByte` constraint(s) [2]; `MemAlignReadByte` constraint(s) [2]; `MemAlignWriteByte` constraint(s) [2].

`sel_high_b` is one of the three bits that reconstruct the byte offset of a
sub-doubleword access (`offset = 4*sel_high_4b + 2*sel_high_2b + sel_high_b`).
Breaking its booleanity to `{0, p-1}` lets the offset — and therefore the address
the access is charged to — take values outside `0..7`.

**Where it lands in the generated Lean.**

* `MemAlignByte.lean` — read by `ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean`
* `MemAlignReadByte.lean` — read by `ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean`
* `MemAlignWriteByte.lean` — read by `ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 115s):

Failing module(s): `ZiskFv.AirsClean.MemAlignByteMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean:323:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean:378:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean:398:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean:419:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean:450:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean:497:2: Type mismatch
```

### Round 16 — Binary / `OPERAND_SWAP` — **MISSED**

`zisk/state-machines/binary/pil/binary.pil:122` — swap free_in_b[i] <-> free_in_c[i]

```diff
- lookup_assumes(BINARY_TABLE_ID, [0, b_op_or_sext, free_in_a[i], free_in_b[i], carry[i-1], free_in_c[i], carry[i] + 2*result_is_a + 4*use_first_byte + 8*mode32_and_c_is_signed]);
+ lookup_assumes(BINARY_TABLE_ID, [0, b_op_or_sext, free_in_a[i], free_in_c[i], carry[i-1], free_in_b[i], carry[i] + 2*result_is_a + 4*use_first_byte + 8*mode32_and_c_is_signed]);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [8, 9].

Same defect class as round 7, on the byte lookups that use the sign-extension
opcode: this time `free_in_b[i]` and `free_in_c[i]` are transposed, so the
lookup treats the *result* byte as the second operand and vice versa.

**Missed.** The swap changes `Binary` constraints 8 and 9. `BinaryMirrorWeld`
welds `Binary` constraints 0-6 and `Binary/Wiring.lean` covers constraint 10;
constraints 7-9 and 11-13 are named nowhere under `ZiskFv/`. Those six are the
byte-table lookup tuples, so the operand ordering the `BinaryTable` sees is
unconstrained by any theorem.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 499s).

Not a stale-cache artifact: the run rebuilt 412 jobs, among them `Extraction.Binary`, `Extraction.LookupWiring`, `Extraction.MemAlignByte`, `Extraction.MemAlignReadByte`, `Extraction.MemAlignWriteByte`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`.

### Round 17 — Mem / `CONST_PERTURB` — not a test

`zisk/state-machines/mem/pil/mem.pil:365` — witness width bits(40) -> bits(41)

```diff
- col witness bits(40) air.previous_step;
+ col witness bits(41) air.previous_step;
```

**Is this a reasonable thing to break?** `bits(n)` compiles to a `witness_bits` *hint* (pil2-compiler `processor.js:1697-1707`), not a constraint.

Not a test. `col witness bits(n)` does not emit a constraint: pil2-compiler turns
it into a `witness_bits` **hint** (`processor.js:1697-1707`), which is
witness-generation metadata. Widening it therefore cannot change the circuit, and
the polynomial normal form of every extracted AIR is unchanged. Range enforcement
in ZisK comes from explicit `range_check(...)` calls, which round 27 mutates
instead.

### Round 18 — BinaryExtension / `CONST_PERTURB` — not a test

`zisk/state-machines/binary/pil/binary_extension.pil:65` — mask 0x77 -> 0x76

```diff
- 6    0x77      0x00000000    0x00000000
+ 6    0x76      0x00000000    0x00000000
```

**Is this a reasonable thing to break?** the sampled line sits inside a `/* … */` block comment.

Not a test — same cause as round 2, in `binary_extension.pil`.

### Round 19 — MemAlign / `CONST_PERTURB` — not a test

`zisk/state-machines/mem/pil/mem_align.pil:96` — witness width bits(3) -> bits(4)

```diff
- col witness bits(3) offset;
+ col witness bits(4) offset;
```

**Is this a reasonable thing to break?** `bits(n)` compiles to a `witness_bits` *hint* (pil2-compiler `processor.js:1697-1707`), not a constraint.

Not a test. `col witness bits(n)` does not emit a constraint: pil2-compiler turns
it into a `witness_bits` **hint** (`processor.js:1697-1707`), which is
witness-generation metadata. Widening it therefore cannot change the circuit, and
the polynomial normal form of every extracted AIR is unchanged. Range enforcement
in ZisK comes from explicit `range_check(...)` calls, which round 27 mutates
instead.

### Round 20 — Arith / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/arith/pil/arith.pil:98` — delete the identity

```diff
- div_overflow * (1 - div) === 0;
+ //    div_overflow * (1 - div) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], dropped [64].

`div_overflow * (1 - div) === 0` confines the signed-division overflow flag to
rows that are actually divisions. Deleting it lets a prover raise `div_overflow`
on a multiplication row and take the overflow branch of the Arith equations there.
This is in the neighbourhood of the already-documented signed DIV/REM defect, so
it is exactly the region where the proof should be most sensitive.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 488s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:177:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:212:11: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:247:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:279:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:286:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:291:2: Type mismatch
```

### Round 21 — Arith / `OPERAND_SWAP` — control

`zisk/state-machines/arith/pil/arith.pil:207` — swap eq[index] <-> carry[index-1]

```diff
- eq[index] + carry[index-1] - carry[index] * CHUNK_SIZE === 0;
+ carry[index-1] + eq[index] - carry[index] * CHUNK_SIZE === 0;
```

**Is this a reasonable thing to break?** the expression tree changed but the polynomial did not (commutativity) — a passing build is the correct outcome here.

Commutativity control: `eq[index] + carry[index-1]` became
`carry[index-1] + eq[index]`. Same polynomial, different tree.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 496s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:330:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:371:36: Application type mismatch: The argument
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:371:49: Application type mismatch: The argument
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:371:64: Application type mismatch: The argument
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:372:4: Application type mismatch: The argument
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:372:52: Application type mismatch: The argument
```

### Round 22 — Binary / `OPERAND_SWAP` — **MISSED**

`zisk/state-machines/binary/pil/binary.pil:122` — swap free_in_a[i] <-> free_in_b[i]

```diff
- lookup_assumes(BINARY_TABLE_ID, [0, b_op_or_sext, free_in_a[i], free_in_b[i], carry[i-1], free_in_c[i], carry[i] + 2*result_is_a + 4*use_first_byte + 8*mode32_and_c_is_signed]);
+ lookup_assumes(BINARY_TABLE_ID, [0, b_op_or_sext, free_in_b[i], free_in_a[i], carry[i-1], free_in_c[i], carry[i] + 2*result_is_a + 4*use_first_byte + 8*mode32_and_c_is_signed]);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [8, 9].

Same defect class as round 7, one lookup further down the byte chain.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 512s).

Not a stale-cache artifact: the run rebuilt 410 jobs, among them `Extraction.Arith`, `Extraction.Binary`, `Extraction.LookupWiring`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.BinaryMirrorWeld`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`.

### Round 23 — Binary / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/binary/pil/binary.pil:83` — '-' -> '+' at col 14

```diff
- cout * (1 - cout) === 0;
+ cout * (1 + cout) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [1].

`cout` is the carry out of the whole 64-bit byte chain, and for the comparison
operations it *is* the result (`c = 0`, the answer is `cout`). Breaking its
booleanity lets a comparison return `p-1` where it should return 1.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 528s):

Failing module(s): `ZiskFv.AirsClean.BinaryMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/BinaryMirrorWeld.lean:262:2: Type mismatch
error: ZiskFv/AirsClean/BinaryMirrorWeld.lean:308:2: Type mismatch
error: ZiskFv/AirsClean/BinaryMirrorWeld.lean:328:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 24 — Arith / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/arith/pil/arith.pil:216` — '-' -> '+' at col 12

```diff
- nr * (1 - nr) === 0;
+ nr * (1 + nr) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [43].

`nr` is the "remainder is negative" flag of the Arith state machine. Its
booleanity is what makes the signed division sign analysis a case split rather
than a free scaling factor.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 11s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:247:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 25 — Binary / `OPERAND_SWAP` — **CAUGHT**

`zisk/state-machines/binary/pil/binary.pil:124` — swap free_in_a[i] <-> carry[i]

```diff
- lookup_assumes(BINARY_TABLE_ID, [mode64, b_op_or_sext, free_in_a[i], free_in_b[i], carry[i-1], free_in_c[i], carry[i] + 2*result_is_a + 4*use_first_byte + 8*c_is_signed]);
+ lookup_assumes(BINARY_TABLE_ID, [mode64, b_op_or_sext, carry[i], free_in_b[i], carry[i-1], free_in_c[i], free_in_a[i] + 2*result_is_a + 4*use_first_byte + 8*c_is_signed]);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Binary` constraint(s) [10].

Transposes the operand byte and the carry-out in the last byte lookup of the
Binary chain, so the table is consulted with the carry in the operand position.

**Where it lands in the generated Lean.**

* `Binary.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 536s):

Failing module(s): `ZiskFv.AirsClean.Binary.Wiring` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/Binary/Wiring.lean:55:2: Unknown identifier `derivedTuple_Binary_10_0.slots.map`
error: ZiskFv/AirsClean/Binary/Wiring.lean:84:10: Unknown identifier `link_Binary_10`
error: ZiskFv/AirsClean/Binary/Wiring.lean:85:17: Unknown identifier `derivedTuple_Binary_10_0`
error: ZiskFv/AirsClean/Binary/Wiring.lean:86:20: Unknown identifier `derivedTuple_Binary_10_1`
error: ZiskFv/AirsClean/Binary/Wiring.lean:93:19: Type mismatch
error: Lean exited with code 1
```

### Round 26 — ArithTable / `TABLE_ROW_EDIT` — **MISSED**

`zisk/state-machines/arith/src/arith_table_data.rs:150` — table row last field 16 -> 17

```diff
- [190, 3123, 12, 16],
+ [190, 3123, 12, 17],
```

**Is this a reasonable thing to break?** lookup-table data read straight from ZisK source by the extractor.

Same class as round 5: one row of the 74-row Arith opcode/flag lookup table.

**Where it lands in the generated Lean.**

* `ArithTable.lean` — **not in the Lake globs; never compiled**

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 689s).

Not a stale-cache artifact: the run rebuilt 408 jobs, among them `Extraction.Binary`, `Extraction.LookupWiring`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.BinaryMirrorWeld`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridge`.

### Round 27 — Main / `RANGE_WIDEN` — **MISSED**

`zisk/state-machines/main/pil/main.pil:334` — range max MAX_RANGE -> MAX_RANGE + 1

```diff
- range_check(expression: b_mem_step - b_reg_prev_mem_step - 1, min: 0, max: MAX_RANGE, sel: b_src_reg);
+ range_check(expression: b_mem_step - b_reg_prev_mem_step - 1, min: 0, max: (MAX_RANGE) + 1, sel: b_src_reg);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [41, 142]; `MemAlign` constraint(s) [33, 34, 35, 36, 38]; `MemAlignByte` constraint(s) [12]; `MemAlignWriteByte` constraint(s) [10].

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
missed rounds. It is consistent with the repository's own documented scope note
that the range/table AIRs (`SpecifiedRanges`) are not composed into the ensemble.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`
* `MemAlign.lean` — read by `ZiskFv/AirsClean/MemAlignMirrorWeld.lean`
* `MemAlignByte.lean` — read by `ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean`
* `MemAlignWriteByte.lean` — read by `ZiskFv/AirsClean/MemAlignByteMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 738s).

Not a stale-cache artifact: the run rebuilt 414 jobs, among them `Extraction.LookupWiring`, `Extraction.Main`, `Extraction.MemAlign`, `Extraction.MemAlignByte`, `Extraction.MemAlignWriteByte`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`.

### Round 28 — Mem / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/mem/pil/mem.pil:375` — delete the identity

```diff
- l_increment + 2**22 * h_increment + 1 === addr_changes * (delta_addr - delta_step) + delta_step;
+ //        l_increment + 2**22 * h_increment + 1 === addr_changes * (delta_addr - delta_step) + delta_step;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Mem` constraint(s) [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32], dropped [33].

This identity is the memory timeline's monotonicity witness: the increment
`l_increment + 2**22 * h_increment + 1` must equal the address delta on a row
where the address changes, and the step delta otherwise. Deleting it removes the
constraint that makes memory accesses ordered, which is the backbone of the
read-after-write argument.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Mem.lean` — read by `ZiskFv/AirsClean/MemMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 196s):

Failing module(s): `ZiskFv.AirsClean.Mem.RangeWiring` — **inside** `root_soundness`'s import closure.

```
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:76:19: Type mismatch
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:89:19: Type mismatch
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:102:19: Type mismatch
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:109:10: Unknown identifier `link_Mem_32`
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:110:10: Unknown identifier `hint_Mem_32_0`
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:130:0: Not a definitional equality: the left-hand side
```

### Round 29 — Main / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:473` — '-' -> '+' at col 18

```diff
- store_pc * (1 - store_pc) === 0;
+ store_pc * (1 + store_pc) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [29].

Same flag as round 12 (`store_pc`), broken a different way: its booleanity
becomes `store_pc * (1 + store_pc) === 0`, admitting `p-1`.

**Where it lands in the generated Lean.**

* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 681s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 30 — Main / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:404` — delete the identity

```diff
- (1 - is_external_op) * op * (flag) === 0;
+ //    (1 - is_external_op) * op * (flag) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142], dropped [143].

`(1 - is_external_op) * op * flag === 0` is half of the internal-operation flag
rule: for an internal op with `op = 1` the `flag` output must be 0. Deleting it
lets an internal operation report the opposite boolean result, which feeds
straight into the branch/`set_pc` logic below it.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 656s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:234:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:284:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:562:14: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:740:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:748:2: Type mismatch
```

### Round 31 — BinaryExtension / `CONST_PERTURB` — not a test

`zisk/state-machines/binary/pil/binary_extension.pil:60` — mask 0xFF -> 0xfe

```diff
- 1    0x8a      0xFFFF8a00    0xFFFFFFFF (since 0x8a & 0x80 = 0x80, we stop here and set the remaining bytes to 0xFF)
+ 1    0x8a      0xFFFF8a00    0xFFFFFFFF (since 0x8a & 0x80 = 0x80, we stop here and set the remaining bytes to 0xfe)
```

**Is this a reasonable thing to break?** the mutation leaves the extracted Lean byte-identical.

Not a test — same cause as round 2, in `binary_extension.pil`.

### Round 32 — BinaryAdd / `OPCODE_SWAP` — **MISSED**

`zisk/state-machines/binary/pil/binary_add.pil:25` — opcode OP_ADD -> OP_SUB

```diff
- proves_operation(op: OP_ADD, a:, b:, c:);
+ proves_operation(op: OP_SUB, a:, b:, c:);
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `BinaryAdd` constraint(s) [5].

`proves_operation(op: OP_ADD, …)` is BinaryAdd's advertisement on the 5000
operation bus: "I am the provider of 64-bit ADD". Re-tagging it `OP_SUB` makes a
row that computes `a + b` answer requests for subtraction, so `SUB` could be
discharged with an addition result. There is a second, correct `SUB` provider
(the Binary AIR), so this is not merely an unsatisfiable circuit — it is an extra
wrong provider for a live opcode.

**Where it lands in the generated Lean.**

* `BinaryAdd.lean` — read by `ZiskFv/AirsClean/BinaryMirrorWeld.lean`
* `Buses.lean` — **not in the Lake globs; never compiled**
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 632s).

Not a stale-cache artifact: the run rebuilt 410 jobs, among them `Extraction.BinaryAdd`, `Extraction.LookupWiring`, `Extraction.Main`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.BinaryMirrorWeld`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`.

### Round 33 — ArithTable / `TABLE_ROW_EDIT` — **MISSED**

`zisk/state-machines/arith/src/arith_table_data.rs:157` — table row last field 15 -> 16

```diff
- [190, 3423, 16, 15],
+ [190, 3423, 16, 16],
```

**Is this a reasonable thing to break?** lookup-table data read straight from ZisK source by the extractor.

Same class as round 5: one row of the 74-row Arith opcode/flag lookup table that
`pil-extract` parses out of ZisK's Rust source into `ArithTable.lean`.

**Where it lands in the generated Lean.**

* `ArithTable.lean` — **not in the Lake globs; never compiled**

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 619s).

Not a stale-cache artifact: the run rebuilt 409 jobs, among them `Extraction.BinaryAdd`, `Extraction.LookupWiring`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.BinaryMirrorWeld`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridge`.

### Round 34 — Arith / `OPERAND_SWAP` — not a test

`zisk/state-machines/arith/pil/arith.pil:168` — swap eq[4] <-> b[1]

```diff
- eq[4] = fab * a[3] * b[1]
+ b[1] = fab * a[3] * eq[4]
```

**Is this a reasonable thing to break?** ZisK's own PIL compiler refuses the mutated source.

Not a test. The swap turns `eq[4] = fab * a[3] * b[1]` into an assignment to the
witness column `b[1]`, which pil2-compiler rejects. Same shape as round 11.

### Round 35 — Main / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:469` — delete the identity

```diff
- is_precompiled * (1 - is_precompiled) === 0;
+ //    is_precompiled * (1 - is_precompiled) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142], dropped [143].

`is_precompiled` selects "this row dispatches to a precompile". Deleting its
booleanity lets a prover set it to any field element, so the gate between the
ordinary RV64IM path and the precompile path stops being a boolean choice.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 608s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:284:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:562:14: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:740:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 36 — ArithTable / `TABLE_ROW_EDIT` — **MISSED**

`zisk/state-machines/arith/src/arith_table_data.rs:148` — table row last field 12 -> 13

```diff
- [190, 3083, 13, 12],
+ [190, 3083, 13, 13],
```

**Is this a reasonable thing to break?** lookup-table data read straight from ZisK source by the extractor.

Same class as round 5: one row of the Arith opcode/flag lookup table.

**Where it lands in the generated Lean.**

* `ArithTable.lean` — **not in the Lake globs; never compiled**

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 604s).

Not a stale-cache artifact: the run rebuilt 407 jobs, among them `Extraction.LookupWiring`, `Extraction.Main`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridge`.

### Round 37 — MemAlignRom / `OPERAND_SWAP` — not a test

`zisk/state-machines/mem/pil/mem_align_rom.pil:20` — swap tsize[0] <-> tsize[1]

```diff
- const int psize = tsize[0] + tsize[1] + tsize[2] + tsize[3];
+ const int psize = tsize[1] + tsize[0] + tsize[2] + tsize[3];
```

**Is this a reasonable thing to break?** the mutation leaves the extracted Lean byte-identical.

Not a test. `psize = tsize[0] + tsize[1] + tsize[2] + tsize[3]` is a compile-time
constant; reordering the summands is the same number. The extracted
`MemAlignRom.lean` is byte-identical.

### Round 38 — Arith / `OPERAND_SWAP` — **MISSED**

`zisk/state-machines/arith/pil/arith.pil:253` — swap d[0] <-> d[1]

```diff
- const expr bus_res0 = secondary * (d[0] + d[1] * CHUNK_SIZE) +
+ const expr bus_res0 = secondary * (d[1] + d[0] * CHUNK_SIZE) +
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [61].

`bus_res0` is the low half of the *result* ZisK publishes on the operation bus
for an Arith row: `secondary * (d[0] + d[1] * CHUNK_SIZE) + …`. Swapping `d[0]`
and `d[1]` transposes the two 16-bit limbs, so the value announced to the rest of
the machine is the byte-swapped remainder. Limb transposition in a bus tuple is a
classic silent-corruption bug.

**Missed.** The swap changes exactly `Arith` constraint 61, and `ArithMirrorWeld`
names 49 of Arith's 65 constraints — 61 is not among them. Constraint 61 is the
challenge-mixing constraint that carries Arith's operation-bus tuple, so the two
16-bit limbs of the result ZisK announces to the rest of the machine can be
transposed without any theorem objecting. Same family as round 32: the row
equations of an AIR are welded, the bus tuple it publishes is not.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`
* `Buses.lean` — **not in the Lake globs; never compiled**
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 609s).

Not a stale-cache artifact: the run rebuilt 409 jobs, among them `Extraction.Arith`, `Extraction.LookupWiring`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.ArithMirrorWeld`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`, `ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridge`.

### Round 39 — MemAlign / `OPERAND_SWAP` — not a test

`zisk/state-machines/mem/pil/mem_align.pil:180` — swap prove_val[rc_index] <-> sel[_offset]

```diff
- prove_val[rc_index] += sel[_offset] * _tmp;
+ sel[_offset] += prove_val[rc_index] * _tmp;
```

**Is this a reasonable thing to break?** ZisK's own PIL compiler refuses the mutated source.

Not a test. The swap turns `prove_val[rc_index] += sel[_offset] * _tmp` into an
assignment to `sel`, which pil2-compiler rejects.

### Round 40 — Main / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:479` — delete the identity

```diff
- a_src_reg * (1 - a_src_reg) === 0;
+ //    a_src_reg * (1 - a_src_reg) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142], dropped [143].

`a_src_reg` selects "operand A comes from a register". Deleting its booleanity is
the register-file analogue of round 1, and it sits directly upstream of the
register-ordering range check that round 27 widens.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 603s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:562:14: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:740:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 41 — Arith / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/arith/pil/arith.pil:77` — delete the identity

```diff
- div_overflow * (b[2] - (1 - m32) * 0xFFFF) === 0;
+ //    div_overflow * (b[2] - (1 - m32) * 0xFFFF) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], dropped [64].

On a signed-division overflow row ZisK pins the divisor `b` to `0xFFFF…` limb by
limb; this identity pins limb 2 (with the 32-bit-mode adjustment). Deleting it
frees that limb, so the overflow branch can be taken with a divisor that is not
the overflow divisor.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 604s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:177:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:197:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:208:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:212:11: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:247:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:269:2: Type mismatch
```

### Round 42 — Main / `SELECTOR_WEAKEN` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:393` — selector is_external_op -> 1

```diff
- (1 - is_external_op) * (1 - op) * c[index] === 0;
+ (1 - 1) * (1 - op) * c[index] === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [7, 13].

`(1 - is_external_op) * (1 - op) * c[index] === 0` forces the result `c` to zero
on an internal operation with `op = 0`. Replacing the `is_external_op` selector by
`1` makes the whole product vanish, so the identity holds on every row and
constrains nothing — the classic "ungated constraint" defect, where a rule stays
in the file but stops applying.

**Where it lands in the generated Lean.**

* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 603s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:243:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:284:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 43 — Arith / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/arith/pil/arith.pil:217` — '-' -> '+' at col 12

```diff
- np * (1 - np) === 0;
+ np * (1 + np) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [44].

`np` is the "product is negative" flag of the Arith state machine; the identity is
its booleanity, and it is what turns the signed-multiplication sign analysis into
a case split.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 13s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:247:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 44 — Arith / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/arith/pil/arith.pil:64` — delete the identity

```diff
- div_by_zero * b[i] === 0;               // forces b must be zero when div_by_zero
+ //        div_by_zero * b[i] === 0;               // forces b must be zero when div_by_zero
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60], dropped [61, 62, 63, 64].

`div_by_zero * b[i] === 0` forces the divisor to be zero on a division-by-zero
row. Deleting it lets a prover claim the division-by-zero result for a non-zero
divisor.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 604s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:177:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:186:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:197:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:208:2: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:212:11: Type mismatch
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:216:11: Type mismatch
```

### Round 45 — Mem / `DROP_CONSTRAINT` — **CAUGHT**

`zisk/state-machines/mem/pil/mem.pil:215` — delete the identity

```diff
- SEGMENT_LAST * (value[i] - segment_last_value[i]) === 0;
+ //        SEGMENT_LAST * (value[i] - segment_last_value[i]) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Mem` constraint(s) [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], dropped [32, 33].

`SEGMENT_LAST * (value[i] - segment_last_value[i]) === 0` is the seam that hands
the last row's memory value of one segment to the next segment as an air value.
Deleting it lets the two segments disagree about the value at the boundary, which
is exactly the cross-segment memory continuity the proof has to rely on.

**Where it lands in the generated Lean.**

* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`
* `Mem.lean` — read by `ZiskFv/AirsClean/MemMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 179s):

Failing module(s): `ZiskFv.AirsClean.Mem.RangeWiring` — **inside** `root_soundness`'s import closure.

```
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:76:19: Type mismatch
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:89:19: Type mismatch
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:96:10: Unknown identifier `link_Mem_31`
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:97:10: Unknown identifier `hint_Mem_31_0`
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:109:10: Unknown identifier `link_Mem_32`
error: ZiskFv/AirsClean/Mem/RangeWiring.lean:110:10: Unknown identifier `hint_Mem_32_0`
```

### Round 46 — Arith / `OPERAND_SWAP` — **MISSED**

`zisk/state-machines/arith/pil/arith.pil:254` — swap c[0] <-> c[1]

```diff
- main_mul * (c[0] + c[1] * CHUNK_SIZE) +
+ main_mul * (c[1] + c[0] * CHUNK_SIZE) +
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Arith` constraint(s) [61].

Same class as round 38, on the multiplication branch of the same bus expression:
the two 16-bit limbs of the announced result `c` are transposed, so the value
placed on the operation bus is the limb-swapped product.

**Missed**, and it reproduces round 38 exactly: `Arith` constraint 61 again, this
time with the multiplication result's limbs transposed instead of the division
result's. Two independent random draws landing on the same unwelded bus tuple.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`
* `Buses.lean` — **not in the Lake globs; never compiled**
* `LookupWiring.lean` — read by `ZiskFv/AirsClean/Binary/Wiring.lean`, `ZiskFv/AirsClean/Mem/RangeWiring.lean`, `ZiskFv/AirsClean/MemAlign/Bridge.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **succeeds** (exit 0, 610s).

Not a stale-cache artifact: the run rebuilt 410 jobs, among them `Extraction.Arith`, `Extraction.LookupWiring`, `Extraction.Mem`, `Extraction.MemGeneratedArtifact`, `Extraction.MemGeneratedConstraintBridge`, `ZiskFv.AirsClean.ArithMirrorWeld`, `ZiskFv.AirsClean.Binary.Wiring`, `ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridge`.

### Round 47 — MemAlign / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/mem/pil/mem_align.pil:127` — '-' -> '+' at col 12

```diff
- wr * (1 - wr) === 0;
+ wr * (1 + wr) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `MemAlign` constraint(s) [25].

`wr` is the read/write selector of a MemAlign row; the memory-bus tuple uses it to
choose `MEMORY_STORE_OP` or `MEMORY_LOAD_OP`. Breaking its booleanity to
`{0, p-1}` lets a row be neither a load nor a store on the bus.

**Where it lands in the generated Lean.**

* `MemAlign.lean` — read by `ZiskFv/AirsClean/MemAlignMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 605s):

Failing module(s): `ZiskFv.AirsClean.MemAlignMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:392:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:465:2: Type mismatch
error: ZiskFv/AirsClean/MemAlignMirrorWeld.lean:538:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 48 — Main / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:476` — '-' -> '+' at col 16

```diff
- set_pc * (1 - set_pc) === 0;
+ set_pc * (1 + set_pc) === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [32].

`set_pc` selects "take the jump target as the next program counter". Breaking its
booleanity is directly on the control-flow path the soundness theorem's next-PC
argument depends on.

**Where it lands in the generated Lean.**

* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 20s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:310:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 49 — Main / `SIGN_FLIP` — **CAUGHT**

`zisk/state-machines/main/pil/main.pil:393` — '-' -> '+' at col 11

```diff
- (1 - is_external_op) * (1 - op) * c[index] === 0;
+ (1 + is_external_op) * (1 - op) * c[index] === 0;
```

**Is this a reasonable thing to break?** changes ZisK's compiled constraint system: `Main` constraint(s) [7, 13].

Same identity as round 42, broken a different way: `(1 + is_external_op)` instead
of `(1 - is_external_op)` inverts which rows the "internal op with `op = 0` has
`c = 0`" rule applies to.

**Where it lands in the generated Lean.**

* `Main.lean` — read by `ZiskFv/AirsClean/MainMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 19s):

Failing module(s): `ZiskFv.AirsClean.MainMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/MainMirrorWeld.lean:243:2: Type mismatch
error: ZiskFv/AirsClean/MainMirrorWeld.lean:284:2: Type mismatch
error: Lean exited with code 1
error: build failed
```

### Round 50 — MemAlignRom / `OPERAND_SWAP` — not a test

`zisk/state-machines/mem/pil/mem_align_rom.pil:124` — swap OFFSET[i+1] <-> WIDTH[i+1]

```diff
- if (j >= OFFSET[i+1] && j < OFFSET[i+1] + WIDTH[i+1]) {
+ if (j >= WIDTH[i+1] && j < OFFSET[i+1] + OFFSET[i+1]) {
```

**Is this a reasonable thing to break?** the mutation leaves the extracted Lean byte-identical.

**Not a test, and it exposes a coverage boundary.** The mutation is inside the ROM
row generator (`sel[j] = 1` for `j` in the access window), yet `MemAlignRom.lean`
is byte-identical.

The reason is in `tools/pil-extract/src/mem_align_rom.rs`: for this virtual AIR the
extractor reads only four things out of `mem_align_rom.pil` — the `OFFSET` and
`WIDTH` fixed columns, the `spsize` / `one_word_combinations` /
`two_word_combinations` constants, and a regex check that the `lookup_proves`
tuple still has its six-column shape — and then **re-implements the row builder in
Rust** (`build_rows`). The `pc`, `delta_pc`, `delta_addr` and `flags` of every ROM
row are therefore computed by the extractor, not read from ZisK. A divergence in
ZisK's own row builder cannot reach Lean, because Lean is being shown the
extractor's version of that builder.

### Round 51 — Arith / `OPERAND_SWAP` — control

`zisk/state-machines/arith/pil/arith.pil:138` — swap a[1] <-> b[0]

```diff
- eq[1] = fab * a[1] * b[0]
+ eq[1] = fab * b[0] * a[1]
```

**Is this a reasonable thing to break?** the expression tree changed but the polynomial did not (commutativity) — a passing build is the correct outcome here.

`eq[1] = fab*a[1]*b[0] + fab*a[0]*b[1] - c[1] …` is the second limb equation of the
Arith 64-bit multiplier. Swapping `a[1]` and `b[0]` turns the first cross term into
`fab*b[0]*a[1]` — the same product — so this is another commutativity control
rather than a defect, and a passing build is the correct outcome.

**Where it lands in the generated Lean.**

* `Arith.lean` — read by `ZiskFv/AirsClean/ArithMirrorWeld.lean`

`tools/pilout-roundtrip/check.py` passes — the extractor carried the mutation into Lean faithfully, so a missed round is not an extractor artifact.

`lake build` **fails** (exit 1, 13s):

Failing module(s): `ZiskFv.AirsClean.ArithMirrorWeld` — outside `root_soundness`'s import closure (a leaf audit module that only `ZiskFv.lean` imports).

```
error: ZiskFv/AirsClean/ArithMirrorWeld.lean:371:36: Application type mismatch: The argument
error: Lean exited with code 1
error: build failed
```

### Round 52 — Main / `SIGN_FLIP` — not a test

`zisk/state-machines/main/pil/main.pil:182` — '+' -> '-' at col 50

```diff
- addr2 === store_offset + store_ind * a[0] + store_use_sp * sp;
+ addr2 === store_offset + store_ind * a[0] - store_use_sp * sp;
```

**Is this a reasonable thing to break?** the mutation leaves the extracted Lean byte-identical.

Not a test — but for a reason worth recording. The identity is inside
`if (stack_enabled) { … }`, and `main.pil:14` declares
`airtemplate Main(int N = 2**21, int RC = 2, int stack_enabled = 0, …)`, which
`zisk.pil` does not override. Ten `if (stack_enabled)` blocks in `main.pil` are
compile-time dead in the pinned configuration, so nothing downstream — pilout,
extraction or proof — can be sensitive to them.

