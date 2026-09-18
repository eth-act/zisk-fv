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
