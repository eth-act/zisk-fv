# The RHS is three representations of one circuit, joined by a bridge

Mapped the circuit-side trees against source (Lesson 03). The RHS is not a clean
single stack — it carries three in-tree representations of the same ZisK circuit,
at two granularities, plus a bifurcated extractor:

- **`tools/pil-extract`** has two emission targets: `air` → gitignored
  `build/extraction/` typed over the legacy `LeanZKCircuit.OpenVM.Circuit` shim
  (off the main Lake graph; only `Mem` cross-checked by the test gate); and
  `clean-component` → **committed** `AirsClean/<AIR>/{Row,Constraints}.lean`,
  faithful-by-construction. `extractor-notes.md`.
- **`ZiskFv/Airs/`** (32 files, per AIR-family) — named-column `Valid_<AIR>`
  records + op-bus/memory-bus model (`matches_entry`, `opBus_row_*`) + lookup
  tables + packed-correct lemmas. Still the spine everything consumes.
- **`ZiskFv/AirsClean/`** (73 files, per AIR-family) — Clean components:
  generated `Row`/`Constraints` + hand-written `Circuit`/`Spec`/`Soundness`/
  `Bridge`; `FullEnsemble` aggregates.
- **`ZiskFv/ZiskCircuit/`** (65 files, per OPCODE) — compositional
  circuit-correctness in field arithmetic (e.g. `Add.lean`: Main + BinaryAdd
  carry chain + op-bus match ⇒ c-lanes = a+b). Imports `Airs`, consumed by
  `EquivCore`.

**Decision-grade insight (the seam):** `AirsClean` does **not** replace `Airs`.
`AirsClean.Binary.validOfRow` (`Bridge.lean:346`) lowers a Clean `BinaryRow` into
the legacy `Valid_Binary` record — docstring "No `Circuit.main` left." And there
is literal duplication: `Airs.Tables.BinaryTable` *and* `AirsClean.BinaryTable`,
two namespaces, both with opcode constants. So the prime RHS re-architecture
targets are: (1) subsume the hand-written `Airs` `Valid_` model into generated
`AirsClean` and drop the `validOfRow` bridge; (2) unify the duplicated tables to
one source of truth; (3) retire the legacy `air`→OpenVM-shim extraction once
`Mem` moves to `clean-component`.

**Trust angle:** constructibility risk lives in the hand-written `Airs`
`Valid_<AIR>` records (over-strong constraints → vacuous theorems), which is why
the trust gate watches them; `validOfRow` is the current defense (ties the
record to a generated row). Granularity mismatch (ZiskCircuit per-opcode vs
Airs/AirsClean per-AIR) is why one opcode proof pulls from all three trees.

**Implication:** Lesson 04 (global hypotheses) should connect `aeneasBridgeTrust`
to this RHS picture. A future "build/CI" lesson should note the legacy
extraction path as a cleanup candidate.
