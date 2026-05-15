# `ZiskFv/Bits/`

Fixed-width arithmetic and packed-lane lemmas. Foundational layer
sitting between `Field/` and everything else.

- **`U64.lean`** — bridge lemmas between `BitVec 64`, `Nat`, and
  `Fin (2^64)`. Adders, subtractors, shifts, sign-extensions,
  toNat / toInt round-trips.
- **`PackedBitVec/`** —
  - `NoWrap.lean`, `MulNoWrap.lean`, `WidePCNoWrap.lean` —
    no-wraparound lemmas for packed-lane arithmetic, the engine
    that turns `Fin p` decompositions into honest `BitVec` results
    without modular-reduction surprises.
  - `Signed.lean`, `SignedNoWrap.lean`, `SignedChunkLift.lean` —
    signed variants for the SEXT/SRA family.
  - `Extensions.lean` — generic lifting helpers.
- **`Execution.lean`** — generic execution-trace structure used by
  `Airs/` and `ZiskCircuit/`. Pure data; no semantics.
- **`PackedBitVec.lean`** (top-level) — module aggregator for the
  packed-lane lemmas.

No axioms; pure-proof layer. Heavy `linear_combination` use; see
the trap notes in `CLAUDE.md` about `ring`-atom-level distinctions
between `4294967296 * 4294967296` and `18446744073709551616` (same
number, different polynomial atoms).
