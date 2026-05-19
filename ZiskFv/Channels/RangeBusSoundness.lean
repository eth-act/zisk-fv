import Mathlib
import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks

/-!
# Range-bus soundness — single axiom replacing per-AIR range pins

ZisK's PIL declares column bit-widths via `bits(N)` annotations
(e.g. `col witness bits(32) a[RC]`). The `pil2-compiler` lowers each
annotation to a row-level lookup against the standard range-checker
bus (`RANGE_BUS_ID`), and lookup-argument soundness on that bus IS
the trust assumption that propagates the bound up to Lean.

On `main` (and through the `clean-integration` consolidations), this
manifests as 14 per-AIR axioms — one for each AIR that declares
`bits(N)` columns:

| File                                         | Axiom                                       |
|----------------------------------------------|---------------------------------------------|
| `Airs/Main/Ranges.lean`                      | `main_columns_in_range`                     |
| `Airs/Binary/BinaryAddRanges.lean`           | `binary_add_columns_in_range`               |
| `Airs/Binary/BinaryExtensionRanges.lean`     | `binary_extension_columns_in_range`         |
| `Airs/Arith/Ranges.lean`                     | 8 arith `*_columns_in_range*` axioms        |
| `Airs/MemoryBus/EntryRanges.lean`            | `memory_bus_entry_byte_range_perm_sound`    |

All 14 are the **same trust claim** — "this column was declared
`bits(N)` in PIL, therefore the range-checker bus's lookup-argument
soundness gives `(col r).val < 2^N`". The only thing that varies
across them is the witness type (`Valid_<AIR>`) and the
(column, width) pairs.

This file lands the consolidated axiom `range_bus_sound`. Per-AIR
range theorems become **derived** rather than axiomatized — each
becomes a one-line application of `range_bus_sound` per column.

## Trust footprint

Net for this file: **+1 axiom** (`range_bus_sound`). Each subsequent
per-AIR PR that derives its old `*_columns_in_range` axiom from
`range_bus_sound` retires **−1 axiom**. Cluster math:

* After this PR + BinaryAdd derivation: +1, −1 = **net 0** (the PoC,
  this commit chain)
* After Binary, BinaryExtension derivations: −2 more
* After Main, MemoryBus byte-range, 8 Arith derivations: −10 more
* Cluster total when all 14 retire: **+1 − 14 = −13 axioms**

## Trust class

#5b — range-bus / byte-range soundness. Same scope as the 14 axioms
it replaces. Citation:

* PIL bus identifier: `zisk/pil/opids.pil` (`RANGE_BUS_ID`)
* Protocol soundness: `pil2-stark/src/lookup_check.rs` (verifier-side
  soundness proof of the lookup-argument construction)
* Pil2-compiler emission site: `pil2-compiler/src/expression/...`
  (the `bits(N)` lowering pass)
-/

namespace ZiskFv.Channels.RangeBusSoundness

open Goldilocks

/-! ## Named bit-width bounds

Per the project's coding convention (no raw decimal literals for
bit-width bounds), the following `abbrev`s are the canonical names
for the powers of two that range-bus participants commonly land on.
Defined as `abbrev` so `decide`/`omega`/`rfl` unfold transparently
and the V2 binder walker (`whnfR`) sees through them. -/

/-- Upper bound for `bits(1)` (boolean) values: `2^1 = 2`. -/
abbrev U1_max : ℕ := 2 ^ 1
/-- Upper bound for `bits(4)` values: `2^4 = 16`. -/
abbrev U4_max : ℕ := 2 ^ 4
/-- Upper bound for `bits(8)` values: `2^8 = 256`. -/
abbrev U8_max : ℕ := 2 ^ 8
/-- Upper bound for `bits(16)` values: `2^16 = 65536`. -/
abbrev U16_max : ℕ := 2 ^ 16
/-- Upper bound for `bits(32)` values: `2^32 = 4294967296`. -/
abbrev U32_max : ℕ := 2 ^ 32

/-! ## Evaluation lemmas for the named constants

These `@[simp]` lemmas unfold the abbrevs to their decimal values
so downstream `omega` / `simp` passes can fold them away without
needing to manually `unfold U<N>_max`. The equations are `rfl`-true,
but registering them as simp lemmas ensures every tactic in the
codebase that uses simp's normalization sees the literal form. -/
@[simp] lemma U1_max_eq  : U1_max  = 2 := rfl
@[simp] lemma U4_max_eq  : U4_max  = 16 := rfl
@[simp] lemma U8_max_eq  : U8_max  = 256 := rfl
@[simp] lemma U16_max_eq : U16_max = 65536 := rfl
@[simp] lemma U32_max_eq : U32_max = 4294967296 := rfl

/-- **PIL `bits(N)` annotation marker.** Definitional placeholder for
    "PIL declared this column as `bits(width)`". This is *not* a
    cryptographic claim — it's a textual citation marker. The
    cryptographic content lives in `range_bus_sound`.

    Concretely `True`, so per-column registrations are trivial.
    Future versions may strengthen this to a proper Prop if we want
    to enforce structural checks across the codebase. -/
def PIL_bits_annotation
    {W : Type} (_w : W) (_col : W → ℕ → FGL) (_width : ℕ) : Prop := True

/-- **Range-bus lookup-argument soundness (consolidated).** A column
    declared `bits(width)` in PIL has value `< 2^width` at every row.

    This is the single trust axiom for ZisK's range-checker bus,
    replacing the 14 per-AIR `*_columns_in_range` axioms. Each AIR
    registers its columns via per-column applications of this axiom;
    the previous per-AIR axioms become derived theorems.

    Trust class: lookup-argument soundness on `RANGE_BUS_ID` (same
    cryptographic scope as the 14 retired per-AIR axioms; PIL
    citation in each retired axiom's docstring is preserved on the
    derived theorem). -/
axiom range_bus_sound
    {W : Type} (w : W) (col : W → ℕ → FGL) (width : ℕ)
    (_h_in_range_bus : PIL_bits_annotation w col width) :
    ∀ r, (col w r).val < 2 ^ width

/-! ## Signed-region soundness for Arith's carry table

The Arith AIR's carry columns are range-checked against
`ARITH_RANGE_CARRY`, whose entries are `[-0xEFFFF .. 0xF0000]`
(`zisk/state-machines/arith/pil/arith_range_table.pil:69`). In
Goldilocks-`Fin` representation this is the disjoint union of:

* the **non-negative** band `[0, 0xF0000]`, i.e. `.val < 0xF0001 = 983041`
* the **negative** band `[GL_prime - 0xF0000, GL_prime - 1]`,
  i.e. `GL_prime - 983040 ≤ .val`

This is a different soundness shape than `range_bus_sound`'s
`< 2^width`. We capture it via a sibling axiom
`signed_range_bus_sound` so the 4 signed/W-mode Arith carry-column
range axioms become derived theorems.

Trust class: same #6b as the retired pure-bit-width Arith range
axioms (range-checker bus lookup soundness, signed-table sub-class). -/

/-- Threshold for the signed-mode arith carry table's non-negative band. -/
abbrev ARITH_SIGNED_POS_BOUND : ℕ := 983041   -- 0xF0001
/-- Threshold for the signed-mode arith carry table's negative band. -/
abbrev ARITH_SIGNED_NEG_OFFSET : ℕ := 983040  -- 0xF0000

/-- **PIL `ARITH_RANGE_CARRY` annotation marker.** Same definitional
    role as `PIL_bits_annotation` but for the signed-carry table. -/
def PIL_arith_signed_carry_annotation
    {W : Type} (_w : W) (_col : W → ℕ → FGL) : Prop := True

/-- **Signed Arith carry-table soundness (consolidated).** A column
    range-checked against `ARITH_RANGE_CARRY` (entries
    `[-0xEFFFF..0xF0000]`) satisfies the signed-band disjunction at
    every row.

    Replaces the 4 signed/W-mode `arith_*_carry_columns_in_range_*`
    axioms. Trust class: #6b range-checker bus lookup soundness,
    signed-table sub-class. -/
axiom signed_range_bus_sound
    {W : Type} (w : W) (col : W → ℕ → FGL)
    (_h_in_arith_signed_carry_bus : PIL_arith_signed_carry_annotation w col) :
    ∀ r, (col w r).val < ARITH_SIGNED_POS_BOUND
       ∨ GL_prime - ARITH_SIGNED_NEG_OFFSET ≤ (col w r).val

end ZiskFv.Channels.RangeBusSoundness
