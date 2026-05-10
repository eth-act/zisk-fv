# BinaryExtension `free_in_c[BYTES][2]` layout — definitive resolution

> **Status:** Investigation complete; finding definitive. The named-accessor
> convention in `ZiskFv/Airs/Binary/BinaryExtension.lean:40-45` is **wrong
> relative to the actual circuit layout**. The cascade fix that aligns
> downstream files with the correct row-major interpretation is staged for
> a follow-up PR.

## Executive summary

PIL2 declares `col witness bits(32) free_in_c[BYTES][2]` with `BYTES = 8` —
a 16-cell 2-D witness array on `BinaryExtension`. The pil2-compiler
flattens this **row-major**: `free_in_c[j][k]` lands at flat index
`2*j + k` in the AIR's column ordering. Per zisk's pilout that places:

| 2-D index | flat | column id |
|--|--|--|
| `free_in_c[0][0]` | 0 | 10 |
| `free_in_c[0][1]` | 1 | 11 |
| `free_in_c[1][0]` | 2 | 12 |
| `free_in_c[1][1]` | 3 | 13 |
| … | … | … |
| `free_in_c[7][0]` | 14 | 24 |
| `free_in_c[7][1]` | 15 | 25 |

`Valid_BinaryExtension` (`ZiskFv/Airs/Binary/BinaryExtension.lean`)
exposes named accessors `free_in_c_0..15` mapped to columns 10..25
sequentially — **the underlying column mapping is correct**. What is wrong
is the *interpretation* in the structure's docstring and in every
downstream consumer (`BinaryExtensionPackedCorrect.lean`,
`Equivalence/RdValDerivation/BinaryShift.lean`, the 15 BinaryExtension-
using `equiv_<OP>` files), which read `free_in_c_0..7` as the byte-0..7
**c_lo half** and `free_in_c_8..15` as the byte-0..7 **c_hi half**
(column-major). The actual semantic, given pil2-compiler's row-major
flattening, is interleaved:

| named accessor | actual semantic |
|--|--|
| `free_in_c_0` | byte 0's c_lo contribution |
| `free_in_c_1` | byte 0's c_hi contribution |
| `free_in_c_2` | byte 1's c_lo contribution |
| `free_in_c_3` | byte 1's c_hi contribution |
| … | … |
| `free_in_c_14` | byte 7's c_lo contribution |
| `free_in_c_15` | byte 7's c_hi contribution |

Therefore the correct sums emitted on the operation bus are:

```
c_lo = free_in_c_0 + free_in_c_2 + free_in_c_4 + free_in_c_6
     + free_in_c_8 + free_in_c_10 + free_in_c_12 + free_in_c_14
c_hi = free_in_c_1 + free_in_c_3 + free_in_c_5 + free_in_c_7
     + free_in_c_9 + free_in_c_11 + free_in_c_13 + free_in_c_15
```

The existing `equiv_SLL` / `SRL` / `SRA` / `Lb` / `Lh` / `Lw` / shift-W
family `h_match_clo` shapes (`m.c_0 = free_in_c_0 + … + free_in_c_7`) and
the `BinaryExtensionPackedCorrect.ByteLookupHypotheses` mapping
(`e_j.c_lo_byte = v.free_in_c_<j>`, `e_j.c_hi_byte = v.free_in_c_<j+8>`)
both encode the column-major reading. They are unfulfillable from the
real bus emission and thus the per-opcode equiv proofs that consume them
are **conditionally** sound only.

This PR pins the resolution in writing and corrects the named-accessor
docstring. The downstream cascade fix is staged for a focused follow-up
(see [§ Cascade fix plan](#cascade-fix-plan)).

## Evidence

### 1. The pil2-compiler hint payload

`build/extraction/Extraction/Buses.lean::bus_emission_BinaryExtension_0`
records the operation-bus emission for BinaryExtension's
`proves_operation` (gsum_debug_data #1220). The slot's NAME is the
expression rendered by the upstream pil2-compiler (StringValue field of
the protobuf `Hint`); the slot's VALUE is the raw column reference
chain. They MUST agree because pil2-compiler emits both consistently.

c_lo slot (truncated for clarity):

```lean
{ name := "free_in_c[0][0] + free_in_c[1][0] + free_in_c[2][0] + free_in_c[3][0]
         + free_in_c[4][0] + free_in_c[5][0] + free_in_c[6][0] + free_in_c[7][0]"
, value := fun c row =>
    Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)
  + Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0) }
```

c_hi slot:

```lean
{ name := "free_in_c[0][1] + free_in_c[1][1] + free_in_c[2][1] + free_in_c[3][1]
         + free_in_c[4][1] + free_in_c[5][1] + free_in_c[6][1] + free_in_c[7][1]"
, value := fun c row =>
    column := 11, 13, 15, 17, 19, 21, 23, 25 }  -- (truncated)
```

So `free_in_c[j][0]` is at column `10 + 2j` and `free_in_c[j][1]` is at
column `11 + 2j`. **Row-major flattening is the ground truth.**

### 2. The extractor preserves pil2-compiler's order

`tools/pil-extract/src/main.rs:299-308`:

```rust
} else {
    // Array symbol: lengths[...] gives per-dimension sizes and `id` is
    // the base column index. Flatten across all indices.
    let total: u32 = sym.lengths.iter().product();
    for k in 0..total {
        m.insert((stage, sym.id + k), format!("{}[{}]", sym.name, k));
    }
}
```

The extractor takes the flat range `[sym.id, sym.id + total)` and labels
each column with the flat index `k`. It does NOT re-flatten — pil2-compiler
chose the column ordering. So extractor labels `free_in_c[0..15]` are
just sequential names for the columns in pil2-compiler's chosen order.

Per `build/extraction/Extraction/BinaryExtension.lean:24-39`, those flat
labels are:

```
-- stage 1 col 10: free_in_c[0]
-- stage 1 col 11: free_in_c[1]
-- stage 1 col 12: free_in_c[2]
…
-- stage 1 col 25: free_in_c[15]
```

Combining with §1: `free_in_c[k]` (extractor flat) corresponds to
`free_in_c[k/2][k%2]` (PIL 2-D). That is row-major.

### 3. `Valid_BinaryExtension`'s docstring contradicts §1+§2

`ZiskFv/Airs/Binary/BinaryExtension.lean:40-45`:

> The `free_in_c` array is split logically into a low half (indices
> 0..7) and a high half (indices 8..15), where `free_in_c_<i>` is the
> byte-`i` low-32-bit contribution to the 64-bit shift result and
> `free_in_c_<i+8>` is its high-32-bit contribution.

This describes a **column-major** logical split. It contradicts the
actual row-major circuit layout established by §1 + §2.

### 4. Downstream code encodes the same wrong (column-major) reading

`ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean:91-123`:

```lean
structure ByteLookupHypotheses (v : Valid_BinaryExtension C FGL FGL) (row : ℕ) where
  e0 : BinaryExtensionTableEntry FGL
  h0 : … ∧ e0.c_lo_byte = v.free_in_c_0 row ∧ e0.c_hi_byte = v.free_in_c_8 row
  e1 : … ∧ e1.c_lo_byte = v.free_in_c_1 row ∧ e1.c_hi_byte = v.free_in_c_9 row
  …
  e7 : … ∧ e7.c_lo_byte = v.free_in_c_7 row ∧ e7.c_hi_byte = v.free_in_c_15 row
```

This says "byte-j's c_lo_byte = `free_in_c_<j>` and byte-j's c_hi_byte =
`free_in_c_<j+8>`" (column-major). Should be:

```
e_j.c_lo_byte = v.free_in_c_<2*j>      -- row-major byte-j lo
e_j.c_hi_byte = v.free_in_c_<2*j+1>    -- row-major byte-j hi
```

`ZiskFv/Equivalence/{Sll,Slli,Sra,Srai,Srl,Srli,Shift,ShiftLI,ShiftR,ShiftRA,ShiftRAI,ShiftRLI,Lb,Lh,Lw}.lean`'s
`h_match_clo` / `h_match_chi`:

```lean
(h_match_clo : m.c_0 r_main
    = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
      + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
      + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
      + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
```

Should be:

```lean
(h_match_clo : m.c_0 r_main
    = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
      + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
      + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
      + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
```

These shapes are user-supplied and never derived — see `docs/fv/known-gaps.md`
— so the proofs build despite the contradiction. The Phase A OpBus axiom
(`op_bus_perm_sound_BinaryExtension`) is the first piece of infrastructure
that would attempt to derive them from the bus protocol, which is when the
contradiction surfaces.

## What this PR changes

1. **`docs/fv/binext-layout-resolution.md`** (this file) — definitive
   investigation record.
2. **`ZiskFv/Airs/Binary/BinaryExtension.lean:40-45`** — docstring
   corrected to row-major.

The downstream files that encode the column-major reading are NOT
modified in this PR. Their proofs continue to build (against the
wrong-shaped user-supplied hypothesis). The cascade fix is staged
separately — see below.

## Cascade fix plan (follow-up PR, "Step 0b")

To realign the codebase with the correct row-major layout:

| File | Change | Estimated lines |
|--|--|--|
| `ZiskFv/Airs/Binary/BinaryExtensionPackedCorrect.lean` | Re-map `ByteLookupHypotheses` (`e_j.c_lo_byte = v.free_in_c_<2j>`, `e_j.c_hi_byte = v.free_in_c_<2j+1>`); re-write all downstream sum aggregations and per-byte lemmas | ~401 mechanical edits across 50+ lemmas |
| `ZiskFv/Equivalence/RdValDerivation/BinaryShift.lean` | Re-write the per-shift discharge lemma chain to consume the corrected shapes | ~724 mechanical edits across 30+ lemmas (1651-line file) |
| `ZiskFv/Equivalence/{Sll,Slli,Sra,Srai,Srl,Srli,Shift,ShiftLI,ShiftR,ShiftRA,ShiftRAI,ShiftRLI}.lean` | Update `h_match_clo` / `h_match_chi` and `hc_lo_*` / `hc_hi_*` shapes to interleaved | ~32 edits each × 12 files = ~384 |
| `ZiskFv/Equivalence/{Lb,Lh,Lw}.lean` | Same as above for signed loads | ~16 edits each × 3 files = ~48 |

Total: ~1,557 mechanical edits, 16+ files. Risk of subtle errors during
the rename pass justifies a focused follow-up PR with its own review pass.
The proofs should continue to typecheck because the *structural pattern*
of every derivation is unchanged — only the variable indices shift.

The follow-up PR ordering: Step 0b lands before Step 2c
(BinaryExtension discharge bridge in `docs/fv/plans/op-bus-and-global-compliance.md`),
which depends on the corrected named-accessor convention.

## Why this matters

`opBus_row_BinaryExtension` (added in Phase A on the
`op-bus-and-global-compliance` branch, commit `30fca60`) faithfully
encodes the row-major bus emission. It is **correct** relative to the
real circuit. Any per-opcode discharge that derives `h_match_clo` from
the OpBus permutation axiom (`op_bus_perm_sound_BinaryExtension`) will
produce the row-major sum. The current per-opcode `h_match_clo` shapes
expect the column-major sum and would fail unification.

Without resolving this, the BinaryExtension and related signed-load
shapes cannot be threaded through the Phase A OpBus axiom into a global
compliance theorem. Resolving it via the cascade fix is the prerequisite
for `equiv_SLL` / `SRL` / `SRA` / `Lb` / `Lh` / `Lw` and the W-shift
family (12 ITYPE / RTYPE shifts + 3 signed loads = 15 opcodes) to become
unconditionally sound.
