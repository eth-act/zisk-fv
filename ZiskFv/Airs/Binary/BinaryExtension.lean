import Mathlib

import ZiskFv.Field.Goldilocks

/-!
Named-column mirror of the extracted ZisK `BinaryExtension` AIR.

The `BinaryExtension` AIR (pilout idx 12) has **zero F-typed
constraints** — all 8 of its constraints are lookup arguments
(`bus_id = 124` against the BinaryExtensionTable) and permutation /
operation-bus interactions (mixed F/ExtF, skipped at the extraction
layer). Consequently this file contains only the typed-accessor
structure `Valid_BinaryExtension`; there are no per-constraint bridge
lemmas to author.

The structure exists purely so downstream packed-correctness lemmas
(see `BinaryExtensionPackedCorrect.lean`) can refer to the witness
columns by name when they consume the trusted byte-level relation
provided by `Airs/BinaryExtensionTable.lean::bin_ext_table_consumer_wf`.

Column layout taken from the witness-column header in
`ZiskFv/Extraction/BinaryExtension.lean`:

* stage 1 cols 0..28 (29 columns): `op`, `free_in_a[0..7]`, `free_in_b`,
  `free_in_c[0..15]`, `op_is_shift`, `b[0]`, `b[1]`.
* stage 2 cols 0..5 (6 columns): `gsum`, `im[0..3]`, `im_high_degree[0]`.

Mirrors the structural pattern of `Airs/Binary/BinaryAdd.lean`.
-/

namespace ZiskFv.Airs.BinaryExtension

open Goldilocks

/-!
## Deprecation notice — Phase D3/D4 removal

The `circuit` field and all `_def` constraint fields below are slated
for removal as part of the OpenVM Circuit retirement plan (see
`/home/cody/.claude/plans/ok-i-will-let-humble-reddy.md`):

* `circuit : C F ExtF` removed in Phase D3
* All `<col>_def` fields removed in Phase D4

After D6 (the completion marker), the canonical AIR view is the Clean
`Air.Flat.Component` at `ZiskFv/AirsClean/BinaryExtension/`. The Bridge at
`ZiskFv/AirsClean/BinaryExtension/Bridge.lean` provides the v1-compatibility shim.

Note: Lean 4 does not permit `@[deprecated]` attributes on structure
fields (verified via spike), so this notice is documentation-only.
-/

/-- Named accessors for one row of ZisK's `BinaryExtension` AIR.

    The `free_in_c` array is split logically into a low half (indices
    0..7) and a high half (indices 8..15), where `free_in_c_<i>` is the
    byte-`i` low-32-bit contribution to the 64-bit shift result and
    `free_in_c_<i+8>` is its high-32-bit contribution. (See
    `BinaryExtensionTableEntry.c_lo_byte` / `c_hi_byte` in
    `Airs/BinaryExtensionTable.lean`.) -/
structure Valid_BinaryExtension (F ExtF : Type)
    [Field F] [Field ExtF] where
  /-- Operation opcode (matches one of `OP_SLL`, `OP_SRL`, `OP_SRA`,
      `OP_SLL_W`, `OP_SRL_W`, `OP_SRA_W`, `OP_SEXT_B`, `OP_SEXT_H`,
      `OP_SEXT_W`). -/
  op : ℕ → F
  /-- Per-byte input lanes of operand A. -/
  free_in_a_0 : ℕ → F
  free_in_a_1 : ℕ → F
  free_in_a_2 : ℕ → F
  free_in_a_3 : ℕ → F
  free_in_a_4 : ℕ → F
  free_in_a_5 : ℕ → F
  free_in_a_6 : ℕ → F
  free_in_a_7 : ℕ → F
  /-- Shift amount (single byte). -/
  free_in_b : ℕ → F
  /-- Per-byte LOW 32-bit contribution of byte `i`'s shifted result
      (indices 0..7). -/
  free_in_c_0 : ℕ → F
  free_in_c_1 : ℕ → F
  free_in_c_2 : ℕ → F
  free_in_c_3 : ℕ → F
  free_in_c_4 : ℕ → F
  free_in_c_5 : ℕ → F
  free_in_c_6 : ℕ → F
  free_in_c_7 : ℕ → F
  /-- Per-byte HIGH 32-bit contribution of byte `i`'s shifted result
      (indices 8..15 in PIL = `free_in_c[byte_i][1]`). -/
  free_in_c_8 : ℕ → F
  free_in_c_9 : ℕ → F
  free_in_c_10 : ℕ → F
  free_in_c_11 : ℕ → F
  free_in_c_12 : ℕ → F
  free_in_c_13 : ℕ → F
  free_in_c_14 : ℕ → F
  free_in_c_15 : ℕ → F
  /-- 1 iff the opcode belongs to the shift family (SLL, SRL, SRA,
      SLL_W, SRL_W, SRA_W); 0 for sign-extension opcodes. -/
  op_is_shift : ℕ → F
  /-- Auxiliary witness columns from the `proves_operation` permutation
      (helper bytes for the Main-side route). -/
  b_0 : ℕ → F
  b_1 : ℕ → F
  /-- Stage-2 permutation accumulator. -/
  gsum : ℕ → F
  im_0 : ℕ → F
  im_1 : ℕ → F
  im_2 : ℕ → F
  im_3 : ℕ → F
  im_high_degree_0 : ℕ → F

end ZiskFv.Airs.BinaryExtension
