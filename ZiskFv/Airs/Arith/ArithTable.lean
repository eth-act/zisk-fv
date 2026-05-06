import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div
import ZiskFv.Extraction.ArithTable

/-!
# arith_table permutation-lookup soundness

The ZisK Arith state machine pipes every active row through a fixed
lookup table `arith_table` (see
`zisk/state-machines/arith/pil/arith_table.pil`) that deterministically
maps an opcode / mode pair to sign / parity witnesses
`(na, nb, np, nr)`.

## Architecture

The trust surface here factors into two layers:

1. **Plookup soundness** — one axiom per AIR variant
   (`arith_table_lookup_sound_mul`, `_div`) saying every row's
   `(op, m32, na, nb, np, nr)` tuple matches some row in
   `Extraction.ArithTable.arith_table` (the 74-row hand-extracted
   constant). This is the irreducible plookup-protocol soundness;
   formalizing the underlying ZK protocol in Lean is out of scope.
2. **Witness-mapping theorems** of the shape
   `arith_table_<op>_witnesses_from_data` that case-analyze the table
   data (via `decide` over the concrete 74-row list) to derive specific
   `(op, m32) → (na, nb, np, nr)` mappings for each unsigned opcode.

## Scope of the plookup axioms

`arith_table_lookup_sound_mul/_div` pin every row's tuple as matching
some row in the extracted table. The specific table data
(`Extraction.ArithTable.arith_table`) matches `arith_table.pil`'s
74-row table for the RV64IM subset:

- `(OP_MULU, m32=0)`  → `(0, 0, 0, 0)` — RV64 MULU
- `(OP_MULUH, m32=0)` → `(0, 0, 0, 0)` — RV64 MULHU
- `(OP_MUL, m32=0)`   → `(a.3, b.3, d.3, 0)` — signed; conditional
- `(OP_DIVU, m32=0)`  → `(0, 0, 0, 0)` — RV64 DIVU
- `(OP_REMU, m32=0)`  → `(0, 0, 0, 0)` — RV64 REMU
- `(OP_MUL_W, m32=1)` → `(0, 0, 0, 0)` — RV64 MULW

The `_from_data` theorems below cover only the unsigned cases (where
the quadruple is constant zero). Signed cases remain conditional
(na = a.3, nb = b.3, np = d.3) and require bit-extraction lemmas.
-/

namespace ZiskFv.Airs.Arith.ArithTable

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.ArithMul
open ZiskFv.Airs.ArithDiv

variable {C : Type → Type → Type} {F ExtF : Type}
variable [Field F] [Field ExtF] [Circuit F ExtF C]

/-! ## Plookup-soundness axioms

The two irreducible plookup-soundness axioms. Each says every active
row's tuple matches some row in the extracted `arith_table`. Standard
ZK literature result (Plookup / logUp grand-product soundness);
re-formalizing the protocol in Lean is out of scope.
-/

open ZiskFv.Extraction.ArithTable in
/-- **Plookup-soundness axiom for the Arith MUL state machine.** Says:
    every `Valid_ArithMul` row's `(op, m32, na, nb, np, nr)` tuple
    matches some row in `arith_table` (the 74-row extracted lookup
    table). The actual ZK protocol enforces this via a grand-product
    polynomial identity; we axiomatize the soundness statement directly.

    **Trust basis.** Standard Plookup / logUp soundness theorem from
    the ZK literature. Reformalizing the protocol in Lean is out of
    scope (separate cryptographic project).

    **Note.** We compare `m32`, `na`, `nb`, `np`, `nr` as `Nat` values
    (the table entries) cast into `F`. Direct tuple equality avoids
    a lift. -/
axiom arith_table_lookup_sound_mul
    {C : Type → Type → Type} [Circuit FGL FGL C] :
    ∀ (v : Valid_ArithMul C FGL FGL) (row : ℕ),
      ∃ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
        v.op row = tbl_row.op
      ∧ v.m32 row = (Nat.cast tbl_row.m32 : FGL)
      ∧ v.na row = (Nat.cast tbl_row.na : FGL)
      ∧ v.nb row = (Nat.cast tbl_row.nb : FGL)
      ∧ v.np row = (Nat.cast tbl_row.np : FGL)
      ∧ v.nr row = (Nat.cast tbl_row.nr : FGL)

/-- **Plookup-soundness for the Arith DIV state machine.** -/
axiom arith_table_lookup_sound_div
    {C : Type → Type → Type} [Circuit FGL FGL C] :
    ∀ (v : Valid_ArithDiv C FGL FGL) (row : ℕ),
      ∃ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
        v.op row = tbl_row.op
      ∧ v.m32 row = (Nat.cast tbl_row.m32 : FGL)
      ∧ v.na row = (Nat.cast tbl_row.na : FGL)
      ∧ v.nb row = (Nat.cast tbl_row.nb : FGL)
      ∧ v.np row = (Nat.cast tbl_row.np : FGL)
      ∧ v.nr row = (Nat.cast tbl_row.nr : FGL)

/-! ## Witness-mapping `_from_data` theorems

For each unsigned RV64IM opcode, a private `_witnesses_zero` lemma
(by `decide` over the 74-row table) plus a `_from_data` theorem
deriving the witness mapping from `arith_table_lookup_sound_mul/_div`
+ that lemma.
-/

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_MULU` has all four sign-witness fields equal to zero (as
    `Nat`). Proven by `decide` over the 74-row concrete list. -/
private lemma arith_table_op_mulu_witnesses_zero :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_MULU →
      tbl_row.na = 0 ∧ tbl_row.nb = 0
      ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0 := by
  decide

/-- **Witness mapping theorem — OP_MULU.**
    Derived from `arith_table_lookup_sound_mul` + case analysis on
    the extracted `arith_table`. -/
theorem arith_table_mulu_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MULU) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_mul v row
  have h_tbl_op : tbl_row.op = OP_MULU := h_op_eq.symm.trans h_op
  obtain ⟨hna, hnb, hnp, hnr⟩ :=
    arith_table_op_mulu_witnesses_zero tbl_row h_in h_tbl_op
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_na_eq, hna]; rfl
  · rw [h_nb_eq, hnb]; rfl
  · rw [h_np_eq, hnp]; rfl
  · rw [h_nr_eq, hnr]; rfl

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_MULUH` has all four sign-witness fields equal to zero. -/
private lemma arith_table_op_muluh_witnesses_zero :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_MULUH →
      tbl_row.na = 0 ∧ tbl_row.nb = 0
      ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0 := by
  decide

/-- **Witness mapping theorem — OP_MULUH.** -/
theorem arith_table_muluh_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MULUH) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_mul v row
  have h_tbl_op : tbl_row.op = OP_MULUH := h_op_eq.symm.trans h_op
  obtain ⟨hna, hnb, hnp, hnr⟩ :=
    arith_table_op_muluh_witnesses_zero tbl_row h_in h_tbl_op
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_na_eq, hna]; rfl
  · rw [h_nb_eq, hnb]; rfl
  · rw [h_np_eq, hnp]; rfl
  · rw [h_nr_eq, hnr]; rfl

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_MUL_W` has all four sign-witness fields equal to zero. -/
private lemma arith_table_op_mulw_witnesses_zero :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_MUL_W →
      tbl_row.na = 0 ∧ tbl_row.nb = 0
      ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0 := by
  decide

/-- **Witness mapping theorem — OP_MUL_W.** -/
theorem arith_table_mulw_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MUL_W) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_mul v row
  have h_tbl_op : tbl_row.op = OP_MUL_W := h_op_eq.symm.trans h_op
  obtain ⟨hna, hnb, hnp, hnr⟩ :=
    arith_table_op_mulw_witnesses_zero tbl_row h_in h_tbl_op
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_na_eq, hna]; rfl
  · rw [h_nb_eq, hnb]; rfl
  · rw [h_np_eq, hnp]; rfl
  · rw [h_nr_eq, hnr]; rfl

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_DIVU` has all four sign-witness fields equal to zero. -/
private lemma arith_table_op_divu_witnesses_zero :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_DIVU →
      tbl_row.na = 0 ∧ tbl_row.nb = 0
      ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0 := by
  decide

/-- **Witness mapping theorem — OP_DIVU.** -/
theorem arith_table_divu_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_DIVU) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_div v row
  have h_tbl_op : tbl_row.op = OP_DIVU := h_op_eq.symm.trans h_op
  obtain ⟨hna, hnb, hnp, hnr⟩ :=
    arith_table_op_divu_witnesses_zero tbl_row h_in h_tbl_op
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_na_eq, hna]; rfl
  · rw [h_nb_eq, hnb]; rfl
  · rw [h_np_eq, hnp]; rfl
  · rw [h_nr_eq, hnr]; rfl

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_REMU` has all four sign-witness fields equal to zero. -/
private lemma arith_table_op_remu_witnesses_zero :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_REMU →
      tbl_row.na = 0 ∧ tbl_row.nb = 0
      ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0 := by
  decide

/-- **Witness mapping theorem — OP_REMU.** -/
theorem arith_table_remu_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_REMU) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_div v row
  have h_tbl_op : tbl_row.op = OP_REMU := h_op_eq.symm.trans h_op
  obtain ⟨hna, hnb, hnp, hnr⟩ :=
    arith_table_op_remu_witnesses_zero tbl_row h_in h_tbl_op
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_na_eq, hna]; rfl
  · rw [h_nb_eq, hnb]; rfl
  · rw [h_np_eq, hnp]; rfl
  · rw [h_nr_eq, hnr]; rfl

/-! ## Per-opcode specializations and bundling shims

The per-opcode `arith_table_<op>_witnesses` specialization theorems
delegate to the corresponding `_from_data` lemma. The `h_m32`
hypothesis is retained for signature stability but is unused (the
witness mapping is determined by `op` alone for unsigned ops). The
two `arith_table_row_witness_unsigned` / `_unsigned_div` bundlers
exist for caller compatibility. -/

/-- **Specialization — OP_MULU unsigned.** The arith_table forces
    `(na, nb, np, nr) = (0, 0, 0, 0)` for an unsigned 64-bit MUL row.

    Derived from `arith_table_mulu_witnesses_from_data`; `h_m32` is
    retained for signature stability but unused. -/
theorem arith_table_mulu_witnesses
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MULU) (_h_m32 : v.m32 row = 0) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 :=
  arith_table_mulu_witnesses_from_data v row h_op

/-- **Specialization — OP_MULUH unsigned high.** The arith_table
    forces `(na, nb, np, nr) = (0, 0, 0, 0)` for an unsigned 64-bit
    MUL-high row. Derived from `_from_data`. -/
theorem arith_table_muluh_witnesses
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MULUH) (_h_m32 : v.m32 row = 0) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 :=
  arith_table_muluh_witnesses_from_data v row h_op

/-- **Specialization — OP_MUL_W 32-bit.** The arith_table forces
    `(na, nb, np, nr) = (0, 0, 0, 0)` for a 32-bit MULW row. -/
theorem arith_table_mulw_witnesses
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MUL_W) (_h_m32 : v.m32 row = 1) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 :=
  arith_table_mulw_witnesses_from_data v row h_op

/-- **Specialization — OP_DIVU primary.** The arith_table forces
    `(na, nb, np, nr) = (0, 0, 0, 0)` for an unsigned 64-bit DIVU row. -/
theorem arith_table_divu_witnesses
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_DIVU) (_h_m32 : v.m32 row = 0) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 :=
  arith_table_divu_witnesses_from_data v row h_op

/-- **Specialization — OP_REMU secondary.** The arith_table forces
    `(na, nb, np, nr) = (0, 0, 0, 0)` for an unsigned 64-bit REMU row. -/
theorem arith_table_remu_witnesses
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_REMU) (_h_m32 : v.m32 row = 0) :
    v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0 :=
  arith_table_remu_witnesses_from_data v row h_op

/-- **Bundling shim.** Compatibility wrapper around the per-opcode
    `_from_data` lemmas. New code should use
    `arith_table_<op>_witnesses_from_data` directly. -/
theorem arith_table_row_witness_unsigned
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ) :
    (v.op row = OP_MULU → v.m32 row = 0 →
        v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∧ (v.op row = OP_MUL_W → v.m32 row = 1 →
        v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0) :=
  ⟨fun h_op _ => arith_table_mulu_witnesses_from_data v row h_op,
   fun h_op _ => arith_table_mulw_witnesses_from_data v row h_op⟩

/-- **Bundling shim.** Compatibility wrapper around the per-opcode
    `_from_data` lemmas (DIVU / REMU). -/
theorem arith_table_row_witness_unsigned_div
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ) :
    (v.op row = OP_DIVU → v.m32 row = 0 →
        v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∧ (v.op row = OP_REMU → v.m32 row = 0 →
        v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0) :=
  ⟨fun h_op _ => arith_table_divu_witnesses_from_data v row h_op,
   fun h_op _ => arith_table_remu_witnesses_from_data v row h_op⟩

/-! ## Signed `_from_data` theorems

For each signed RV64IM opcode, a private `_witnesses_disj` lemma (by
`decide` over the 74-row table) plus a `_from_data` theorem deriving
the witness mapping from `arith_table_lookup_sound_mul/_div` + the
disjunction lemma.

Unlike the unsigned cases (where every matching row has
`(na, nb, np, nr) = (0, 0, 0, 0)`), signed opcodes have multiple
matching rows with different sign-witness patterns — the conclusion
is a disjunction over the distinct `(na, nb, np, nr)` tuples that
appear in the table for the target opcode.

No new axioms; each theorem chains `arith_table_lookup_sound_*` with
the disjunction lemma. The disjunction lemma is decidable because the
table is a concrete 74-row constant.
-/

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_MULSUH` has its `(na, nb, np, nr)` field tuple matching one
    of the 3 patterns. -/
private lemma arith_table_op_mulsuh_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_MULSUH →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_MULSUH.**
    Disjunction over the 3 distinct `(na, nb, np, nr)` patterns that
    `OP_MULSUH` rows take in the extracted `arith_table`. -/
theorem arith_table_mulsuh_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MULSUH) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_mul v row
  have h_tbl_op : tbl_row.op = OP_MULSUH := h_op_eq.symm.trans h_op
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_mulsuh_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (by simpa using lift 1 0 1 0 hna hnb hnp hnr))

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_MUL` has its `(na, nb, np, nr)` field tuple matching one of
    the 6 patterns (`nr = 0` always; `(na, nb, np)` ranges over a
    6-element subset of `{0,1}^3`). -/
private lemma arith_table_op_mul_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_MUL →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_MUL.**
    Disjunction over the 6 distinct `(na, nb, np, nr)` patterns that
    `OP_MUL` rows take in the extracted `arith_table`. -/
theorem arith_table_mul_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MUL) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_mul v row
  have h_tbl_op : tbl_row.op = OP_MUL := h_op_eq.symm.trans h_op
  -- Quad lift: each disjunct converts `tbl_row.{na,nb,np,nr}` to `v.{na,nb,np,nr} row`.
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_mul_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (Or.inl (by simpa using lift 0 1 0 0 hna hnb hnp hnr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using lift 1 1 0 0 hna hnb hnp hnr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 0 hna hnb hnp hnr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using lift 0 1 1 0 hna hnb hnp hnr)))))

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_MULH` has its `(na, nb, np, nr)` field tuple matching one of
    the 6 patterns. Same patterns as `OP_MUL` (the table places them
    on different `range_ab/range_cd` rows but the sign witnesses
    coincide). -/
private lemma arith_table_op_mulh_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_MULH →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_MULH.**
    Same disjunction shape as `OP_MUL` (the two opcodes share their
    sign-witness patterns). -/
theorem arith_table_mulh_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_MULH) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_mul v row
  have h_tbl_op : tbl_row.op = OP_MULH := h_op_eq.symm.trans h_op
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_mulh_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (Or.inl (by simpa using lift 0 1 0 0 hna hnb hnp hnr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using lift 1 1 0 0 hna hnb hnp hnr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 0 hna hnb hnp hnr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using lift 0 1 1 0 hna hnb hnp hnr)))))

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_DIV` has its `(na, nb, np, nr)` field tuple matching one of
    the 10 distinct patterns. (The table has 11 rows for OP_DIV but
    two share their sign-witness pattern, so 10 distinct tuples.) -/
private lemma arith_table_op_div_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_DIV →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_DIV.**
    Disjunction over the 10 distinct `(na, nb, np, nr)` patterns. -/
theorem arith_table_div_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_DIV) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_div v row
  have h_tbl_op : tbl_row.op = OP_DIV := h_op_eq.symm.trans h_op
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_div_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (Or.inl (by simpa using lift 0 1 0 0 hna hnb hnp hnr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 1 0 0 hna hnb hnp hnr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 0 hna hnb hnp hnr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 0 hna hnb hnp hnr))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 0 1 1 hna hnb hnp hnr)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 1 hna hnb hnp hnr))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 1 hna hnb hnp hnr)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using lift 1 1 1 0 hna hnb hnp hnr)))))))))

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_REM` has its `(na, nb, np, nr)` field tuple matching one of
    the 10 distinct patterns. Same patterns as `OP_DIV`. -/
private lemma arith_table_op_rem_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_REM →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_REM.**
    Same disjunction shape as `OP_DIV`. -/
theorem arith_table_rem_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_REM) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_div v row
  have h_tbl_op : tbl_row.op = OP_REM := h_op_eq.symm.trans h_op
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_rem_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (Or.inl (by simpa using lift 0 1 0 0 hna hnb hnp hnr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 1 0 0 hna hnb hnp hnr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 0 hna hnb hnp hnr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 0 hna hnb hnp hnr))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 0 1 1 hna hnb hnp hnr)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 1 hna hnb hnp hnr))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 1 hna hnb hnp hnr)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using lift 1 1 1 0 hna hnb hnp hnr)))))))))

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_DIV_W` has its `(na, nb, np, nr)` field tuple matching one of
    the 10 distinct patterns. (Same pattern set as `OP_DIV` — the W
    variant uses the 32-bit range tables but the sign-witness columns
    match.) -/
private lemma arith_table_op_div_w_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_DIV_W →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_DIV_W.**
    Same disjunction shape as `OP_DIV`. -/
theorem arith_table_div_w_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_DIV_W) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_div v row
  have h_tbl_op : tbl_row.op = OP_DIV_W := h_op_eq.symm.trans h_op
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_div_w_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (Or.inl (by simpa using lift 0 1 0 0 hna hnb hnp hnr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 1 0 0 hna hnb hnp hnr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 0 hna hnb hnp hnr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 0 hna hnb hnp hnr))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 0 1 1 hna hnb hnp hnr)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 1 hna hnb hnp hnr))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 1 hna hnb hnp hnr)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using lift 1 1 1 0 hna hnb hnp hnr)))))))))

/-- Helper: every row of `arith_table` whose `op` field equals
    `OP_REM_W` has its `(na, nb, np, nr)` field tuple matching one of
    the 10 distinct patterns. Same pattern set as `OP_DIV_W`. -/
private lemma arith_table_op_rem_w_witnesses_disj :
    ∀ tbl_row ∈ ZiskFv.Extraction.ArithTable.arith_table,
      tbl_row.op = OP_REM_W →
      (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 0 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 0 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 0 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 1)
      ∨ (tbl_row.na = 1 ∧ tbl_row.nb = 1 ∧ tbl_row.np = 1 ∧ tbl_row.nr = 0) := by
  decide

/-- **Witness mapping theorem — OP_REM_W.**
    Same disjunction shape as `OP_DIV_W`. -/
theorem arith_table_rem_w_witnesses_from_data
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithDiv C FGL FGL) (row : ℕ)
    (h_op : v.op row = OP_REM_W) :
    (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 0 ∧ v.nr row = 0)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0)
    ∨ (v.na row = 0 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 0 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 0 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 1)
    ∨ (v.na row = 1 ∧ v.nb row = 1 ∧ v.np row = 1 ∧ v.nr row = 0) := by
  obtain ⟨tbl_row, h_in, h_op_eq, _, h_na_eq, h_nb_eq, h_np_eq, h_nr_eq⟩ :=
    arith_table_lookup_sound_div v row
  have h_tbl_op : tbl_row.op = OP_REM_W := h_op_eq.symm.trans h_op
  have lift : ∀ (a b c d : Nat),
      tbl_row.na = a → tbl_row.nb = b → tbl_row.np = c → tbl_row.nr = d →
      v.na row = (a : FGL) ∧ v.nb row = (b : FGL)
        ∧ v.np row = (c : FGL) ∧ v.nr row = (d : FGL) := by
    intro a b c d hna hnb hnp hnr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h_na_eq, hna]
    · rw [h_nb_eq, hnb]
    · rw [h_np_eq, hnp]
    · rw [h_nr_eq, hnr]
  rcases arith_table_op_rem_w_witnesses_disj tbl_row h_in h_tbl_op with
    ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩ | ⟨hna, hnb, hnp, hnr⟩
    | ⟨hna, hnb, hnp, hnr⟩
  · exact Or.inl (by simpa using lift 0 0 0 0 hna hnb hnp hnr)
  · exact Or.inr (Or.inl (by simpa using lift 1 0 0 0 hna hnb hnp hnr))
  · exact Or.inr (Or.inr (Or.inl (by simpa using lift 0 1 0 0 hna hnb hnp hnr)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 1 0 0 hna hnb hnp hnr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 0 hna hnb hnp hnr)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 0 hna hnb hnp hnr))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 0 1 1 hna hnb hnp hnr)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 1 0 1 1 hna hnb hnp hnr))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa using lift 0 1 1 1 hna hnb hnp hnr)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using lift 1 1 1 0 hna hnb hnp hnr)))))))))

/-! ## Table-closed wrappers (item 2 closure)

Wrappers that retire the scope-honest `(h_na, h_nb, h_np, h_nr)`
parameters on the unsigned-mode packed-correct lemmas by invoking
the `arith_table_*_witnesses` specializations internally.

Callers need only supply the opcode + mode hypotheses; the four sign
witnesses are derived from the arith_table lookup.
-/

/-- Table-closed wrapper for `arith_mul_unsigned_packed_correct_bundled`.
    Drops `(h_na, h_nb, h_np, h_nr)` in favor of the `(h_op, h_m32)`
    pair that identifies this as a MULU row. -/
theorem arith_mul_unsigned_packed_correct_table_closed
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (v : Valid_ArithMul C FGL FGL) (row : ℕ)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v row)
    (h_op : v.op row = OP_MULU) (h_sext : v.sext row = 0)
    (h_m32 : v.m32 row = 0) (h_div : v.div row = 0) :
    ZiskFv.Airs.ArithMul.a_chunks_packed v row
      * ZiskFv.Airs.ArithMul.b_chunks_packed v row
      = ZiskFv.Airs.ArithMul.c_chunks_packed v row
        + ZiskFv.Airs.ArithMul.d_chunks_packed v row
          * (65536 * 65536 * 65536 * 65536) := by
  obtain ⟨h_na, h_nb, h_np, h_nr⟩ := arith_table_mulu_witnesses v row h_op h_m32
  exact ZiskFv.Airs.ArithMul.arith_mul_unsigned_packed_correct_bundled
    v row h_chain h_na h_nb h_np h_nr h_sext h_m32 h_div

end ZiskFv.Airs.Arith.ArithTable
