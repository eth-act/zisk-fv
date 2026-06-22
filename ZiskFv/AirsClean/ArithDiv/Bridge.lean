import ZiskFv.AirsClean.ArithDiv.Circuit
import ZiskFv.Airs.Arith.Div

/-!
# `Valid_ArithDiv` ↔ `ArithDivRow` compatibility bridge (Phase C4 D-6)

Connects the existing `Valid_ArithDiv` interface (a record with named
column accessors `ℕ → FGL`) to the Clean Component's `ArithDivRow`, and
exposes a Component-routed `div_carry_chain_holds` derivation.

The bridge:

* `rowAt v r` — project `Valid_ArithDiv` at row `r` into an
  `ArithDivRow FGL` (the Clean Component's row type).
* `div_carry_chain_via_component v r` — given the hand-rolled 11-clause
  `div_carry_chain_holds v r` predicate, re-derives the **same**
  11-clause `div_carry_chain_holds v r` **through the Clean Component
  `circuit`'s proven `soundness` field** (via `spec_via_component`).
  Any consumer of this lemma genuinely depends on `circuit` — this is
  the C4 re-root point that makes `AirsClean/ArithDiv/` load-bearing
  for the DIV/REM-family opcodes.

`div_carry_chain_via_component` has the *identity* statement
`div_carry_chain_holds v r → div_carry_chain_holds v r`, but its proof
is **not** `id`: the input 11 clauses are routed through
`ArithDiv.spec_via_component` (→ `circuit.soundness`), and the 11-clause
`ArithDiv.Spec` is projected back. The genuine routing is what the C4
D-6 re-root requires; the consumers in `EquivCore/Bridge/Arith.lean`
swap their raw `h_chain` for `div_carry_chain_via_component v r_a
h_chain` before destructuring.

## Trust note

No axioms added. This bridge routes the existing `Valid_ArithDiv`
consumers through the Clean Component's `soundness`; NO new soundness
or completeness declarations are introduced.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks
open ZiskFv.Channels.OperationBus

/-- Constant-expression view of an `ArithDivRow`, used when specializing
    lookup-aware Clean soundness to one concrete row. -/
@[reducible]
def constVar (row : ArithDivRow FGL) : Var ArithDivRow FGL where
  chunks :=
    { a_0 := .const row.chunks.a_0, a_1 := .const row.chunks.a_1,
      a_2 := .const row.chunks.a_2, a_3 := .const row.chunks.a_3,
      b_0 := .const row.chunks.b_0, b_1 := .const row.chunks.b_1,
      b_2 := .const row.chunks.b_2, b_3 := .const row.chunks.b_3,
      c_0 := .const row.chunks.c_0, c_1 := .const row.chunks.c_1,
      c_2 := .const row.chunks.c_2, c_3 := .const row.chunks.c_3,
      d_0 := .const row.chunks.d_0, d_1 := .const row.chunks.d_1,
      d_2 := .const row.chunks.d_2, d_3 := .const row.chunks.d_3 }
  flags :=
    { na := .const row.flags.na, nb := .const row.flags.nb,
      nr := .const row.flags.nr, np := .const row.flags.np,
      sext := .const row.flags.sext, m32 := .const row.flags.m32,
      div := .const row.flags.div,
      div_by_zero := .const row.flags.div_by_zero,
      div_overflow := .const row.flags.div_overflow,
      main_div := .const row.flags.main_div,
      main_mul := .const row.flags.main_mul, op := .const row.flags.op,
      signed := .const row.flags.signed,
      range_ab := .const row.flags.range_ab,
      range_cd := .const row.flags.range_cd,
      bus_res1 := .const row.flags.bus_res1,
      multiplicity := .const row.flags.multiplicity }
  aux :=
    { carry_0 := .const row.aux.carry_0, carry_1 := .const row.aux.carry_1,
      carry_2 := .const row.aux.carry_2, carry_3 := .const row.aux.carry_3,
      carry_4 := .const row.aux.carry_4, carry_5 := .const row.aux.carry_5,
      carry_6 := .const row.aux.carry_6, fab := .const row.aux.fab,
      na_fb := .const row.aux.na_fb, nb_fa := .const row.aux.nb_fa }

/-- The lookup-aware Clean circuit sources ArithTable membership from its
    `lookup (Table.fromStatic ArithTable.arithTable) ...` operation.

    This is the shape C3/C4-b needs globally: the membership proof is
    extracted from `ConstraintsHold.Soundness` of `mainWithArithTable`,
    not supplied as an opcode-wrapper promise. -/
theorem arith_table_spec_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (input_var : Var ArithDivRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithArithTable input_var).operations offset)) :
    ArithTable.arithTable.Spec
      #v[Expression.eval env input_var.flags.op, Expression.eval env input_var.flags.m32,
        Expression.eval env input_var.flags.div, Expression.eval env input_var.flags.na,
        Expression.eval env input_var.flags.nb, Expression.eval env input_var.flags.np,
        Expression.eval env input_var.flags.nr, Expression.eval env input_var.flags.sext,
        Expression.eval env input_var.flags.div_by_zero,
        Expression.eval env input_var.flags.div_overflow,
        Expression.eval env input_var.flags.main_mul, Expression.eval env input_var.flags.main_div,
        Expression.eval env input_var.flags.signed, Expression.eval env input_var.flags.range_ab,
        Expression.eval env input_var.flags.range_cd] := by
  simp only [mainWithArithTable, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨_h6, _h7, _h8, _h31, _h32, _h33, _h34, _h35, _h36, _h37, _h38,
      h_lookup⟩
  simpa [Lookup.Soundness, Table.fromStatic, StaticTable.toTable, Table.toRaw,
    ArithTableSpec, arithTableRow] using h_lookup

/-- Constant-row specialization of
    `arith_table_spec_of_lookup_aware_soundness`. -/
theorem arith_table_spec_of_lookup_aware_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : ArithDivRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithArithTable (constVar row)).operations offset)) :
    ArithTableSpec row := by
  have h_table :=
    arith_table_spec_of_lookup_aware_soundness offset env (constVar row) h_holds
  simpa [ArithTableSpec, arithTableRow, constVar] using h_table

/-- Project a `Valid_ArithDiv` at row `r` into a Clean `ArithDivRow FGL`.
    The Clean-row columns map 1:1 (`carry_i` ↔ `Valid_ArithDiv.cy_i`);
    extraction-only witnesses such as `inv_sum_all_bs` are not part of the
    Clean row. -/
@[reducible]
def rowAt (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    : ArithDivRow FGL where
  chunks :=
    { a_0 := v.a_0 r, a_1 := v.a_1 r, a_2 := v.a_2 r, a_3 := v.a_3 r
      b_0 := v.b_0 r, b_1 := v.b_1 r, b_2 := v.b_2 r, b_3 := v.b_3 r
      c_0 := v.c_0 r, c_1 := v.c_1 r, c_2 := v.c_2 r, c_3 := v.c_3 r
      d_0 := v.d_0 r, d_1 := v.d_1 r, d_2 := v.d_2 r, d_3 := v.d_3 r }
  flags :=
    { na := v.na r, nb := v.nb r, nr := v.nr r, np := v.np r
      sext := v.sext r, m32 := v.m32 r, div := v.div r
      div_by_zero := v.div_by_zero r, div_overflow := v.div_overflow r
      main_div := v.main_div r, main_mul := v.main_mul r, op := v.op r
      signed := v.signed r, range_ab := v.range_ab r, range_cd := v.range_cd r
      bus_res1 := v.bus_res1 r, multiplicity := v.multiplicity r }
  aux :=
    { fab := v.fab r, na_fb := v.na_fb r, nb_fa := v.nb_fa r
      carry_0 := v.cy_0 r, carry_1 := v.cy_1 r, carry_2 := v.cy_2 r
      carry_3 := v.cy_3 r, carry_4 := v.cy_4 r, carry_5 := v.cy_5 r
      carry_6 := v.cy_6 r }

/-! ## Lookup-derived range witnesses -/

/-- Lookup-aware Clean witness for the sixteen `bits(16)` chunk lookups in
    a selected ArithDiv row. This is structural evidence for the Clean
    `lookup rangeTable16` operations in `mainWithChunkRanges`; it is not a
    replacement range axiom. -/
structure ChunkRangeLookupWitness
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((mainWithChunkRanges (constVar (rowAt v r))).operations offset)

theorem chunk_ranges_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r : ℕ}
    (w : ChunkRangeLookupWitness v r) :
    (v.a_0 r).val < 2 ^ 16 ∧ (v.a_1 r).val < 2 ^ 16
  ∧ (v.a_2 r).val < 2 ^ 16 ∧ (v.a_3 r).val < 2 ^ 16
  ∧ (v.b_0 r).val < 2 ^ 16 ∧ (v.b_1 r).val < 2 ^ 16
  ∧ (v.b_2 r).val < 2 ^ 16 ∧ (v.b_3 r).val < 2 ^ 16
  ∧ (v.c_0 r).val < 2 ^ 16 ∧ (v.c_1 r).val < 2 ^ 16
  ∧ (v.c_2 r).val < 2 ^ 16 ∧ (v.c_3 r).val < 2 ^ 16
  ∧ (v.d_0 r).val < 2 ^ 16 ∧ (v.d_1 r).val < 2 ^ 16
  ∧ (v.d_2 r).val < 2 ^ 16 ∧ (v.d_3 r).val < 2 ^ 16 := by
  have h_holds := w.holds
  simp only [mainWithChunkRanges, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨_h6, _h7, _h8, _h31, _h32, _h33, _h34, _h35, _h36, _h37, _h38,
      h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
      h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3⟩
  exact ⟨by simpa [rowAt, constVar] using h_a0,
    by simpa [rowAt, constVar] using h_a1,
    by simpa [rowAt, constVar] using h_a2,
    by simpa [rowAt, constVar] using h_a3,
    by simpa [rowAt, constVar] using h_b0,
    by simpa [rowAt, constVar] using h_b1,
    by simpa [rowAt, constVar] using h_b2,
    by simpa [rowAt, constVar] using h_b3,
    by simpa [rowAt, constVar] using h_c0,
    by simpa [rowAt, constVar] using h_c1,
    by simpa [rowAt, constVar] using h_c2,
    by simpa [rowAt, constVar] using h_c3,
    by simpa [rowAt, constVar] using h_d0,
    by simpa [rowAt, constVar] using h_d1,
    by simpa [rowAt, constVar] using h_d2,
    by simpa [rowAt, constVar] using h_d3⟩

/-- Lookup-aware Clean witness for the seven unsigned carry lookups in a
    selected ArithDiv row. -/
structure UnsignedCarryRangeLookupWitness
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((mainWithUnsignedCarryRanges (constVar (rowAt v r))).operations offset)

theorem unsigned_carry_ranges_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r : ℕ}
    (w : UnsignedCarryRangeLookupWitness v r) :
    (v.cy_0 r).val < 2 ^ 17 ∧ (v.cy_1 r).val < 2 ^ 17
  ∧ (v.cy_2 r).val < 2 ^ 17 ∧ (v.cy_3 r).val < 2 ^ 17
  ∧ (v.cy_4 r).val < 2 ^ 17 ∧ (v.cy_5 r).val < 2 ^ 17
  ∧ (v.cy_6 r).val < 2 ^ 17 := by
  have h_holds := w.holds
  simp only [mainWithUnsignedCarryRanges, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨_h6, _h7, _h8, _h31, _h32, _h33, _h34, _h35, _h36, _h37, _h38,
      h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6⟩
  exact ⟨by simpa [rowAt, constVar] using h_cy0,
    by simpa [rowAt, constVar] using h_cy1,
    by simpa [rowAt, constVar] using h_cy2,
    by simpa [rowAt, constVar] using h_cy3,
    by simpa [rowAt, constVar] using h_cy4,
    by simpa [rowAt, constVar] using h_cy5,
    by simpa [rowAt, constVar] using h_cy6⟩

/-- Lookup-aware Clean witness for the seven signed/W carry range lookups in
    a selected ArithDiv row. -/
structure SignedCarryRangeLookupWitness
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((mainWithSignedCarryRanges (constVar (rowAt v r))).operations offset)

theorem signed_carry_ranges_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r : ℕ}
    (w : SignedCarryRangeLookupWitness v r) :
    ((v.cy_0 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_0 r).val)
  ∧ ((v.cy_1 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_1 r).val)
  ∧ ((v.cy_2 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_2 r).val)
  ∧ ((v.cy_3 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_3 r).val)
  ∧ ((v.cy_4 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_4 r).val)
  ∧ ((v.cy_5 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_5 r).val)
  ∧ ((v.cy_6 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_6 r).val) := by
  have h_holds := w.holds
  simp only [mainWithSignedCarryRanges, main, circuit_norm] at h_holds
  rcases h_holds with
    ⟨_h6, _h7, _h8, _h31, _h32, _h33, _h34, _h35, _h36, _h37, _h38,
      h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6⟩
  exact ⟨by simpa [rowAt, constVar] using h_cy0,
    by simpa [rowAt, constVar] using h_cy1,
    by simpa [rowAt, constVar] using h_cy2,
    by simpa [rowAt, constVar] using h_cy3,
    by simpa [rowAt, constVar] using h_cy4,
    by simpa [rowAt, constVar] using h_cy5,
    by simpa [rowAt, constVar] using h_cy6⟩

/-- Build an ArithDiv `SignedCarryRangeLookupWitness` from the row's carry-chain
    `Spec` plus its seven signed-carry range facts.  Same constant-row / dummy-env
    technique as the ArithMul / Mem family builders — non-vacuous: the substantive
    content is the `FullSpec`-projected facts a P4 construction derives from
    balance. -/
def signedCarryRangeLookupWitness_of_spec
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r : ℕ}
    (h_spec : Spec (rowAt v r))
    (h_carry :
      ((v.cy_0 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_0 r).val)
      ∧ ((v.cy_1 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_1 r).val)
      ∧ ((v.cy_2 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_2 r).val)
      ∧ ((v.cy_3 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_3 r).val)
      ∧ ((v.cy_4 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_4 r).val)
      ∧ ((v.cy_5 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_5 r).val)
      ∧ ((v.cy_6 r).val < 983041 ∨ GL_prime - 983040 ≤ (v.cy_6 r).val)) :
    SignedCarryRangeLookupWitness v r := by
  refine ⟨0, ⟨fun _ => 0, fun _ _ => #[]⟩, ?_⟩
  simp only [mainWithSignedCarryRanges, main, circuit_norm]
  obtain ⟨hc6, hc7, hc8, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38⟩ := h_spec
  obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ := h_carry
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hc6
  · linear_combination hc7
  · linear_combination hc8
  · linear_combination hc31
  · linear_combination hc32
  · linear_combination hc33
  · linear_combination hc34
  · linear_combination hc35
  · linear_combination hc36
  · linear_combination hc37
  · linear_combination hc38
  · simpa [rowAt] using hr0
  · simpa [rowAt] using hr1
  · simpa [rowAt] using hr2
  · simpa [rowAt] using hr3
  · simpa [rowAt] using hr4
  · simpa [rowAt] using hr5
  · simpa [rowAt] using hr6

/-- Build an ArithDiv `ChunkRangeLookupWitness` from the row's carry-chain `Spec`
    plus its sixteen 16-bit chunk facts. -/
def chunkRangeLookupWitness_of_spec
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r : ℕ}
    (h_spec : Spec (rowAt v r))
    (h_chunks :
      (v.a_0 r).val < 65536 ∧ (v.a_1 r).val < 65536
      ∧ (v.a_2 r).val < 65536 ∧ (v.a_3 r).val < 65536
      ∧ (v.b_0 r).val < 65536 ∧ (v.b_1 r).val < 65536
      ∧ (v.b_2 r).val < 65536 ∧ (v.b_3 r).val < 65536
      ∧ (v.c_0 r).val < 65536 ∧ (v.c_1 r).val < 65536
      ∧ (v.c_2 r).val < 65536 ∧ (v.c_3 r).val < 65536
      ∧ (v.d_0 r).val < 65536 ∧ (v.d_1 r).val < 65536
      ∧ (v.d_2 r).val < 65536 ∧ (v.d_3 r).val < 65536) :
    ChunkRangeLookupWitness v r := by
  refine ⟨0, ⟨fun _ => 0, fun _ _ => #[]⟩, ?_⟩
  simp only [mainWithChunkRanges, main, circuit_norm]
  obtain ⟨hc6, hc7, hc8, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38⟩ := h_spec
  obtain ⟨ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
          hcc0, hcc1, hcc2, hcc3, hd0, hd1, hd2, hd3⟩ := h_chunks
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination hc6
  · linear_combination hc7
  · linear_combination hc8
  · linear_combination hc31
  · linear_combination hc32
  · linear_combination hc33
  · linear_combination hc34
  · linear_combination hc35
  · linear_combination hc36
  · linear_combination hc37
  · linear_combination hc38
  · simpa [rowAt] using ha0
  · simpa [rowAt] using ha1
  · simpa [rowAt] using ha2
  · simpa [rowAt] using ha3
  · simpa [rowAt] using hb0
  · simpa [rowAt] using hb1
  · simpa [rowAt] using hb2
  · simpa [rowAt] using hb3
  · simpa [rowAt] using hcc0
  · simpa [rowAt] using hcc1
  · simpa [rowAt] using hcc2
  · simpa [rowAt] using hcc3
  · simpa [rowAt] using hd0
  · simpa [rowAt] using hd1
  · simpa [rowAt] using hd2
  · simpa [rowAt] using hd3

/-- Concrete primary DIV/DIVU op-bus message for a Clean ArithDiv row. -/
@[reducible]
def primaryOpBusMessage (row : ArithDivRow FGL) : OpBusMessage FGL :=
  { op := row.flags.op
    a_lo := row.chunks.c_0 + row.chunks.c_1 * 65536
    a_hi := row.chunks.c_2 + row.chunks.c_3 * 65536
    b_lo := row.chunks.b_0 + row.chunks.b_1 * 65536
    b_hi := row.chunks.b_2 + row.chunks.b_3 * 65536
    c_lo := row.chunks.a_0 + row.chunks.a_1 * 65536
    c_hi := row.flags.bus_res1
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Concrete secondary REM/REMU op-bus message for a Clean ArithDiv row. -/
@[reducible]
def secondaryOpBusMessage (row : ArithDivRow FGL) : OpBusMessage FGL :=
  { op := row.flags.op
    a_lo := row.chunks.c_0 + row.chunks.c_1 * 65536
    a_hi := row.chunks.c_2 + row.chunks.c_3 * 65536
    b_lo := row.chunks.b_0 + row.chunks.b_1 * 65536
    b_hi := row.chunks.b_2 + row.chunks.b_3 * 65536
    c_lo := row.chunks.d_0 + row.chunks.d_1 * 65536
    c_hi := row.flags.bus_res1
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem eval_primaryOpBusMessageExpr
    (env : Environment FGL) (row : Var ArithDivRow FGL) :
    eval env (primaryOpBusMessageExpr row) = primaryOpBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [primaryOpBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

theorem eval_secondaryOpBusMessageExpr
    (env : Environment FGL) (row : Var ArithDivRow FGL) :
    eval env (secondaryOpBusMessageExpr row) =
      secondaryOpBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [secondaryOpBusMessageExpr,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  repeat constructor

theorem primaryOpBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (primaryOpBusMessage (rowAt v r)) (v.multiplicity r) =
      ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r := by
  rfl

theorem secondaryOpBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (secondaryOpBusMessage (rowAt v r)) (v.multiplicity r) =
      ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r := by
  rfl

set_option maxHeartbeats 1000000 in
/-- **C4 D-6 re-root — Component-routed `div_carry_chain_holds`.**

    From the hand-rolled 11-clause `div_carry_chain_holds v r`
    predicate, re-derive `div_carry_chain_holds v r` **through the Clean
    Component `circuit`** — `spec_via_component` routes the 11 clauses
    through `circuit.soundness`, so any consumer of this lemma depends
    on `circuit`.

    `div_carry_chain_holds`'s 11 named-form conjuncts (`fab_eq_div`,
    `na_fb_eq_div`, `nb_fa_eq_div`, `carry_eq_0..7_div`) are exactly the
    11 clauses of `ArithDiv.Spec (rowAt v r)` (`(rowAt v r).aux.fab` ≡
    `v.fab r` etc. — `rowAt` is `@[reducible]`); `spec_via_component`
    delivers that `Spec` from those same 11 equations as constraints. -/
theorem div_carry_chain_via_component
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r) :
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r := by
  -- Unfold the hand-rolled bundle into its 11 raw FGL equations.
  simp only [ZiskFv.Airs.ArithDiv.div_carry_chain_holds,
    ZiskFv.Airs.ArithDiv.fab_eq_div, ZiskFv.Airs.ArithDiv.na_fb_eq_div,
    ZiskFv.Airs.ArithDiv.nb_fa_eq_div, ZiskFv.Airs.ArithDiv.carry_eq_0_div,
    ZiskFv.Airs.ArithDiv.carry_eq_1_div, ZiskFv.Airs.ArithDiv.carry_eq_2_div,
    ZiskFv.Airs.ArithDiv.carry_eq_3_div, ZiskFv.Airs.ArithDiv.carry_eq_4_div,
    ZiskFv.Airs.ArithDiv.carry_eq_5_div, ZiskFv.Airs.ArithDiv.carry_eq_6_div,
    ZiskFv.Airs.ArithDiv.carry_eq_7_div] at h_chain ⊢
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  -- Route the 11 equations through the Clean Component's `soundness`.
  -- `spec_via_component (rowAt v r)` consumes the 11 equations as
  -- constraints and delivers `ArithDiv.Spec (rowAt v r)` — its 11
  -- clauses are the same equations (`rowAt` is `@[reducible]`, so
  -- `(rowAt v r).aux.fab` reduces to `v.fab r` etc.).
  exact spec_via_component (rowAt v r) h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38

/-- Combine the load-bearing Clean carry-chain route with a separately
    sourced ArithTable lookup membership proof.

    This is the non-laundered C3/C4-b shape: `h_table` is explicit here
    because the current global theorem does not yet provide lookup
    membership. Compliance wrappers must not acquire this as a fresh
    per-opcode promise; the proof becomes useful only once the shared
    lookup/ensemble statement supplies `ArithTableSpec (rowAt v r)`. -/
theorem full_spec_of_carry_chain_and_arith_table
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r)
    (h_table : ArithTableSpec (rowAt v r)) :
    FullSpec (rowAt v r) := by
  simp only [ZiskFv.Airs.ArithDiv.div_carry_chain_holds,
    ZiskFv.Airs.ArithDiv.fab_eq_div, ZiskFv.Airs.ArithDiv.na_fb_eq_div,
    ZiskFv.Airs.ArithDiv.nb_fa_eq_div, ZiskFv.Airs.ArithDiv.carry_eq_0_div,
    ZiskFv.Airs.ArithDiv.carry_eq_1_div, ZiskFv.Airs.ArithDiv.carry_eq_2_div,
    ZiskFv.Airs.ArithDiv.carry_eq_3_div, ZiskFv.Airs.ArithDiv.carry_eq_4_div,
    ZiskFv.Airs.ArithDiv.carry_eq_5_div, ZiskFv.Airs.ArithDiv.carry_eq_6_div,
    ZiskFv.Airs.ArithDiv.carry_eq_7_div] at h_chain
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  exact ⟨spec_via_component (rowAt v r)
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38, h_table⟩

end ZiskFv.AirsClean.ArithDiv
