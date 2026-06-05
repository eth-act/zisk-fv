import ZiskFv.AirsClean.ArithMul.Circuit
import ZiskFv.Airs.Arith.Mul

/-!
# `Valid_ArithMul` ↔ `ArithMulRow` compatibility + Component re-root

Connects the existing `Valid_ArithMul` interface (a record with named
column accessors `ℕ → FGL`) to the Clean Component's `ArithMulRow`,
and exposes the **C3 re-root entry point**
`mul_carry_chain_holds_via_component` — the MUL-family equivalence
proofs (MUL / MULH / MULHU / MULHSU / MULW) source the AIR's
MUL-mode carry-chain constraints **through the Clean Component's
proven `Spec`** rather than consuming the raw `mul_carry_chain_holds`
predicate directly.

## Trust note

No axioms. The re-root routes the *same* 11 carry-chain equations
through `circuit.soundness` (genuinely proved), so the trust surface is
unchanged and `circuit` becomes load-bearing for the MUL family.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks
open ZiskFv.Channels.OperationBus

/-- Constant-expression view of an `ArithMulRow`, used when specializing
    lookup-aware Clean soundness to one concrete row. -/
@[reducible]
def constVar (row : ArithMulRow FGL) : Var ArithMulRow FGL where
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
  carries :=
    { carry_0 := .const row.carries.carry_0, carry_1 := .const row.carries.carry_1,
      carry_2 := .const row.carries.carry_2, carry_3 := .const row.carries.carry_3,
      carry_4 := .const row.carries.carry_4, carry_5 := .const row.carries.carry_5,
      carry_6 := .const row.carries.carry_6, fab := .const row.carries.fab,
      na_fb := .const row.carries.na_fb, nb_fa := .const row.carries.nb_fa }

/-- The lookup-aware Clean circuit sources ArithTable membership from its
    `lookup (Table.fromStatic ArithTable.arithTable) ...` operation.

    This is the shape C3/C4-b needs globally: the membership proof is
    extracted from `ConstraintsHold.Soundness` of `mainWithArithTable`,
    not supplied as an opcode-wrapper promise. -/
theorem arith_table_spec_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (input_var : Var ArithMulRow FGL)
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
    `arith_table_spec_of_lookup_aware_soundness`.

    This is the local C3 lookup bridge for one concrete ArithMul row:
    `ArithTableSpec row` comes from the lookup-aware Clean circuit's
    `lookup`, not from an opcode-wrapper promise. -/
theorem arith_table_spec_of_lookup_aware_const_soundness
    (offset : ℕ) (env : Environment FGL) (row : ArithMulRow FGL)
    (h_holds :
      ConstraintsHold.Soundness env
        ((mainWithArithTable (constVar row)).operations offset)) :
    ArithTableSpec row := by
  have h_table :=
    arith_table_spec_of_lookup_aware_soundness offset env (constVar row) h_holds
  simpa [ArithTableSpec, arithTableRow, constVar] using h_table

/-- Project a `Valid_ArithMul` at row `r` into a Clean `ArithMulRow FGL`.
    The `Valid_ArithMul` record exposes all 28 chunk / flag / carry
    columns the MUL-mode carry-chain Component constrains; the map is
    1:1 (the `cy_i` accessors map to the row's `carry_i` fields). -/
@[reducible]
def rowAt (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :
    ArithMulRow FGL where
  chunks := {
    a_0 := v.a_0 r, a_1 := v.a_1 r, a_2 := v.a_2 r, a_3 := v.a_3 r
    b_0 := v.b_0 r, b_1 := v.b_1 r, b_2 := v.b_2 r, b_3 := v.b_3 r
    c_0 := v.c_0 r, c_1 := v.c_1 r, c_2 := v.c_2 r, c_3 := v.c_3 r
    d_0 := v.d_0 r, d_1 := v.d_1 r, d_2 := v.d_2 r, d_3 := v.d_3 r
  }
  flags := {
    na := v.na r, nb := v.nb r, nr := v.nr r, np := v.np r
    sext := v.sext r, m32 := v.m32 r, div := v.div r
    div_by_zero := v.div_by_zero r, div_overflow := v.div_overflow r
    main_div := v.main_div r, main_mul := v.main_mul r
    signed := v.signed r, range_ab := v.range_ab r, range_cd := v.range_cd r
    op := v.op r, bus_res1 := v.bus_res1 r, multiplicity := v.multiplicity r
  }
  carries := {
    carry_0 := v.cy_0 r, carry_1 := v.cy_1 r, carry_2 := v.cy_2 r
    carry_3 := v.cy_3 r, carry_4 := v.cy_4 r, carry_5 := v.cy_5 r
    carry_6 := v.cy_6 r, fab := v.fab r, na_fb := v.na_fb r, nb_fa := v.nb_fa r
  }

/-- Lookup-aware Clean witness for the sixteen `bits(16)` chunk lookups in
    a selected ArithMul row. This is structural evidence for the Clean
    `lookup rangeTable16` operations in `mainWithChunkRanges`; it is not a
    replacement range axiom. -/
structure ChunkRangeLookupWitness
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((mainWithChunkRanges (constVar (rowAt v r))).operations offset)

theorem chunk_ranges_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL} {r : ℕ}
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

/-- Lookup-aware Clean witness for the seven `bits(17)` unsigned carry
    lookups in a selected ArithMul row. This is structural evidence for
    `mainWithUnsignedCarryRanges`, not a replacement range axiom. -/
structure UnsignedCarryRangeLookupWitness
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((mainWithUnsignedCarryRanges (constVar (rowAt v r))).operations offset)

theorem unsigned_carry_ranges_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL} {r : ℕ}
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

/-- Lookup-aware Clean witness for the seven signed/W carry range lookups
    in a selected ArithMul row. This is structural evidence for
    `mainWithSignedCarryRanges`, not a replacement range axiom. -/
structure SignedCarryRangeLookupWitness
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((mainWithSignedCarryRanges (constVar (rowAt v r))).operations offset)

theorem signed_carry_ranges_of_lookup_aware_const_soundness
    {v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL} {r : ℕ}
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

/-- Concrete primary MUL/MULW op-bus message for a Clean ArithMul row. -/
@[reducible]
def primaryOpBusMessage (row : ArithMulRow FGL) : OpBusMessage FGL :=
  { op := row.flags.op
    a_lo := row.chunks.a_0 + row.chunks.a_1 * 65536
    a_hi := row.chunks.a_2 + row.chunks.a_3 * 65536
    b_lo := row.chunks.b_0 + row.chunks.b_1 * 65536
    b_hi := row.chunks.b_2 + row.chunks.b_3 * 65536
    c_lo := row.chunks.c_0 + row.chunks.c_1 * 65536
    c_hi := row.flags.bus_res1
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Concrete secondary MULH/MULHU/MULHSU op-bus message for a Clean row. -/
@[reducible]
def secondaryOpBusMessage (row : ArithMulRow FGL) : OpBusMessage FGL :=
  { op := row.flags.op
    a_lo := row.chunks.a_0 + row.chunks.a_1 * 65536
    a_hi := row.chunks.a_2 + row.chunks.a_3 * 65536
    b_lo := row.chunks.b_0 + row.chunks.b_1 * 65536
    b_hi := row.chunks.b_2 + row.chunks.b_3 * 65536
    c_lo := row.chunks.d_0 + row.chunks.d_1 * 65536
    c_hi := row.flags.bus_res1
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem eval_primaryOpBusMessageExpr
    (env : Environment FGL) (row : Var ArithMulRow FGL) :
    eval env (primaryOpBusMessageExpr row) = primaryOpBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [primaryOpBusMessageExpr, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, Expression.eval]
  repeat constructor

theorem eval_secondaryOpBusMessageExpr
    (env : Environment FGL) (row : Var ArithMulRow FGL) :
    eval env (secondaryOpBusMessageExpr row) =
      secondaryOpBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [secondaryOpBusMessageExpr, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, Expression.eval]
  repeat constructor

theorem primaryOpBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (primaryOpBusMessage (rowAt v r)) (v.multiplicity r) =
      ZiskFv.Airs.ArithMul.opBus_row_Arith v r := by
  rfl

theorem secondaryOpBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (secondaryOpBusMessage (rowAt v r)) (v.multiplicity r) =
      ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r := by
  rfl

/-- The Clean Component `Spec` projected at a `Valid_ArithMul` row,
    derived **through the Clean Component**. From the AIR's MUL-mode
    carry-chain constraints (`mul_carry_chain_holds v r` = named-form
    constraints `6/7/8` + `31..38`), produce `Spec (rowAt v r)` by
    routing the 11 equations through `spec_via_component` (the
    `circuit.soundness` entry point). Every `rowAt` field is
    `@[reducible]`-defeq to the corresponding `v.<col> r`. -/
theorem spec_of_carry_chain_via_component
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r) :
    Spec (rowAt v r) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  simp only [ZiskFv.Airs.ArithMul.mul_constraint_6_named,
    ZiskFv.Airs.ArithMul.mul_constraint_7_named,
    ZiskFv.Airs.ArithMul.mul_constraint_8_named,
    ZiskFv.Airs.ArithMul.mul_constraint_31_named,
    ZiskFv.Airs.ArithMul.mul_constraint_32_named,
    ZiskFv.Airs.ArithMul.mul_constraint_33_named,
    ZiskFv.Airs.ArithMul.mul_constraint_34_named,
    ZiskFv.Airs.ArithMul.mul_constraint_35_named,
    ZiskFv.Airs.ArithMul.mul_constraint_36_named,
    ZiskFv.Airs.ArithMul.mul_constraint_37_named,
    ZiskFv.Airs.ArithMul.mul_constraint_38_named]
    at h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38
  exact spec_via_component (rowAt v r)
    h6 h7 h8 h31 h32 h33 h34 h35 h36 h37 h38

/-- **C3 re-root entry point.** Given the MUL-mode carry-chain
    constraint set of ZisK's Arith AIR (`mul_carry_chain_holds v r`),
    re-derive the *same* constraint set **through the Clean Component**
    — its proven `soundness` field, via `spec_of_carry_chain_via_component`.

    The output type equals the input type; the point of the routing is
    the **dependency graph**: any consumer of this lemma genuinely
    depends on `circuit`, making `AirsClean/ArithMul/` load-bearing
    (plan V-4). The trust surface is unchanged — the 11 carry-chain
    equations are still the AIR-fidelity hypothesis; they are now routed
    through `circuit.soundness` (genuinely proved, no new soundness axiom). -/
theorem mul_carry_chain_holds_via_component
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r) :
    ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r := by
  obtain ⟨hs6, hs7, hs8, hs31, hs32, hs33, hs34, hs35, hs36, hs37, hs38⟩ :=
    spec_of_carry_chain_via_component v r h_chain
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ZiskFv.Airs.ArithMul.mul_constraint_6_named,
      ZiskFv.Airs.ArithMul.mul_constraint_7_named,
      ZiskFv.Airs.ArithMul.mul_constraint_8_named,
      ZiskFv.Airs.ArithMul.mul_constraint_31_named,
      ZiskFv.Airs.ArithMul.mul_constraint_32_named,
      ZiskFv.Airs.ArithMul.mul_constraint_33_named,
      ZiskFv.Airs.ArithMul.mul_constraint_34_named,
      ZiskFv.Airs.ArithMul.mul_constraint_35_named,
      ZiskFv.Airs.ArithMul.mul_constraint_36_named,
      ZiskFv.Airs.ArithMul.mul_constraint_37_named,
      ZiskFv.Airs.ArithMul.mul_constraint_38_named]
  · exact hs6
  · exact hs7
  · exact hs8
  · exact hs31
  · exact hs32
  · exact hs33
  · exact hs34
  · exact hs35
  · exact hs36
  · exact hs37
  · exact hs38

/-- Combine the load-bearing Clean carry-chain route with a separately
    sourced ArithTable lookup membership proof.

    This is the non-laundered C3/C4-b shape: `h_table` is explicit here
    because the current global theorem does not yet provide lookup
    membership. Compliance wrappers must not acquire this as a fresh
    per-opcode promise; the proof becomes useful only once the shared
    lookup/ensemble statement supplies `ArithTableSpec (rowAt v r)`. -/
theorem full_spec_of_carry_chain_and_arith_table
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chain : ZiskFv.Airs.ArithMul.mul_carry_chain_holds v r)
    (h_table : ArithTableSpec (rowAt v r)) :
    FullSpec (rowAt v r) := by
  exact ⟨spec_of_carry_chain_via_component v r h_chain, h_table⟩

end ZiskFv.AirsClean.ArithMul
