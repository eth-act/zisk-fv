import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.Bits.PackedBitVec.MulNoWrap

/-!
# ArithTable projection lemmas from Clean lookup membership

These lemmas are the data-half replacements for the old
`arith_table_op_*` axioms. They deliberately require
`ArithTableSpec (rowAt v r)`, i.e. the lookup-membership fact produced by
the lookup-aware Clean Arith entry points. They are not wired into
Compliance until that membership is sourced globally.

No axioms.
-/

namespace ZiskFv.AirsClean.ArithTableProjections

open Goldilocks
open ZiskFv.PackedBitVec.MulNoWrap (packed4)

@[reducible]
def packed2 (c₀ c₁ : ℕ) : ℕ :=
  c₀ + c₁ * 65536

private lemma packed4_msb64_eq_zero_of_high_pos
    {c₀ c₁ c₂ c₃ : ℕ}
    (h₀ : c₀ < 65536) (h₁ : c₁ < 65536) (h₂ : c₂ < 65536)
    (h₃ : c₃ < 32768) :
    (if 2 ^ 63 ≤ packed4 c₀ c₁ c₂ c₃ then 1 else 0) = 0 := by
  have hlt : packed4 c₀ c₁ c₂ c₃ < 2 ^ 63 := by
    unfold packed4
    norm_num
    nlinarith [h₀, h₁, h₂, h₃]
  exact if_neg (Nat.not_le_of_gt hlt)

private lemma packed4_msb64_eq_one_of_high_neg
    {c₀ c₁ c₂ c₃ : ℕ} (h₃ : 32768 ≤ c₃) :
    (if 2 ^ 63 ≤ packed4 c₀ c₁ c₂ c₃ then 1 else 0) = 1 := by
  have hge : 2 ^ 63 ≤ packed4 c₀ c₁ c₂ c₃ := by
    unfold packed4
    norm_num
    nlinarith [h₃, Nat.zero_le c₀, Nat.zero_le c₁, Nat.zero_le c₂]
  exact if_pos hge

private lemma packed2_msb32_eq_zero_of_high_pos
    {c₀ c₁ : ℕ} (h₀ : c₀ < 65536) (h₁ : c₁ < 32768) :
    (if 2 ^ 31 ≤ packed2 c₀ c₁ then 1 else 0) = 0 := by
  have hlt : packed2 c₀ c₁ < 2 ^ 31 := by
    unfold packed2
    norm_num
    nlinarith [h₀, h₁]
  exact if_neg (Nat.not_le_of_gt hlt)

private lemma packed2_msb32_eq_one_of_high_neg
    {c₀ c₁ : ℕ} (h₁ : 32768 ≤ c₁) :
    (if 2 ^ 31 ≤ packed2 c₀ c₁ then 1 else 0) = 1 := by
  have hge : 2 ^ 31 ≤ packed2 c₀ c₁ := by
    unfold packed2
    norm_num
    nlinarith [h₁, Nat.zero_le c₀]
  exact if_pos hge

/-- A POS indexed Arith range lookup proves a 64-bit sign witness is zero. -/
theorem sign_eq_msb64_of_pos_range_lookup {sign rangeId c₀ c₁ c₂ c₃ : FGL}
    (h_sign : sign = 0)
    (h₀ : c₀.val < 65536) (h₁ : c₁.val < 65536) (h₂ : c₂.val < 65536)
    (h_id : RangeTables.ArithRangePosId rangeId)
    (h_lookup : RangeTables.arithRangeTable.Spec #v[rangeId, c₃]) :
    sign.val = if 2 ^ 63 ≤ packed4 c₀.val c₁.val c₂.val c₃.val then 1 else 0 := by
  have h₃ := RangeTables.arithRangeTable_pos_bound_of_spec h_id h_lookup
  have hif := packed4_msb64_eq_zero_of_high_pos h₀ h₁ h₂ h₃
  rw [h_sign]
  exact hif.symm

/-- A NEG indexed Arith range lookup proves a 64-bit sign witness is one. -/
theorem sign_eq_msb64_of_neg_range_lookup {sign rangeId c₀ c₁ c₂ c₃ : FGL}
    (h_sign : sign = 1)
    (h_id : RangeTables.ArithRangeNegId rangeId)
    (h_lookup : RangeTables.arithRangeTable.Spec #v[rangeId, c₃]) :
    sign.val = if 2 ^ 63 ≤ packed4 c₀.val c₁.val c₂.val c₃.val then 1 else 0 := by
  have h₃ := (RangeTables.arithRangeTable_neg_bound_of_spec h_id h_lookup).1
  have hif := packed4_msb64_eq_one_of_high_neg (c₀ := c₀.val) (c₁ := c₁.val)
    (c₂ := c₂.val) h₃
  rw [h_sign]
  exact hif.symm

/-- A POS indexed Arith range lookup proves a W-mode sign witness is zero. -/
theorem sign_eq_msb32_of_pos_range_lookup {sign rangeId c₀ c₁ : FGL}
    (h_sign : sign = 0)
    (h₀ : c₀.val < 65536)
    (h_id : RangeTables.ArithRangePosId rangeId)
    (h_lookup : RangeTables.arithRangeTable.Spec #v[rangeId, c₁]) :
    sign.val = if 2 ^ 31 ≤ packed2 c₀.val c₁.val then 1 else 0 := by
  have h₁ := RangeTables.arithRangeTable_pos_bound_of_spec h_id h_lookup
  have hif := packed2_msb32_eq_zero_of_high_pos h₀ h₁
  rw [h_sign]
  exact hif.symm

/-- A NEG indexed Arith range lookup proves a W-mode sign witness is one. -/
theorem sign_eq_msb32_of_neg_range_lookup {sign rangeId c₀ c₁ : FGL}
    (h_sign : sign = 1)
    (h_id : RangeTables.ArithRangeNegId rangeId)
    (h_lookup : RangeTables.arithRangeTable.Spec #v[rangeId, c₁]) :
    sign.val = if 2 ^ 31 ≤ packed2 c₀.val c₁.val then 1 else 0 := by
  have h₁ := (RangeTables.arithRangeTable_neg_bound_of_spec h_id h_lookup).1
  have hif := packed2_msb32_eq_one_of_high_neg (c₀ := c₀.val) h₁
  rw [h_sign]
  exact hif.symm

namespace Counterexamples

theorem mulhsu_np_xor_not_static :
    ∃ t : fields 15 FGL,
      ZiskFv.AirsClean.ArithTable.arithTable.Spec t
        ∧ t[0] = 179
        ∧ t[3] = 1
        ∧ t[4] = 0
        ∧ t[5] = 0
        ∧ t[5] ≠ t[3] + t[4] - 2 * t[3] * t[4] := by
  refine ⟨ZiskFv.AirsClean.ArithTable.rows[3], ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨(3 : Fin 74), rfl⟩
  · simp [ZiskFv.AirsClean.ArithTable.rows]

theorem mulh_np_xor_not_static :
    ∃ t : fields 15 FGL,
      ZiskFv.AirsClean.ArithTable.arithTable.Spec t
        ∧ t[0] = 181
        ∧ t[3] = 1
        ∧ t[4] = 0
        ∧ t[5] = 0
        ∧ t[5] ≠ t[3] + t[4] - 2 * t[3] * t[4] := by
  refine ⟨ZiskFv.AirsClean.ArithTable.rows[12], ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨(12 : Fin 74), rfl⟩
  · simp [ZiskFv.AirsClean.ArithTable.rows]

theorem mulw_sext_zero_not_static :
    ∃ t : fields 15 FGL,
      ZiskFv.AirsClean.ArithTable.arithTable.Spec t
        ∧ t[0] = 182
        ∧ t[7] = 1 := by
  refine ⟨ZiskFv.AirsClean.ArithTable.rows[18], ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨(18 : Fin 74), rfl⟩
  · simp [ZiskFv.AirsClean.ArithTable.rows]

theorem divuw_sext_zero_not_static :
    ∃ t : fields 15 FGL,
      ZiskFv.AirsClean.ArithTable.arithTable.Spec t
        ∧ t[0] = 188
        ∧ t[7] = 1 := by
  refine ⟨ZiskFv.AirsClean.ArithTable.rows[46], ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨(46 : Fin 74), rfl⟩
  · simp [ZiskFv.AirsClean.ArithTable.rows]

theorem divw_sext_zero_not_static :
    ∃ t : fields 15 FGL,
      ZiskFv.AirsClean.ArithTable.arithTable.Spec t
        ∧ t[0] = 190
        ∧ t[7] = 1 := by
  refine ⟨ZiskFv.AirsClean.ArithTable.rows[57], ?_⟩
  refine ⟨?_, ?_⟩
  · exact ⟨(57 : Fin 74), rfl⟩
  · simp [ZiskFv.AirsClean.ArithTable.rows]

end Counterexamples

namespace Mul

/-- Every lookup-aware ArithMul row carries an Arith-family opcode.  This is
    the data fact used by full-ensemble provider matching to rule out low
    Binary-family opcodes from the ArithMul branch. -/
theorem op_val_ge_176
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row) :
    176 <= row.flags.op.val := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned,
      _hrange_ab, _hrange_cd⟩
    rw [hop]
    norm_num

/-- Bare-`ArithMulRow` MULW mode pins (mirrors `op_val_ge_176`'s shape — a bare
    row + `ArithTableSpec`, no `Valid_ArithMul`/`rowAt` wrapper).  This lets the
    P4 MULW construction read the mode flags off the balance-selected provider
    `ArithMulRow` WITHOUT routing through `vOfMulwRow`, whose per-field closures
    force a costly whnf of the heavy `Classical.choose` provider row. -/
theorem mulw_mode_pins_of_row
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 182) :
    row.flags.div = 0 ∧ row.flags.main_mul = 1 ∧ row.flags.main_div = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hdiv, hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

/-- Bare-`ArithMulRow` MULHU secondary mode pins (mirrors `mulw_mode_pins_of_row`
    — a bare row + `ArithTableSpec`, no `Valid_ArithMul`/`rowAt` wrapper).  Lets
    the P4 MULHU construction read the secondary mode flags off the
    balance-selected provider `ArithMulRow` WITHOUT routing through a `rowAt`
    view (whose per-field closures force a costly whnf of the heavy
    `Classical.choose` provider row). -/
theorem mulhu_mode_pins_of_row
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 177) :
    row.flags.div = 0 ∧ row.flags.main_mul = 0 ∧ row.flags.main_div = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hdiv, hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

/-- Bare-`ArithMulRow` DIVU mode pins (mirrors `mulw_mode_pins_of_row`).  Reads
    the full unsigned-DIVU mode flags off the balance-selected provider
    `ArithMulRow` (the DIVU provider is the SHARED ArithMul component) WITHOUT
    routing through a `rowAt` view.  At op `184` (`OP_DIVU`) the shared
    74-row ArithTable pins `na = nb = np = nr = sext = m32 = 0`, `div = 1`,
    `main_div = 1`, `main_mul = 0`. -/
theorem divu_mode_pins_of_row
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 184) :
    row.flags.na = 0 ∧ row.flags.nb = 0 ∧ row.flags.np = 0 ∧ row.flags.nr = 0
      ∧ row.flags.sext = 0 ∧ row.flags.m32 = 0 ∧ row.flags.div = 1
      ∧ row.flags.main_div = 1 ∧ row.flags.main_mul = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hsext, hm32, hdiv, hmain_div, hmain_mul⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

/-- Bare-`ArithMulRow` REMU secondary mode pins (mirrors `divu_mode_pins_of_row`
    but for `OP_REMU = 185`).  Reads the full unsigned-REMU mode flags off the
    balance-selected provider `ArithMulRow` (the REMU provider is the SHARED
    ArithMul component) WITHOUT routing through a `rowAt` view.  At op `185`
    (`OP_REMU`) the shared 74-row ArithTable pins
    `na = nb = np = nr = sext = m32 = 0`, `div = 1`, `main_div = 0`,
    `main_mul = 0` (REMU consumes the **secondary** lane — the remainder in
    `d[]` — so `main_div = 0`, unlike DIVU's `main_div = 1`). -/
theorem remu_mode_pins_of_row
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 185) :
    row.flags.na = 0 ∧ row.flags.nb = 0 ∧ row.flags.np = 0 ∧ row.flags.nr = 0
      ∧ row.flags.sext = 0 ∧ row.flags.m32 = 0 ∧ row.flags.div = 1
      ∧ row.flags.main_div = 0 ∧ row.flags.main_mul = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hsext, hm32, hdiv, hmain_div, hmain_mul⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

/-- Bare-`ArithMulRow` DIVUW (W-mode) mode pins (mirrors `divu_mode_pins_of_row`
    but for `OP_DIVU_W = 188`, `m32 = 1`).  Reads the unsigned-DIVUW mode flags
    off the balance-selected provider `ArithMulRow` (the DIVUW provider is the
    SHARED ArithMul component) WITHOUT routing through a `rowAt` view.  At op
    `188` all three shared 74-row ArithTable rows pin
    `na = nb = np = nr = 0`, `m32 = 1`, `div = 1`, `main_div = 1`,
    `main_mul = 0`.  Note `sext` is NOT uniform across the op-188 rows
    (the W-mode sign-extension lives in the `bus_res1` encoding / the
    `h_sext_choice` bus residual), so it is intentionally omitted. -/
theorem divuw_mode_pins_of_row
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 188) :
    row.flags.na = 0 ∧ row.flags.nb = 0 ∧ row.flags.np = 0 ∧ row.flags.nr = 0
      ∧ row.flags.m32 = 1 ∧ row.flags.div = 1
      ∧ row.flags.main_div = 1 ∧ row.flags.main_mul = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hm32, hdiv, hmain_div, hmain_mul⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

/-- Bare-`ArithMulRow` REMUW (W-mode secondary) mode pins (mirrors
    `remu_mode_pins_of_row` but for `OP_REMU_W = 189`, `m32 = 1`).  Reads the
    unsigned-REMUW mode flags off the balance-selected provider `ArithMulRow`
    (the REMUW provider is the SHARED ArithMul component) WITHOUT routing through
    a `rowAt` view.  At op `189` all four shared 74-row ArithTable rows pin
    `na = nb = np = nr = 0`, `m32 = 1`, `div = 1`, `main_div = 0`,
    `main_mul = 0` (REMUW consumes the **secondary** lane — the remainder in
    `d[]` — so `main_div = 0`, unlike DIVUW's `main_div = 1`; and `m32 = 1` for
    the W width, unlike REMU's `m32 = 0`).  Note `sext` is NOT uniform across the
    op-189 rows (the W-mode sign-extension lives in the `h_sext_choice` bus
    residual), so it is intentionally omitted. -/
theorem remuw_mode_pins_of_row
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec row)
    (h_op : row.flags.op = 189) :
    row.flags.na = 0 ∧ row.flags.nb = 0 ∧ row.flags.np = 0 ∧ row.flags.nr = 0
      ∧ row.flags.m32 = 1 ∧ row.flags.div = 1
      ∧ row.flags.main_div = 0 ∧ row.flags.main_mul = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hm32, hdiv, hmain_div, hmain_mul⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mul_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 180) :
    v.main_mul r = 1 ∧ v.main_div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mul_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 180) :
    v.nr r = 0 ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0
      ∧ (v.na r = 0 ∨ v.na r = 1)
      ∧ (v.nb r = 0 ∨ v.nb r = 1)
      ∧ (v.np r = 0 ∨ v.np r = 1) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | refine ⟨hnr, hsext, hm32, hdiv, ?_, ?_, ?_⟩
      · first | exact Or.inl hna | exact Or.inr hna
      · first | exact Or.inl hnb | exact Or.inr hnb
      · first | exact Or.inl hnp | exact Or.inr hnp
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mul_range_pins
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 180) :
    (v.na r = 0 → v.nb r = 0 → v.range_ab r = 4)
      ∧ (v.na r = 1 → v.nb r = 0 → v.range_ab r = 7)
      ∧ (v.na r = 0 → v.nb r = 1 → v.range_ab r = 5)
      ∧ (v.na r = 1 → v.nb r = 1 → v.range_ab r = 8)
      ∧ (v.np r = 0 → v.range_cd r = 1)
      ∧ (v.np r = 1 → v.range_cd r = 2) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, hna, hnb, hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, hrange_ab,
      hrange_cd⟩
    first
    | constructor
      · intro hna0 hnb0
        rw [hna0] at hna
        rw [hnb0] at hnb
        first | exact hrange_ab | contradiction
      constructor
      · intro hna1 hnb0
        rw [hna1] at hna
        rw [hnb0] at hnb
        first | exact hrange_ab | contradiction
      constructor
      · intro hna0 hnb1
        rw [hna0] at hna
        rw [hnb1] at hnb
        first | exact hrange_ab | contradiction
      constructor
      · intro hna1 hnb1
        rw [hna1] at hna
        rw [hnb1] at hnb
        first | exact hrange_ab | contradiction
      constructor
      · intro hnp0
        rw [hnp0] at hnp
        first | exact hrange_cd | contradiction
      · intro hnp1
        rw [hnp1] at hnp
        first | exact hrange_cd | contradiction
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mul_np_xor_or_zero_product_shape
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 180) :
    v.np r = v.na r + v.nb r - 2 * v.na r * v.nb r
      ∨ (v.na r = 1 ∧ v.nb r = 0 ∧ v.np r = 0)
      ∨ (v.na r = 0 ∧ v.nb r = 1 ∧ v.np r = 0) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, hna, hnb, hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    rw [hop] at h_op
    have hval := congrArg Fin.val h_op
    norm_num at hval
  all_goals
    first
    | right; left
      exact ⟨hna, hnb, hnp⟩
    | right; right
      exact ⟨hna, hnb, hnp⟩
    | left
      rw [hna, hnb, hnp]
      norm_num

theorem mulhu_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 177) :
    v.na r = 0 ∧ v.nb r = 0 ∧ v.np r = 0 ∧ v.nr r = 0
      ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hsext, hm32, hdiv⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mulhu_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 177) :
    v.main_mul r = 0 ∧ v.main_div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mulh_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 181) :
    v.main_mul r = 0 ∧ v.main_div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mulh_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 181) :
    v.nr r = 0 ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0
      ∧ (v.na r = 0 ∨ v.na r = 1)
      ∧ (v.nb r = 0 ∨ v.nb r = 1)
      ∧ (v.np r = 0 ∨ v.np r = 1) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | refine ⟨hnr, hsext, hm32, hdiv, ?_, ?_, ?_⟩
      · first | exact Or.inl hna | exact Or.inr hna
      · first | exact Or.inl hnb | exact Or.inr hnb
      · first | exact Or.inl hnp | exact Or.inr hnp
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mulhsu_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 179) :
    v.main_mul r = 0 ∧ v.main_div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mulhsu_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 179) :
    v.nb r = 0
      ∧ v.nr r = 0 ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0
      ∧ (v.na r = 0 ∨ v.na r = 1)
      ∧ (v.np r = 0 ∨ v.np r = 1) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | refine ⟨hnb, hnr, hsext, hm32, hdiv, ?_, ?_⟩
      · first | exact Or.inl hna | exact Or.inr hna
      · first | exact Or.inl hnp | exact Or.inr hnp
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

/-- **MULH product-sign shape (op 181).** Mirror of
    `mul_np_xor_or_zero_product_shape`: every lookup-aware MULH row has the
    honest signed product sign `np = na XOR nb`, OR one of the two exceptional
    product-sign shapes the shared 74-row ArithTable also admits for op 181
    (see `Counterexamples.mulh_np_xor_not_static`, row 12: `na=1, nb=0, np=0`).
    Those exceptional shapes are exactly the malicious signed-MUL witness forge;
    they are excluded by the `h_not_forge` hypothesis the canonical theorem
    consumes, leaving the honest XOR branch for the high-half proof. -/
theorem mulh_np_xor_or_zero_product_shape
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 181) :
    v.np r = v.na r + v.nb r - 2 * v.na r * v.nb r
      ∨ (v.na r = 1 ∧ v.nb r = 0 ∧ v.np r = 0)
      ∨ (v.na r = 0 ∧ v.nb r = 1 ∧ v.np r = 0) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, hna, hnb, hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    rw [hop] at h_op
    have hval := congrArg Fin.val h_op
    norm_num at hval
  all_goals
    first
    | right; left
      exact ⟨hna, hnb, hnp⟩
    | right; right
      exact ⟨hna, hnb, hnp⟩
    | left
      rw [hna, hnb, hnp]
      norm_num

/-- **MULHSU product-sign shape (op 179).** Companion of
    `mulh_np_xor_or_zero_product_shape` for the signed × unsigned high half.
    The table pins `nb = 0` (the unsigned operand), so the honest branch reads
    `np = na` (`= na XOR 0`); the exceptional shapes are the same forge shapes
    the table admits (`Counterexamples.mulhsu_np_xor_not_static`, row 3). -/
theorem mulhsu_np_xor_or_zero_product_shape
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 179) :
    v.np r = v.na r + v.nb r - 2 * v.na r * v.nb r
      ∨ (v.na r = 1 ∧ v.nb r = 0 ∧ v.np r = 0)
      ∨ (v.na r = 0 ∧ v.nb r = 1 ∧ v.np r = 0) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, hna, hnb, hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    rw [hop] at h_op
    have hval := congrArg Fin.val h_op
    norm_num at hval
  all_goals
    first
    | right; left
      exact ⟨hna, hnb, hnp⟩
    | right; right
      exact ⟨hna, hnb, hnp⟩
    | left
      rw [hna, hnb, hnp]
      norm_num

theorem mulw_basic_mode_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 182) :
    v.na r = 0 ∧ v.nb r = 0 ∧ v.np r = 0 ∧ v.nr r = 0
      ∧ v.m32 r = 1 ∧ v.div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hm32, hdiv⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mulw_main_selector_pin
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_op : v.op r = 182) :
    v.main_mul r = 1 ∧ v.main_div r = 0 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithMul.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow h_op ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hmain_mul, hmain_div⟩
    | rw [h_op] at hop
      have hval := congrArg Fin.val hop
      norm_num at hval

theorem mul_main_selector_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 180) :
    v.main_mul r = 1 ∧ v.main_div r = 0 := by
  exact mul_main_selector_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mul_basic_mode_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 180) :
    v.nr r = 0 ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0
      ∧ (v.na r = 0 ∨ v.na r = 1)
      ∧ (v.nb r = 0 ∨ v.nb r = 1)
      ∧ (v.np r = 0 ∨ v.np r = 1) := by
  exact mul_basic_mode_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mul_range_pins_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 180) :
    (v.na r = 0 → v.nb r = 0 → v.range_ab r = 4)
      ∧ (v.na r = 1 → v.nb r = 0 → v.range_ab r = 7)
      ∧ (v.na r = 0 → v.nb r = 1 → v.range_ab r = 5)
      ∧ (v.na r = 1 → v.nb r = 1 → v.range_ab r = 8)
      ∧ (v.np r = 0 → v.range_cd r = 1)
      ∧ (v.np r = 1 → v.range_cd r = 2) := by
  exact mul_range_pins v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mul_np_xor_or_zero_product_shape_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 180) :
    v.np r = v.na r + v.nb r - 2 * v.na r * v.nb r
      ∨ (v.na r = 1 ∧ v.nb r = 0 ∧ v.np r = 0)
      ∨ (v.na r = 0 ∧ v.nb r = 1 ∧ v.np r = 0) := by
  exact mul_np_xor_or_zero_product_shape v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulhu_mode_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 177) :
    v.na r = 0 ∧ v.nb r = 0 ∧ v.np r = 0 ∧ v.nr r = 0
      ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0 := by
  exact mulhu_mode_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulhu_main_selector_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 177) :
    v.main_mul r = 0 ∧ v.main_div r = 0 := by
  exact mulhu_main_selector_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulh_main_selector_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 181) :
    v.main_mul r = 0 ∧ v.main_div r = 0 := by
  exact mulh_main_selector_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulh_basic_mode_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 181) :
    v.nr r = 0 ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0
      ∧ (v.na r = 0 ∨ v.na r = 1)
      ∧ (v.nb r = 0 ∨ v.nb r = 1)
      ∧ (v.np r = 0 ∨ v.np r = 1) := by
  exact mulh_basic_mode_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulhsu_main_selector_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 179) :
    v.main_mul r = 0 ∧ v.main_div r = 0 := by
  exact mulhsu_main_selector_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulhsu_basic_mode_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 179) :
    v.nb r = 0
      ∧ v.nr r = 0 ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 0
      ∧ (v.na r = 0 ∨ v.na r = 1)
      ∧ (v.np r = 0 ∨ v.np r = 1) := by
  exact mulhsu_basic_mode_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulw_basic_mode_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 182) :
    v.na r = 0 ∧ v.nb r = 0 ∧ v.np r = 0 ∧ v.nr r = 0
      ∧ v.m32 r = 1 ∧ v.div r = 0 := by
  exact mulw_basic_mode_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem mulw_main_selector_pin_of_lookup_aware_soundness
    (offset : ℕ) (env : Environment FGL)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_holds :
      ConstraintsHold.Soundness env
        ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
          (ZiskFv.AirsClean.ArithMul.constVar
            (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset))
    (h_op : v.op r = 182) :
    v.main_mul r = 1 ∧ v.main_div r = 0 := by
  exact mulw_main_selector_pin v r
    (ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
      offset env (ZiskFv.AirsClean.ArithMul.rowAt v r) h_holds)
    h_op

theorem na_eq_msb64_of_pos_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chunks : ZiskFv.AirsClean.ArithMul.ChunkRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_na : v.na r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r)) :
    (v.na r).val =
      if 2 ^ 63 ≤ packed4 (v.a_0 r).val (v.a_1 r).val (v.a_2 r).val (v.a_3 r).val
      then 1 else 0 := by
  rcases h_chunks with ⟨ha0, ha1, ha2, _ha3, _hb0, _hb1, _hb2, _hb3,
    _hc0, _hc1, _hc2, _hc3, _hd0, _hd1, _hd2, _hd3⟩
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_pos_range_lookup h_na
    (by simpa using ha0) (by simpa using ha1) (by simpa using ha2) h_id ha3_lookup

theorem na_eq_msb64_of_neg_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_na : v.na r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r)) :
    (v.na r).val =
      if 2 ^ 63 ≤ packed4 (v.a_0 r).val (v.a_1 r).val (v.a_2 r).val (v.a_3 r).val
      then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_neg_range_lookup h_na h_id ha3_lookup

theorem nb_eq_msb64_of_pos_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chunks : ZiskFv.AirsClean.ArithMul.ChunkRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_nb : v.nb r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r + 17)) :
    (v.nb r).val =
      if 2 ^ 63 ≤ packed4 (v.b_0 r).val (v.b_1 r).val (v.b_2 r).val (v.b_3 r).val
      then 1 else 0 := by
  rcases h_chunks with ⟨_ha0, _ha1, _ha2, _ha3, hb0, hb1, hb2, _hb3,
    _hc0, _hc1, _hc2, _hc3, _hd0, _hd1, _hd2, _hd3⟩
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_pos_range_lookup h_nb
    (by simpa using hb0) (by simpa using hb1) (by simpa using hb2) h_id hb3_lookup

theorem nb_eq_msb64_of_neg_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_nb : v.nb r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r + 17)) :
    (v.nb r).val =
      if 2 ^ 63 ≤ packed4 (v.b_0 r).val (v.b_1 r).val (v.b_2 r).val (v.b_3 r).val
      then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_neg_range_lookup h_nb h_id hb3_lookup

theorem na_eq_msb32_of_pos_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chunks : ZiskFv.AirsClean.ArithMul.ChunkRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_na : v.na r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r + 26)) :
    (v.na r).val = if 2 ^ 31 ≤ packed2 (v.a_0 r).val (v.a_1 r).val then 1 else 0 := by
  rcases h_chunks with ⟨ha0, _ha1, _ha2, _ha3, _hb0, _hb1, _hb2, _hb3,
    _hc0, _hc1, _hc2, _hc3, _hd0, _hd1, _hd2, _hd3⟩
  rcases h_indexed with ⟨ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_pos_range_lookup h_na (by simpa using ha0) h_id ha1_lookup

theorem na_eq_msb32_of_neg_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_na : v.na r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r + 26)) :
    (v.na r).val = if 2 ^ 31 ≤ packed2 (v.a_0 r).val (v.a_1 r).val then 1 else 0 := by
  rcases h_indexed with ⟨ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_neg_range_lookup h_na h_id ha1_lookup

theorem nb_eq_msb32_of_pos_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_chunks : ZiskFv.AirsClean.ArithMul.ChunkRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_nb : v.nb r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r + 9)) :
    (v.nb r).val = if 2 ^ 31 ≤ packed2 (v.b_0 r).val (v.b_1 r).val then 1 else 0 := by
  rcases h_chunks with ⟨_ha0, _ha1, _ha2, _ha3, hb0, _hb1, _hb2, _hb3,
    _hc0, _hc1, _hc2, _hc3, _hd0, _hd1, _hd2, _hd3⟩
  rcases h_indexed with ⟨_ha1_lookup, hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_pos_range_lookup h_nb (by simpa using hb0) h_id hb1_lookup

theorem nb_eq_msb32_of_neg_indexed
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r))
    (h_nb : v.nb r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r + 9)) :
    (v.nb r).val = if 2 ^ 31 ≤ packed2 (v.b_0 r).val (v.b_1 r).val then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_neg_range_lookup h_nb h_id hb1_lookup

end Mul

namespace Div

theorem div_rem_signed_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_op : v.op r = 186 ∨ v.op r = 187) :
    v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 1 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, _hna, _hnb, _hnp, _hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hsext, hm32, hdiv⟩
    | rcases h_op with h_op | h_op <;>
        rw [h_op] at hop <;>
        have hval := congrArg Fin.val hop <;>
        norm_num at hval

theorem div_rem_unsigned_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_op : v.op r = 184 ∨ v.op r = 185) :
    v.na r = 0 ∧ v.nb r = 0 ∧ v.np r = 0 ∧ v.nr r = 0
      ∧ v.sext r = 0 ∧ v.m32 r = 0 ∧ v.div r = 1 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hsext, hm32, hdiv⟩
    | rcases h_op with h_op | h_op <;>
        rw [h_op] at hop <;>
        have hval := congrArg Fin.val hop <;>
        norm_num at hval

theorem div_rem_main_selector_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (_h_op : v.op r = 186 ∨ v.op r = 187) :
    (v.op r = 186 → v.main_div r = 1 ∧ v.main_mul r = 0)
  ∧ (v.op r = 187 → v.main_div r = 0 ∧ v.main_mul r = 0) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    constructor
    · intro h186
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h186] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval
    · intro h187
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h187] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval

theorem div_rem_unsigned_main_selector_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (_h_op : v.op r = 184 ∨ v.op r = 185) :
    (v.op r = 184 → v.main_div r = 1 ∧ v.main_mul r = 0)
  ∧ (v.op r = 185 → v.main_div r = 0 ∧ v.main_mul r = 0) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    constructor
    · intro h184
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h184] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval
    · intro h185
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h185] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval

theorem div_rem_unsigned_w_basic_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_op : v.op r = 188 ∨ v.op r = 189) :
    v.na r = 0 ∧ v.nb r = 0 ∧ v.np r = 0 ∧ v.nr r = 0
      ∧ v.m32 r = 1 ∧ v.div r = 1 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, hna, hnb, hnp, hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hna, hnb, hnp, hnr, hm32, hdiv⟩
    | rcases h_op with h_op | h_op <;>
        rw [h_op] at hop <;>
        have hval := congrArg Fin.val hop <;>
        norm_num at hval

theorem div_rem_signed_w_basic_mode_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_op : v.op r = 190 ∨ v.op r = 191) :
    v.m32 r = 1 ∧ v.div r = 1 := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, hm32, hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, _hmain_mul, _hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    first
    | exact ⟨hm32, hdiv⟩
    | rcases h_op with h_op | h_op <;>
        rw [h_op] at hop <;>
        have hval := congrArg Fin.val hop <;>
        norm_num at hval

theorem div_rem_w_main_selector_pin
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_table : ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (_h_op : v.op r = 188 ∨ v.op r = 189 ∨ v.op r = 190 ∨ v.op r = 191) :
    (v.op r = 188 → v.main_div r = 1 ∧ v.main_mul r = 0)
  ∧ (v.op r = 189 → v.main_div r = 0 ∧ v.main_mul r = 0)
  ∧ (v.op r = 190 → v.main_div r = 1 ∧ v.main_mul r = 0)
  ∧ (v.op r = 191 → v.main_div r = 0 ∧ v.main_mul r = 0) := by
  rcases h_table with ⟨i, hrow⟩
  fin_cases i <;>
    simp [ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithTable.rows] at hrow ⊢
  all_goals
    rcases hrow with ⟨hop, _hm32, _hdiv, _hna, _hnb, _hnp, _hnr, _hsext,
      _hdiv_by_zero, _hdiv_overflow, hmain_mul, hmain_div, _hsigned, _hrange_ab,
      _hrange_cd⟩
    constructor
    · intro h188
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h188] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval
    constructor
    · intro h189
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h189] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval
    constructor
    · intro h190
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h190] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval
    · intro h191
      first
      | exact ⟨hmain_div, hmain_mul⟩
      | rw [h191] at hop
        have hval := congrArg Fin.val hop
        norm_num at hval

theorem na_eq_msb64_of_pos_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_a0 : (v.a_0 r).val < 65536) (h_a1 : (v.a_1 r).val < 65536)
    (h_a2 : (v.a_2 r).val < 65536)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_na : v.na r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r)) :
    (v.na r).val =
      if 2 ^ 63 ≤ packed4 (v.a_0 r).val (v.a_1 r).val (v.a_2 r).val (v.a_3 r).val
      then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_pos_range_lookup h_na h_a0 h_a1 h_a2 h_id ha3_lookup

theorem na_eq_msb64_of_neg_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_na : v.na r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r)) :
    (v.na r).val =
      if 2 ^ 63 ≤ packed4 (v.a_0 r).val (v.a_1 r).val (v.a_2 r).val (v.a_3 r).val
      then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_neg_range_lookup h_na h_id ha3_lookup

theorem nb_eq_msb64_of_pos_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_b0 : (v.b_0 r).val < 65536) (h_b1 : (v.b_1 r).val < 65536)
    (h_b2 : (v.b_2 r).val < 65536)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_nb : v.nb r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r + 17)) :
    (v.nb r).val =
      if 2 ^ 63 ≤ packed4 (v.b_0 r).val (v.b_1 r).val (v.b_2 r).val (v.b_3 r).val
      then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_pos_range_lookup h_nb h_b0 h_b1 h_b2 h_id hb3_lookup

theorem nb_eq_msb64_of_neg_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_nb : v.nb r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r + 17)) :
    (v.nb r).val =
      if 2 ^ 63 ≤ packed4 (v.b_0 r).val (v.b_1 r).val (v.b_2 r).val (v.b_3 r).val
      then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb64_of_neg_range_lookup h_nb h_id hb3_lookup

theorem na_eq_msb32_of_pos_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_a0 : (v.a_0 r).val < 65536)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_na : v.na r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r + 26)) :
    (v.na r).val = if 2 ^ 31 ≤ packed2 (v.a_0 r).val (v.a_1 r).val then 1 else 0 := by
  rcases h_indexed with ⟨ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_pos_range_lookup h_na h_a0 h_id ha1_lookup

theorem na_eq_msb32_of_neg_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_na : v.na r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r + 26)) :
    (v.na r).val = if 2 ^ 31 ≤ packed2 (v.a_0 r).val (v.a_1 r).val then 1 else 0 := by
  rcases h_indexed with ⟨ha1_lookup, _hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_neg_range_lookup h_na h_id ha1_lookup

theorem nb_eq_msb32_of_pos_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_b0 : (v.b_0 r).val < 65536)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_nb : v.nb r = 0)
    (h_id : RangeTables.ArithRangePosId (v.range_ab r + 9)) :
    (v.nb r).val = if 2 ^ 31 ≤ packed2 (v.b_0 r).val (v.b_1 r).val then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_pos_range_lookup h_nb h_b0 h_id hb1_lookup

theorem nb_eq_msb32_of_neg_indexed
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ)
    (h_indexed : ZiskFv.AirsClean.ArithDiv.IndexedRangeSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r))
    (h_nb : v.nb r = 1)
    (h_id : RangeTables.ArithRangeNegId (v.range_ab r + 9)) :
    (v.nb r).val = if 2 ^ 31 ≤ packed2 (v.b_0 r).val (v.b_1 r).val then 1 else 0 := by
  rcases h_indexed with ⟨_ha1_lookup, hb1_lookup, _hc1_lookup, _hd1_lookup,
    _ha3_lookup, _hb3_lookup, _hc3_lookup, _hd3_lookup⟩
  exact sign_eq_msb32_of_neg_range_lookup h_nb h_id hb1_lookup

end Div

end ZiskFv.AirsClean.ArithTableProjections
