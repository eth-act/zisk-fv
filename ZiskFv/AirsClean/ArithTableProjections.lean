import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge

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

end Div

end ZiskFv.AirsClean.ArithTableProjections
