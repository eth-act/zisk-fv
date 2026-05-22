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
