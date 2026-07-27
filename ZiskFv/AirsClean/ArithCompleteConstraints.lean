import ZiskFv.AirsClean.ArithMul.Constraints

/-!
The complete local constraint set for the shared Arith provider.

Each group below is a handwritten circuit mirror of the named generated
`Extraction.Arith.constraint_N_every_row` definitions. The comments are source
citations, not machine-checked links; equivalence was audited against the current
generated extraction.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks Circuit

@[circuit_norm] def sharedMainComplete (row : Var ArithMulRow FGL) : Circuit FGL Unit := do
  mainWithArithTable row
  -- `constraint_0_every_row`--`constraint_5_every_row`;
  -- `arith/pil/arith.pil:50-55`.
  assertZero (row.flags.main_div * (row.flags.main_div - 1))
  assertZero (row.flags.main_mul * (row.flags.main_mul - 1))
  assertZero (row.flags.main_mul * row.flags.main_div)
  assertZero (row.flags.signed * (1 - row.flags.signed))
  assertZero (row.flags.div_by_zero * (1 - row.flags.div_by_zero))
  assertZero (row.flags.div_overflow * (1 - row.flags.div_overflow))
  -- `constraint_9_every_row`--`constraint_24_every_row`;
  -- `arith/pil/arith.pil:64,69-72,75-78,81-84`.
  assertZero (row.flags.div_by_zero * row.chunks.b_0)
  assertZero (row.flags.div_by_zero * row.chunks.b_1)
  assertZero (row.flags.div_by_zero * row.chunks.b_2)
  assertZero (row.flags.div_by_zero * row.chunks.b_3)
  assertZero (row.flags.div_by_zero * (row.chunks.a_0 - 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_1 - 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_2 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_3 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_0 - 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_1 - 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_2 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_3 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * row.chunks.c_0)
  assertZero (row.flags.div_overflow * (row.chunks.c_1 - row.flags.m32 * 32768))
  assertZero (row.flags.div_overflow * row.chunks.c_2)
  assertZero (row.flags.div_overflow * (row.chunks.c_3 - (1 - row.flags.m32) * 32768))
  -- `constraint_25_every_row`--`constraint_30_every_row`;
  -- `arith/pil/arith.pil:92,95,98-99,101-102`.
  assertZero ((row.flags.div - row.flags.div_by_zero) *
    (1 - row.carries.inv_sum_all_bs *
      (((row.chunks.b_0 + row.chunks.b_1) + row.chunks.b_2) + row.chunks.b_3)))
  assertZero (row.flags.div_by_zero * (1 - row.flags.div))
  assertZero (row.flags.div_overflow * (1 - row.flags.div))
  assertZero (row.flags.div_overflow * (1 - row.flags.signed))
  assertZero (row.flags.div_overflow * row.flags.div_by_zero)
  assertZero (row.flags.div_by_zero * row.flags.div_overflow)
  -- `constraint_39_every_row`--`constraint_45_every_row`;
  -- `arith/pil/arith.pil:212-218`.
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  -- `constraint_46_every_row`; `arith/pil/arith.pil:262`.
  assertZero (row.flags.bus_res1 -
    (row.flags.sext * 4294967295 + (1 - row.flags.m32) *
      (((1 - row.flags.main_mul - row.flags.main_div) *
          (row.chunks.d_2 + row.chunks.d_3 * 65536)) +
       row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
       row.flags.main_div * (row.chunks.a_2 + row.chunks.a_3 * 65536))))
  -- `constraint_47_every_row`--`constraint_48_every_row`;
  -- `arith/pil/arith.pil:264-265`.
  assertZero (row.flags.m32 *
    (row.flags.div * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
      (1 - row.flags.div) * (row.chunks.a_2 + row.chunks.a_3 * 65536)))
  assertZero (row.flags.m32 * (row.chunks.b_2 + row.chunks.b_3 * 65536))

/-- Forget the appended local assertions while retaining the lookup-aware base
provider constraints. -/
theorem sharedMainComplete_base_soundness
    (offset : ℕ) (env : Environment FGL) (row : Var ArithMulRow FGL)
    (h : ConstraintsHold.Soundness env ((sharedMainComplete row).operations offset)) :
    ConstraintsHold.Soundness env ((mainWithArithTable row).operations offset) := by
  simp only [sharedMainComplete, mainWithArithTable, main, circuit_norm] at h ⊢
  rcases h with
    ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38,
      h46, hlookup, hra1, hrb1, hrc1, hrd1, hra3, hrb3, hrc3, hrd3,
      ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
      hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3,
      hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6, _⟩
  exact ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38,
    h46, hlookup, hra1, hrb1, hrc1, hrd1, hra3, hrb3, hrc3, hrd3,
    ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
    hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3,
    hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6⟩

set_option maxHeartbeats 1600000 in
/-- Project exactly the appended generated Div block from the live completed
constraint list. -/
theorem sharedDivBlockSpec_of_constraints
    (offset : ℕ) (env : Environment FGL) (row : Var ArithMulRow FGL)
    (h : Operations.ConstraintsHold env
      ((sharedMainComplete row).operations offset)) :
    SharedDivBlockSpec (eval env row) := by
  simp only [sharedMainComplete, mainWithArithTable, main, circuit_norm] at h
  cases row with
  | mk chunks flags carries =>
    cases chunks with
    | mk a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 =>
    cases flags with
    | mk na nb nr np sext m32 div div0 overflow mainDiv mainMul signed
        rangeAB rangeCD op busRes multiplicity =>
    cases carries with
    | mk cy0 cy1 cy2 cy3 cy4 cy5 cy6 fab nafb nbfa inv =>
    simp only [SharedDivBlockSpec, DivModeSpec, DivBoundarySpec, DivInverseSumSpec,
      DivScopeSpec, DivWModeSpec, ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components, ProvableStruct.toComponents,
      ProvableStruct.eval.go, ProvableType.eval_field] at *
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (mainDiv * (mainDiv - 1)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (mainMul * (mainMul - 1)) (by simp)
    · simpa [Expression.eval] using h.1 (mainMul * mainDiv) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (signed * (1 - signed)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (div0 * (1 - div0)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (overflow * (1 - overflow)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (div * (1 - div)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (m32 * (1 - m32)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (na * (1 - na)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (nb * (1 - nb)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (nr * (1 - nr)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (np * (1 - np)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (sext * (1 - sext)) (by simp)
    · simpa [Expression.eval] using h.1 (div0 * b0) (by simp)
    · simpa [Expression.eval] using h.1 (div0 * b1) (by simp)
    · simpa [Expression.eval] using h.1 (div0 * b2) (by simp)
    · simpa [Expression.eval] using h.1 (div0 * b3) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (div0 * (a0 - 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (div0 * (a1 - 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (div0 * (a2 - (1 - m32) * 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (div0 * (a3 - (1 - m32) * 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (overflow * (b0 - 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (overflow * (b1 - 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (overflow * (b2 - (1 - m32) * 65535)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (overflow * (b3 - (1 - m32) * 65535)) (by simp)
    · simpa [Expression.eval] using h.1 (overflow * c0) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (overflow * (c1 - m32 * 32768)) (by simp)
    · simpa [Expression.eval] using h.1 (overflow * c2) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (overflow * (c3 - (1 - m32) * 32768)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 ((div - div0) * (1 - inv * (((b0 + b1) + b2) + b3))) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (div0 * (1 - div)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (overflow * (1 - div)) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using h.1 (overflow * (1 - signed)) (by simp)
    · simpa [Expression.eval] using h.1 (overflow * div0) (by simp)
    · simpa [Expression.eval] using h.1 (div0 * overflow) (by simp)
    · simpa [Expression.eval, sub_eq_add_neg] using
        h.1 (m32 * (div * (c2 + c3 * 65536) + (1 - div) * (a2 + a3 * 65536))) (by simp)
    · simpa [Expression.eval] using h.1 (m32 * (b2 + b3 * 65536)) (by simp)

end ZiskFv.AirsClean.ArithMul
