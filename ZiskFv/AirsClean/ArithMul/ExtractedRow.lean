import ZiskFv.AirsClean.ArithMirrorWeld

/-!
# Materializing the Clean Arith row from extracted columns

This module reads the 44 modeled stage-1 columns directly from an
`Extraction.Circuit` row. Generated constraints 0–48 then imply exactly the
polynomial part of the live Arith model: `Spec`, `C46Spec`, and
`SharedDivBlockSpec`. Static-table and range-lookup membership are deliberately
absent: the F-only generated assertions do not establish those facts.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

universe u

variable {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]

/-- Read the modeled Arith stage-1 columns 0–43 in the layout pinned by
`ArithMirrorWeld.mainValue`. -/
@[reducible]
def materializedRow (source : C FGL FGL) (sourceRow : Nat) : ArithMulRow FGL :=
  { chunks :=
      { a_0 := Extraction.Circuit.main source 1 7 sourceRow 0
        a_1 := Extraction.Circuit.main source 1 8 sourceRow 0
        a_2 := Extraction.Circuit.main source 1 9 sourceRow 0
        a_3 := Extraction.Circuit.main source 1 10 sourceRow 0
        b_0 := Extraction.Circuit.main source 1 11 sourceRow 0
        b_1 := Extraction.Circuit.main source 1 12 sourceRow 0
        b_2 := Extraction.Circuit.main source 1 13 sourceRow 0
        b_3 := Extraction.Circuit.main source 1 14 sourceRow 0
        c_0 := Extraction.Circuit.main source 1 15 sourceRow 0
        c_1 := Extraction.Circuit.main source 1 16 sourceRow 0
        c_2 := Extraction.Circuit.main source 1 17 sourceRow 0
        c_3 := Extraction.Circuit.main source 1 18 sourceRow 0
        d_0 := Extraction.Circuit.main source 1 19 sourceRow 0
        d_1 := Extraction.Circuit.main source 1 20 sourceRow 0
        d_2 := Extraction.Circuit.main source 1 21 sourceRow 0
        d_3 := Extraction.Circuit.main source 1 22 sourceRow 0 }
    flags :=
      { na := Extraction.Circuit.main source 1 23 sourceRow 0
        nb := Extraction.Circuit.main source 1 24 sourceRow 0
        nr := Extraction.Circuit.main source 1 25 sourceRow 0
        np := Extraction.Circuit.main source 1 26 sourceRow 0
        sext := Extraction.Circuit.main source 1 27 sourceRow 0
        m32 := Extraction.Circuit.main source 1 28 sourceRow 0
        div := Extraction.Circuit.main source 1 29 sourceRow 0
        div_by_zero := Extraction.Circuit.main source 1 36 sourceRow 0
        div_overflow := Extraction.Circuit.main source 1 37 sourceRow 0
        main_div := Extraction.Circuit.main source 1 33 sourceRow 0
        main_mul := Extraction.Circuit.main source 1 34 sourceRow 0
        signed := Extraction.Circuit.main source 1 35 sourceRow 0
        range_ab := Extraction.Circuit.main source 1 42 sourceRow 0
        range_cd := Extraction.Circuit.main source 1 43 sourceRow 0
        op := Extraction.Circuit.main source 1 39 sourceRow 0
        bus_res1 := Extraction.Circuit.main source 1 40 sourceRow 0
        multiplicity := Extraction.Circuit.main source 1 41 sourceRow 0 }
    carries :=
      { carry_0 := Extraction.Circuit.main source 1 0 sourceRow 0
        carry_1 := Extraction.Circuit.main source 1 1 sourceRow 0
        carry_2 := Extraction.Circuit.main source 1 2 sourceRow 0
        carry_3 := Extraction.Circuit.main source 1 3 sourceRow 0
        carry_4 := Extraction.Circuit.main source 1 4 sourceRow 0
        carry_5 := Extraction.Circuit.main source 1 5 sourceRow 0
        carry_6 := Extraction.Circuit.main source 1 6 sourceRow 0
        fab := Extraction.Circuit.main source 1 30 sourceRow 0
        na_fb := Extraction.Circuit.main source 1 31 sourceRow 0
        nb_fa := Extraction.Circuit.main source 1 32 sourceRow 0
        inv_sum_all_bs := Extraction.Circuit.main source 1 38 sourceRow 0 } }

/-- Every modeled stage-1 source column is preserved by materialization. -/
theorem materializedRow_sourceColumn (source : C FGL FGL) (sourceRow : Nat)
    (column : Fin 44) :
    mainValue (extractedArithRow (materializedRow source sourceRow))
        1 column 0 0 =
      Extraction.Circuit.main source 1 column sourceRow 0 := by
  fin_cases column <;> rfl

/-- Source selectors for the low-result MUL/MULW branch. These are readings of
the generated row itself, rather than an added model-validity premise. -/
@[reducible]
def GeneratedPrimaryMulMode (source : C FGL FGL) (row : Nat) : Prop :=
  Extraction.Circuit.main source 1 29 row 0 = 0
    ∧ Extraction.Circuit.main source 1 34 row 0 = 1
    ∧ Extraction.Circuit.main source 1 33 row 0 = 0

/-- Source selectors for the high-result MULH/MULHU/MULHSU branch. -/
@[reducible]
def GeneratedSecondaryMulMode (source : C FGL FGL) (row : Nat) : Prop :=
  Extraction.Circuit.main source 1 29 row 0 = 0
    ∧ Extraction.Circuit.main source 1 34 row 0 = 0
    ∧ Extraction.Circuit.main source 1 33 row 0 = 0

theorem materializedRow_primaryMulMode (source : C FGL FGL) (sourceRow : Nat)
    (h : GeneratedPrimaryMulMode source sourceRow) :
    (materializedRow source sourceRow).flags.div = 0
      ∧ (materializedRow source sourceRow).flags.main_mul = 1
      ∧ (materializedRow source sourceRow).flags.main_div = 0 :=
  h

theorem materializedRow_secondaryMulMode (source : C FGL FGL) (sourceRow : Nat)
    (h : GeneratedSecondaryMulMode source sourceRow) :
    (materializedRow source sourceRow).flags.div = 0
      ∧ (materializedRow source sourceRow).flags.main_mul = 0
      ∧ (materializedRow source sourceRow).flags.main_div = 0 :=
  h

@[reducible]
def GeneratedDivModeAssertions (source : C FGL FGL) (row : Nat) : Prop :=
  Arith.extraction.constraint_0_every_row source row
    ∧ Arith.extraction.constraint_1_every_row source row
    ∧ Arith.extraction.constraint_2_every_row source row
    ∧ Arith.extraction.constraint_3_every_row source row
    ∧ Arith.extraction.constraint_4_every_row source row
    ∧ Arith.extraction.constraint_5_every_row source row
    ∧ Arith.extraction.constraint_39_every_row source row
    ∧ Arith.extraction.constraint_40_every_row source row
    ∧ Arith.extraction.constraint_41_every_row source row
    ∧ Arith.extraction.constraint_42_every_row source row
    ∧ Arith.extraction.constraint_43_every_row source row
    ∧ Arith.extraction.constraint_44_every_row source row
    ∧ Arith.extraction.constraint_45_every_row source row

@[reducible]
def GeneratedDivBoundaryAssertions (source : C FGL FGL) (row : Nat) : Prop :=
  Arith.extraction.constraint_9_every_row source row
    ∧ Arith.extraction.constraint_10_every_row source row
    ∧ Arith.extraction.constraint_11_every_row source row
    ∧ Arith.extraction.constraint_12_every_row source row
    ∧ Arith.extraction.constraint_13_every_row source row
    ∧ Arith.extraction.constraint_14_every_row source row
    ∧ Arith.extraction.constraint_15_every_row source row
    ∧ Arith.extraction.constraint_16_every_row source row
    ∧ Arith.extraction.constraint_17_every_row source row
    ∧ Arith.extraction.constraint_18_every_row source row
    ∧ Arith.extraction.constraint_19_every_row source row
    ∧ Arith.extraction.constraint_20_every_row source row
    ∧ Arith.extraction.constraint_21_every_row source row
    ∧ Arith.extraction.constraint_22_every_row source row
    ∧ Arith.extraction.constraint_23_every_row source row
    ∧ Arith.extraction.constraint_24_every_row source row

@[reducible]
def GeneratedDivScopeAssertions (source : C FGL FGL) (row : Nat) : Prop :=
  Arith.extraction.constraint_26_every_row source row
    ∧ Arith.extraction.constraint_27_every_row source row
    ∧ Arith.extraction.constraint_28_every_row source row
    ∧ Arith.extraction.constraint_29_every_row source row
    ∧ Arith.extraction.constraint_30_every_row source row

@[reducible]
def GeneratedCarryAssertions (source : C FGL FGL) (row : Nat) : Prop :=
  Arith.extraction.constraint_6_every_row source row
    ∧ Arith.extraction.constraint_7_every_row source row
    ∧ Arith.extraction.constraint_8_every_row source row
    ∧ Arith.extraction.constraint_31_every_row source row
    ∧ Arith.extraction.constraint_32_every_row source row
    ∧ Arith.extraction.constraint_33_every_row source row
    ∧ Arith.extraction.constraint_34_every_row source row
    ∧ Arith.extraction.constraint_35_every_row source row
    ∧ Arith.extraction.constraint_36_every_row source row
    ∧ Arith.extraction.constraint_37_every_row source row
    ∧ Arith.extraction.constraint_38_every_row source row

/-- All 49 F-only assertions emitted for Arith. This deliberately contains no
lookup-membership premise. -/
@[reducible]
def GeneratedPolynomialAssertions (source : C FGL FGL) (row : Nat) : Prop :=
  GeneratedDivModeAssertions source row
    ∧ GeneratedDivBoundaryAssertions source row
    ∧ Arith.extraction.constraint_25_every_row source row
    ∧ GeneratedDivScopeAssertions source row
    ∧ GeneratedCarryAssertions source row
    ∧ Arith.extraction.constraint_46_every_row source row
    ∧ Arith.extraction.constraint_47_every_row source row
    ∧ Arith.extraction.constraint_48_every_row source row

/-- The portion of the live component specification established by generated
F-only assertions. Range and static-table lookup membership remain separate. -/
@[reducible]
def PolynomialSpec (row : ArithMulRow FGL) : Prop :=
  Spec row ∧ C46Spec row ∧ SharedDivBlockSpec row

/-- A raw extracted Arith row satisfying generated constraints 0–48 directly
materializes the complete live polynomial model. -/
theorem polynomialSpec_materializedRow (source : C FGL FGL) (sourceRow : Nat)
    (h : GeneratedPolynomialAssertions source sourceRow) :
    PolynomialSpec (materializedRow source sourceRow) := by
  let row := materializedRow source sourceRow
  rcases h with ⟨hMode, hBoundary, hInverse, hScope, hCarry, hC46, hW47, hW48⟩
  have hMode' : GeneratedDivModeAssertions (extractedArithRow row) 0 := by
    change GeneratedDivModeAssertions source sourceRow
    exact hMode
  have hBoundary' : GeneratedDivBoundaryAssertions (extractedArithRow row) 0 := by
    change GeneratedDivBoundaryAssertions source sourceRow
    exact hBoundary
  have hInverse' : Arith.extraction.constraint_25_every_row
      (extractedArithRow row) 0 := by
    change Arith.extraction.constraint_25_every_row source sourceRow
    exact hInverse
  have hScope' : GeneratedDivScopeAssertions (extractedArithRow row) 0 := by
    change GeneratedDivScopeAssertions source sourceRow
    exact hScope
  have hCarry' : GeneratedCarryAssertions (extractedArithRow row) 0 := by
    change GeneratedCarryAssertions source sourceRow
    exact hCarry
  have hC46' : Arith.extraction.constraint_46_every_row
      (extractedArithRow row) 0 := by
    change Arith.extraction.constraint_46_every_row source sourceRow
    exact hC46
  have hW' : Arith.extraction.constraint_47_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_48_every_row (extractedArithRow row) 0 := by
    constructor
    · change Arith.extraction.constraint_47_every_row source sourceRow
      exact hW47
    · change Arith.extraction.constraint_48_every_row source sourceRow
      exact hW48
  refine ⟨spec_of_generatedCarryChain row hCarry', (c46Spec_weld row).mpr hC46', ?_⟩
  exact ⟨(divModeSpec_weld row).mpr hMode',
    (divBoundarySpec_weld row).mpr hBoundary',
    (divInverseSumSpec_weld row).mpr hInverse',
    (divScopeSpec_weld row).mpr hScope',
    (divWModeSpec_weld row).mpr hW'⟩

/-- In either source-selected MUL branch, the generated scope polynomial forces
the materialized physical operation flag to zero. -/
theorem materializedRow_divByZero_eq_zero_of_mulMode
    (source : C FGL FGL) (sourceRow : Nat)
    (hAssertions : GeneratedPolynomialAssertions source sourceRow)
    (hMode : GeneratedPrimaryMulMode source sourceRow
      ∨ GeneratedSecondaryMulMode source sourceRow) :
    (materializedRow source sourceRow).flags.div_by_zero = 0 := by
  have hPoly := polynomialSpec_materializedRow source sourceRow hAssertions
  have hDiv : (materializedRow source sourceRow).flags.div = 0 := by
    rcases hMode with h | h
    · exact (materializedRow_primaryMulMode source sourceRow h).1
    · exact (materializedRow_secondaryMulMode source sourceRow h).1
  have hScope : DivScopeSpec (materializedRow source sourceRow) :=
    hPoly.2.2.2.2.2.1
  unfold DivScopeSpec at hScope
  rw [hDiv] at hScope
  simpa using hScope.1

set_option maxRecDepth 10000 in
/-- Every actual polynomial assertion in the live completed Arith circuit
follows from generated constraints 0–48 on the raw source row. Lookups are
intentionally absent from this boundary. -/
theorem sharedMainComplete_assertions_of_generatedPolynomialAssertions
    (source : C FGL FGL) (sourceRow : Nat)
    (v : Var ArithMulRow FGL) (offset : Nat) (env : Environment FGL)
    (h : GeneratedPolynomialAssertions source sourceRow)
    (hv : eval env v = materializedRow source sourceRow) :
    ∀ e ∈ ((sharedMainComplete v).operations offset).shallowConstraints,
      env e = 0 := by
  have hs := polynomialSpec_materializedRow source sourceRow h
  rw [← hv] at hs
  simp only [PolynomialSpec, Spec, C46Spec, SharedDivBlockSpec, DivModeSpec,
    DivBoundarySpec, DivInverseSumSpec, DivScopeSpec, DivWModeSpec,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field] at hs
  rcases hs with ⟨hSpec, hC46, hMode, hBoundary, hInverse, hScope, hW⟩
  rcases hSpec with ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩
  rcases hMode with
    ⟨h0, h1, h2, h3, h4, h5, h39, h40, h41, h42, h43, h44, h45⟩
  rcases hBoundary with
    ⟨h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
      h23, h24⟩
  rcases hScope with ⟨h26, h27, h28, h29, h30⟩
  rcases hW with ⟨h47, h48⟩
  simp only [sharedMainComplete, mainWithArithTable, main, circuit_norm,
    Operations.shallowConstraints, forall_eq_or_imp]
  simp only [← sub_eq_add_neg]
  exact ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38,
    hC46, h0, h1, h2, h3, h4, h5,
    h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, hInverse, h26, h27, h28, h29, h30,
    h39, h40, h41, h42, h43, h44, h45, hC46, h47, h48⟩

end ZiskFv.AirsClean.ArithMul
