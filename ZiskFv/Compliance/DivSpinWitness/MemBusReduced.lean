import ZiskFv.Compliance.DivSpinWitness.MemBusHistories

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.AddSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.DivSpinWitness

def divSpinMemBusNonzeroChronological : List (Interaction FGL) :=
  [ registerBoundaryBootInteraction divSpinBoundaryRowX1
  , registerBoundaryReloadInteraction divSpinBoundaryRowX1
  , registerBoundaryBootInteraction divSpinBoundaryRowX2
  , registerBoundaryReloadInteraction divSpinBoundaryRowX2
  , registerBoundaryBootInteraction divSpinBoundaryRowX3
  , registerBoundaryReloadInteraction divSpinBoundaryRowX3 ] ++
    divSpinIdleBoundaryInteractions ++
  [ mainCRegPreInteraction divSpinAddiX1Row
  , mainCMemInteraction divSpinAddiX1Row
  , mainCRegPreInteraction divSpinAddiX2Row
  , mainCMemInteraction divSpinAddiX2Row
  , mainARegPreInteraction divSpinDivRow
  , mainAMemInteraction divSpinDivRow
  , mainBRegPreInteraction divSpinDivRow
  , mainBMemInteraction divSpinDivRow
  , mainCRegPreInteraction divSpinDivRow
  , mainCMemInteraction divSpinDivRow ]

noncomputable def divSpinMemBusZeroResidual : List (Interaction FGL) :=
  divSpinMemBusInteractions.filter (·.mult = 0)

theorem divSpinMemBusZeroResidual_balanced :
    BalancedInteractions divSpinMemBusZeroResidual := by
  apply zeroInteractions_balanced
  · intro interaction h_interaction
    exact of_decide_eq_true (List.mem_filter.mp h_interaction |>.2)
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    have h_le :
        divSpinMemBusZeroResidual.length ≤ divSpinMemBusInteractions.length := by
      exact List.length_filter_le _ _
    have h_length : divSpinMemBusInteractions.length = 92 := by
      rw [divSpinWitness_memBusInteractions]
      norm_num [divSpinBoundaryRows, divSpinMainRows,
        registerBoundaryMemBusInteractions, mainValueMemBusInteractions,
        Function.comp_def]
    omega

private theorem divSpinIdleBoundaryInteractions_filter_ne_zero :
    divSpinIdleBoundaryInteractions.filter (·.mult ≠ 0) =
      divSpinIdleBoundaryInteractions := by
  unfold divSpinIdleBoundaryInteractions
  generalize List.range 28 = indices
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.filter_append]
      rw [ih]
      simp [registerBoundaryMemBusInteractions, registerBoundaryBootInteraction,
        registerBoundaryReloadInteraction]

theorem divSpinMemBusNonzero_filter :
    divSpinMemBusInteractions.filter (·.mult ≠ 0) =
      divSpinMemBusNonzeroChronological := by
  rw [divSpinWitness_memBusInteractions]
  have h_boundary :
      (divSpinBoundaryRows.flatMap registerBoundaryMemBusInteractions).filter
          (·.mult ≠ 0) =
        [ registerBoundaryBootInteraction divSpinBoundaryRowX1
        , registerBoundaryReloadInteraction divSpinBoundaryRowX1
        , registerBoundaryBootInteraction divSpinBoundaryRowX2
        , registerBoundaryReloadInteraction divSpinBoundaryRowX2
        , registerBoundaryBootInteraction divSpinBoundaryRowX3
        , registerBoundaryReloadInteraction divSpinBoundaryRowX3 ] ++
          divSpinIdleBoundaryInteractions := by
    simp only [divSpinBoundaryRows, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.filter_append]
    rw [show
      List.flatMap registerBoundaryMemBusInteractions
          (List.map (fun i => boundaryRowIdle ((i + 4 : Nat) : FGL)) (List.range 28)) =
        divSpinIdleBoundaryInteractions by
          simp only [divSpinIdleBoundaryInteractions, List.flatMap_map]]
    rw [divSpinIdleBoundaryInteractions_filter_ne_zero]
    simp [registerBoundaryMemBusInteractions, registerBoundaryBootInteraction,
      registerBoundaryReloadInteraction]
  have h_addi_x1 :
      (mainValueMemBusInteractions divSpinAddiX1Row).filter (·.mult ≠ 0) =
        [mainCRegPreInteraction divSpinAddiX1Row,
          mainCMemInteraction divSpinAddiX1Row] := by
    simp [mainValueMemBusInteractions, divSpinAddiX1Row, divSpinAddiX1RowWithLast,
      divSpinAddiX1RowTemplate, mainRomRowOf, divSpinAddiBits,
      ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
      mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
      mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction]
  have h_addi_x2 :
      (mainValueMemBusInteractions divSpinAddiX2Row).filter (·.mult ≠ 0) =
        [mainCRegPreInteraction divSpinAddiX2Row,
          mainCMemInteraction divSpinAddiX2Row] := by
    simp [mainValueMemBusInteractions, divSpinAddiX2Row, divSpinAddiX2RowWithLast,
      divSpinAddiX2RowTemplate, mainRomRowOf, divSpinAddiBits,
      ZiskFv.Compliance.SdLdSpinWitness.addiX0Bits,
      mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
      mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction]
  have h_div :
      (mainValueMemBusInteractions divSpinDivRow).filter (·.mult ≠ 0) =
        mainValueMemBusInteractions divSpinDivRow := by
    simp [mainValueMemBusInteractions, divSpinDivRow, divSpinDivRowTemplate,
      mainRomRowOf, divSpinDivBits, mainARegPreInteraction, mainAMemInteraction,
      mainBRegPreInteraction, mainBMemInteraction, mainCRegPreInteraction,
      mainCMemInteraction]
  have h_jal (step : FGL) :
      (mainValueMemBusInteractions (divSpinJalRow step)).filter (·.mult ≠ 0) = [] := by
    simp [mainValueMemBusInteractions, divSpinJalRow, mainRomRowOf,
      ZiskFv.Compliance.AddSpinWitness.addSpinJalBits,
      mainARegPreInteraction, mainAMemInteraction, mainBRegPreInteraction,
      mainBMemInteraction, mainCRegPreInteraction, mainCMemInteraction]
  simp only [List.filter_append, h_boundary, divSpinMainRows,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    h_addi_x1, h_addi_x2, h_div, h_jal]
  rfl

end ZiskFv.Compliance.DivSpinWitness
