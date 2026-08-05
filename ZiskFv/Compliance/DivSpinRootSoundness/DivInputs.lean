import ZiskFv.Compliance.DivSpinRootSoundness.AddiInputs

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance
open ZiskFv.AirsClean.Main
open ZiskFv.Trusted

namespace ZiskFv.Compliance.DivSpinRootSoundness

theorem divSpinArithProviderTable_eq
    (providerTable : Air.Flat.Table FGL)
    (h_table : providerTable ∈ divSpinAcceptedTrace.witness.allTables)
    (h_component :
      providerTable.component =
        ZiskFv.AirsClean.FullEnsemble.arithMulProviderComponent) :
    providerTable = divSpinArithTable := by
  simp [divSpinAcceptedTrace, Air.Flat.EnsembleWitness.allTables,
    divSpinWitness, divSpinTables] at h_table
  rcases h_table with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst providerTable
  all_goals try rfl
  all_goals
    exfalso
    have h_width := congrArg Air.Flat.Component.rawWidth h_component
    first
    | change (0 : Nat) = 44 at h_width
    | change (4 : Nat) = 44 at h_width
    | change (10 : Nat) = 44 at h_width
    | change (16 : Nat) = 44 at h_width
    | change (30 : Nat) = 44 at h_width
    | change (1 : Nat) = 44 at h_width
    | change (6 : Nat) = 44 at h_width
    | change (17 : Nat) = 44 at h_width
    | change (43 : Nat) = 44 at h_width
    | change (29 : Nat) = 44 at h_width
    | change (39 : Nat) = 44 at h_width
    | change (41 : Nat) = 44 at h_width
    omega

theorem divSpinArithProviderRow_eq
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_table : providerTable = divSpinArithTable)
    (h_row : providerRow ∈ providerTable.table) :
    providerRow = divSpinArithRowArray := by
  subst providerTable
  simpa [divSpinArithTable, Air.Flat.Table.table,
    ZiskFv.AirsClean.ArithMul.componentComplete] using h_row

theorem divSpinArithTable_rowInput :
    ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (divSpinArithTable.environment divSpinArithRowArray) =
      divSpinArithRow := by
  change ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
      (Environment.fromInput divSpinArithRow emptyData) = divSpinArithRow
  simp [Air.Flat.Component.rowInput,
    ProvableType.valueFromOffset_zero_fromInput_eq]

private theorem divSpinArithProviderRowInput_eq
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_table : providerTable = divSpinArithTable)
    (h_row : providerRow = divSpinArithRowArray) :
    ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
        (providerTable.environment providerRow) =
      divSpinArithRow := by
  subst providerTable
  subst providerRow
  exact divSpinArithTable_rowInput

private theorem divSpinDivArow_eq
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable).is_external_op divSpinDivIndex.val = 1)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable divSpinAcceptedTrace.program
        divSpinAcceptedTrace.mainTable).op divSpinDivIndex.val = ZiskFv.Trusted.OP_DIV) :
    divArow divSpinAcceptedTrace divSpinSailTrace divSpinDivIndex
      h_main_active h_main_op = divSpinArithRow := by
  unfold divArow
  let H := main_request_div_provided divSpinAcceptedTrace divSpinDivIndex
    h_main_active h_main_op
  have h_table : H.choose = divSpinArithTable := by
    exact divSpinArithProviderTable_eq H.choose H.choose_spec.1
      H.choose_spec.2.choose_spec.2.1
  have h_row : H.choose_spec.2.choose = divSpinArithRowArray := by
    exact divSpinArithProviderRow_eq H.choose H.choose_spec.2.choose h_table
      H.choose_spec.2.choose_spec.1
  change ZiskFv.AirsClean.ArithMul.componentComplete.rowInput
      (H.choose.environment H.choose_spec.2.choose) = _
  exact divSpinArithProviderRowInput_eq H.choose H.choose_spec.2.choose
    h_table h_row

def divSpinDivInputs :
    Inputs_div divSpinAcceptedTrace divSpinSailTrace divSpinDivIndex
      divSpinDivClaim where
  div_input := divSpinDivInput
  promises := by
    refine {
      input_r1_eq := ?_
      input_r2_eq := ?_
      input_rd_eq := rfl
      input_pc_eq := ?_
      exec_len := ?_
      e0_mult := ?_
      e1_mult := ?_
      m0_mult := ?_
      m0_as := ?_
      m1_mult := ?_
      m1_as := ?_
      m2_mult := ?_
      m2_as := ?_
    }
    · simpa [divSpinDivClaim, divSpinDivInput] using divSpinReadX1Div
    · simpa [divSpinDivClaim, divSpinDivInput] using divSpinReadX2Div
    · simp [divSpinSailTrace, divSpinDivIndex, divSpinState, divSpinRegs,
        divSpinDivInput, x1, x2, x3, regidx_to_fin, reg_of_fin,
        Std.ExtDHashMap.get?_insert]
    all_goals
      norm_num [busSub, Pilot.execRowOf, divSpinAcceptedTrace_mainTable_eq,
        divSpinAcceptedMainRowAt, divSpinDivIndex, divSpinMainRows,
        divSpinDivRow, divSpinDivRowTemplate, mainRomRowOf,
        withMainRegisterPrevious]
  h_rs1_value := by
    intro h_main_active h_main_op
    change (6#64).toInt = _
    rw [show divV divSpinAcceptedTrace divSpinSailTrace divSpinDivIndex
      h_main_active h_main_op = vOfDivuRow divSpinArithRow by
        unfold divV
        rw [divSpinDivArow_eq h_main_active h_main_op]]
    norm_num [BitVec.toInt, vOfDivuRow, divSpinArithRow, divSpinArithDivRow,
      ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinDividend,
      divSpinDivisor, divSpinArithDivFree,
      ZiskFv.PackedBitVec.MulNoWrap.packed4,
      ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]
  h_rs2_value := by
    intro h_main_active h_main_op
    change (2#64).toInt = _
    rw [show divV divSpinAcceptedTrace divSpinSailTrace divSpinDivIndex
      h_main_active h_main_op = vOfDivuRow divSpinArithRow by
        unfold divV
        rw [divSpinDivArow_eq h_main_active h_main_op]]
    norm_num [BitVec.toInt, vOfDivuRow, divSpinArithRow, divSpinArithDivRow,
      ZiskFv.AirsClean.ArithDiv.arithDivRowOf, divSpinDividend,
      divSpinDivisor, divSpinArithDivFree,
      ZiskFv.PackedBitVec.MulNoWrap.packed4,
      ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]
  h_pc_bridge := by rw [divSpinMainPc]; norm_num [divSpinDivIndex, divSpinDivInput]

end ZiskFv.Compliance.DivSpinRootSoundness
