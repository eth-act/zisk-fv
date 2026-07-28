import ZiskFv.Compliance.DivSpinRootSoundness.Facts

open Goldilocks
open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness
open ZiskFv.Compliance.Instantiation
open ZiskFv.Trusted

namespace ZiskFv.Compliance.DivSpinRootSoundness

def divSpinAddiX1OutsideDefectRegion :
    RowOutsideDefectRegion divSpinAcceptedTrace divSpinAddiX1Index
      (divSpinZiskStep divSpinAddiX1Index) := by
  unfold RowOutsideDefectRegion divSpinZiskStep MainSequentialPcDomain mainPcVal
  rw [divSpinMainPc]
  change (0 : Nat) < GL_prime - 4
  norm_num

def divSpinAddiX2OutsideDefectRegion :
    RowOutsideDefectRegion divSpinAcceptedTrace divSpinAddiX2Index
      (divSpinZiskStep divSpinAddiX2Index) := by
  unfold RowOutsideDefectRegion divSpinZiskStep MainSequentialPcDomain mainPcVal
  rw [divSpinMainPc]
  change (4 : Nat) < GL_prime - 4
  norm_num

private theorem divSpinArithRow_signedDivisorInt :
    Defects.signedDivisorInt (vOfDivuRow divSpinArithRow) 0 = 2 := by
  norm_num [Defects.signedDivisorInt, vOfDivuRow, divSpinArithRow,
    divSpinArithDivRow, ZiskFv.AirsClean.ArithDiv.arithDivRowOf,
    divSpinDividend, divSpinDivisor, divSpinArithDivFree,
    ZiskFv.PackedBitVec.MulNoWrap.packed4,
    ZiskFv.Airs.ArithCarryChainCompleteness.chunk16]

private theorem divSpinArithRow_signedRemainderInt :
    Defects.signedRemainderInt (vOfDivuRow divSpinArithRow) 0 = 0 := by
  norm_num [Defects.signedRemainderInt, vOfDivuRow, divSpinArithRow,
    divSpinArithDivRow, ZiskFv.AirsClean.ArithDiv.arithDivRowOf,
    divSpinDividend, divSpinDivisor, divSpinArithDivFree,
    ZiskFv.PackedBitVec.MulNoWrap.packed4]

private theorem divSpinArithRow_notQuotientSignForge :
    ¬ Defects.SignedDivQuotientSignForge (vOfDivuRow divSpinArithRow) 0 := by
  apply Defects.honest_signedDiv_quotient_sign_not_forge
  norm_num [vOfDivuRow, divSpinArithRow,
    divSpinArithDivRow, ZiskFv.AirsClean.ArithDiv.arithDivRowOf,
    divSpinDividend, divSpinDivisor, divSpinArithDivFree,
    ZiskFv.PackedBitVec.MulNoWrap.packed4,
    ZiskFv.PackedBitVec.SignedChunkLift.toIntZ]

def divSpinDivOutsideDefectRegion :
    RowOutsideDefectRegion divSpinAcceptedTrace divSpinDivIndex
      (divSpinZiskStep divSpinDivIndex) := by
  constructor
  · unfold MainSequentialPcDomain mainPcVal
    rw [divSpinMainPc]
    change (8 : Nat) < GL_prime - 4
    norm_num
  · intro providerTable h_table providerRow h_row h_component h_spec h_match op2
    have h_provider :
        providerTable = divSpinArithTable := by
      exact divSpinArithProviderTable_eq providerTable h_table h_component
    have h_providerRow : providerRow = divSpinArithRowArray := by
      exact divSpinArithProviderRow_eq providerTable providerRow h_provider h_row
    subst providerTable
    subst providerRow
    dsimp only
    rw [divSpinArithTable_rowInput]
    intro h_op2
    have h_op2_value : op2.toInt = 2 := by
      rw [h_op2, divSpinArithRow_signedDivisorInt]
    constructor
    · intro h_forge
      rcases h_forge with ⟨h_ne, h_abs⟩
      rw [h_op2_value, show Defects.signedRemainderInt
        (vOfDivuRow divSpinArithRow) 0 = 0 from
          divSpinArithRow_signedRemainderInt] at h_abs
      norm_num at h_abs
    · exact divSpinArithRow_notQuotientSignForge

def divSpinJalOutsideDefectRegion :
    RowOutsideDefectRegion divSpinAcceptedTrace divSpinJalIndex
      (divSpinZiskStep divSpinJalIndex) where
  h_no_fgl_wrap := by
    unfold mainPcVal
    rw [divSpinMainPc]
    change 12 + (BitVec.signExtend 64 (0#21)).toNat < GL_prime
    simp
  h_pc_bound := by
    unfold MainSequentialPcDomain mainPcVal
    rw [divSpinMainPc]
    change 12 < GL_prime - 4
    norm_num
  h_pc_offset_lt_2_32 := by
    intro pc hpc
    unfold mainPcVal at hpc
    rw [divSpinMainPc] at hpc
    rw [BitVec.toNat_add]
    rw [← hpc]
    norm_num [divSpinJalIndex]

def divSpinOutsideDefectRegion :
    ∀ i : Fin 4, RowOutsideDefectRegion divSpinAcceptedTrace i
      (divSpinZiskStep i)
  | ⟨0, _⟩ => divSpinAddiX1OutsideDefectRegion
  | ⟨1, _⟩ => divSpinAddiX2OutsideDefectRegion
  | ⟨2, _⟩ => divSpinDivOutsideDefectRegion
  | ⟨3, _⟩ => divSpinJalOutsideDefectRegion

end ZiskFv.Compliance.DivSpinRootSoundness
