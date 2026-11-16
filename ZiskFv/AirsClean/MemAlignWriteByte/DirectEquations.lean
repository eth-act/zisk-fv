import Extraction.MemAlignWriteByte

/-! Source-only Direct equations. These deliberately accept the actual source
AIR value without replacing it by an honest-builder count. Source lines106-115
and generated c11-c13 do not identify that value with the number of zero rows.
The separate Segment constructor establishes that identity for honest witnesses.
No AcceptedTrace constructor is supplied here. -/
namespace ZiskFv.AirsClean.MemAlignWriteByte

variable {F : Type} [Field F]

def loadPaddingDenominator (alpha gamma : F) : F :=
  (((((8 * alpha) * alpha) * alpha + 1) * alpha + 10) + gamma)

def selectedStorePaddingDenominator (alpha gamma : F) : F :=
  ((((alpha * alpha) * alpha + 2) * alpha + 10) + gamma)

def alignedStorePaddingDenominator (alpha gamma : F) : F :=
  ((((((8 * alpha + 1) * alpha) * alpha + 2) * alpha + 10) + gamma))

def DirectSpec (paddingSize imLoad imSelectedStore imAlignedStore alpha gamma : F) : Prop :=
  imLoad * loadPaddingDenominator alpha gamma - paddingSize = 0 ∧
  imSelectedStore * selectedStorePaddingDenominator alpha gamma - (0 - paddingSize) = 0 ∧
  imAlignedStore * alignedStorePaddingDenominator alpha gamma - paddingSize = 0

/-- All three actual generated source equations, including the negative selected
STORE update. There is no physical-row-count premise on the right. -/
theorem directSpec_iff_extracted
    {C : Type → Type → Sort u} [Extraction.Circuit F F C] (c : C F F) (r : ℕ) :
    DirectSpec (Extraction.Circuit.exposed c (index := 0))
      (Extraction.Circuit.exposed c (index := 1))
      (Extraction.Circuit.exposed c (index := 2))
      (Extraction.Circuit.exposed c (index := 3))
      (Extraction.Circuit.challenge c (index := 0))
      (Extraction.Circuit.challenge c (index := 1)) ↔
    MemAlignWriteByte.extraction.constraint_11_every_row c r ∧
    MemAlignWriteByte.extraction.constraint_12_every_row c r ∧
    MemAlignWriteByte.extraction.constraint_13_every_row c r := Iff.rfl

/-- Exact limitation of the Direct slice: every field-valued padding count has
local Direct witnesses when compressed-message denominators are nonzero. This
is not a whole-AIR counterexample or an assumption about ensemble balance. -/
theorem directSpec_constructible_arbitrary_count (paddingSize alpha gamma : F)
    (hload : loadPaddingDenominator alpha gamma ≠ 0)
    (hselected : selectedStorePaddingDenominator alpha gamma ≠ 0)
    (haligned : alignedStorePaddingDenominator alpha gamma ≠ 0) :
    ∃ imLoad imSelectedStore imAlignedStore,
      DirectSpec paddingSize imLoad imSelectedStore imAlignedStore alpha gamma := by
  refine ⟨paddingSize / loadPaddingDenominator alpha gamma,
    (0 - paddingSize) / selectedStorePaddingDenominator alpha gamma,
    paddingSize / alignedStorePaddingDenominator alpha gamma, ?_⟩
  simp [DirectSpec, hload, hselected, haligned]

end ZiskFv.AirsClean.MemAlignWriteByte
