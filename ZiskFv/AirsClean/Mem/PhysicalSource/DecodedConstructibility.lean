import ZiskFv.AirsClean.Mem.PhysicalSource.DecodedView
import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage

/-! Supplemental existence for the NEW computed decoding profile. The original
chosen source, buffers and independent numeric GROUP result are unchanged.
This is not a producer/ABI/r.id, production-totality or Root acceptance claim. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

/-- The actual original source image satisfies the structural profile; no
caller supplies a successful read or metadata-agreement certificate. -/
theorem decoded_nonvacuous :
    ∃ decoded : DecodedView occurrence, decodedFromComplete? complete = some decoded := by
  have sameSetup : complete.base.setup = Constructibility.setup := by
    have selected := complete.base.setupSelected
    rw [actual_setup] at selected
    exact Option.some.inj selected.symm
  unfold decodedFromComplete?
  split
  · exact ⟨_, rfl⟩
  · rename_i incompatible
    exfalso
    apply incompatible
    change (∀ index : Fin 21,
      (complete.base.setup.airValuesMap[index.val]?).map (·.stage) =
        some (if index.val < 15 then 1 else 2) ∧
      valueOffset complete.base.setup.airValuesMap index.val =
        (if index.val < 15 then index.val else 15 + 3 * (index.val - 15))) ∧
      (complete.base.setup.airgroupValuesMap[0]?).map (·.stage) = some 2
    rw [sameSetup]
    constructor
    · intro index
      fin_cases index <;> decide +kernel
    · decide +kernel

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage
