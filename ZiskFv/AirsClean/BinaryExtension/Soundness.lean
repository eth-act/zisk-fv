import ZiskFv.AirsClean.BinaryExtension.Spec

/-!
# BinaryExtension Soundness

Trivial — Spec is `True`.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

theorem soundness (_row : BinaryExtensionRow FGL)
    (_h_assumptions : Assumptions _row) :
    Spec _row := trivial

end ZiskFv.AirsClean.BinaryExtension
