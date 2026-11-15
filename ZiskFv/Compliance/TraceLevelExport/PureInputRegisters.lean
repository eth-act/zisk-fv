import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement

namespace ZiskFv.Compliance

variable {n : ℕ}

/-- Architectural x0 is constant; all other values come from the ZisK register file. -/
noncomputable def pureInputRegValue {trace : AcceptedZiskTrace n}
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i)) (j : ℕ) (k : Fin 32) : BitVec 64 :=
  if k = 0 then 0 else ziskRegFile steps rowDecodes j k

theorem read_pureInputRegValue {trace : AcceptedZiskTrace n}
    (steps : ∀ i, ZiskStep trace i)
    (rowDecodes : ∀ i, RowDecode trace i (steps i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin n) (h_reg : RegAgree steps rowDecodes init i.val) (k : Fin 32) :
    read_xreg k (chainedSailTrace steps init i) =
      EStateM.Result.ok (pureInputRegValue steps rowDecodes i.val k)
        (chainedSailTrace steps init i) := by
  by_cases hk : k = 0
  · subst k
    simp [pureInputRegValue, read_xreg]
  · simpa [pureInputRegValue, hk, chainedSailTrace] using
      read_xreg_of_regAgree steps rowDecodes init i.val k hk h_reg

end ZiskFv.Compliance
