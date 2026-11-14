import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement

namespace ZiskFv.Compliance

/-- The input surface requires a present PC in every arm, including the canonical
load inputs. This extracts presence without interpreting an absent register as zero. -/
theorem inputsAgreeCore_pc_present {n : Nat} {trace : AcceptedZiskTrace n}
    {binding : SailTrace n} (i : Fin n) (step : ZiskStep trace i)
    (inputs : InputsAgreeCore trace binding i step) :
    ∃ pc, (binding i).regs.get? Register.PC = some pc := by
  cases step <;>
    first
    | exact inputs.h_input_pc
    | exact ⟨_, inputs.h_input_pc⟩
    | exact ⟨_, inputs.promises.input_pc_eq⟩

/-- A successful sound step writes a present nextPC; Sail's existing retire law
therefore gives PC presence at the successor. This does not require row-index
alignment or a per-successor PC-presence promise. -/
theorem pc_present_succ_of_stepSound {n : Nat} {trace : AcceptedZiskTrace n}
    {binding : SailTrace n}
    {steps : ∀ i, ZiskStep trace i}
    {rowDecodes : ∀ i, RowDecode trace i (steps i)}
    (chain : SailRetireChain trace binding steps)
    (j : Nat) (h : j + 1 < n)
    (sound : StepSound trace binding ⟨j, Nat.lt_of_succ_lt h⟩
      (steps ⟨j, Nat.lt_of_succ_lt h⟩) (rowDecodes ⟨j, Nat.lt_of_succ_lt h⟩)) :
    ∃ pc, (binding ⟨j + 1, h⟩).regs.get? Register.PC = some pc := by
  let i : Fin n := ⟨j, Nat.lt_of_succ_lt h⟩
  obtain ⟨result, post, h_ok⟩ :=
    stepChannelOutput_busEffect_ok i (steps i) (rowDecodes i) (binding i)
  have hrows := stepChannelOutput_execRows i (steps i) (rowDecodes i)
  have hlength : (stepChannelOutput i (steps i) (rowDecodes i)).execRows.length = 2 := by
    rw [hrows]
    rfl
  have hread : (stepChannelOutput i (steps i) (rowDecodes i)).execRows[0]!.multiplicity = -1 := by
    rw [hrows]
    rfl
  have hwrite : (stepChannelOutput i (steps i) (rowDecodes i)).execRows[1]!.multiplicity = 1 := by
    rw [hrows]
    rfl
  have hnext := nextPC_of_busEffect_ok _ _ _ _ _ hlength hread hwrite h_ok
  have hsail : sailStepResult binding i (steps i) = .ok result post := by
    rw [(stepSound_iff i (steps i) (rowDecodes i)).mp sound]
    exact h_ok
  rw [chain.retire j h result post hsail, hnext]
  exact ⟨_, rfl⟩

end ZiskFv.Compliance
