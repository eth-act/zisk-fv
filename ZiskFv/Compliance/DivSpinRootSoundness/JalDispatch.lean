import ZiskFv.Compliance.DivSpinRootSoundness.DivInputs

open ZiskFv.Compliance
open ZiskFv.Compliance.DivSpinWitness

namespace ZiskFv.Compliance.DivSpinRootSoundness

def divSpinJalInputs :
    Inputs_jal divSpinAcceptedTrace divSpinSailTrace divSpinJalIndex
      divSpinJalClaim where
  jal_input := divSpinJalInput
  misa_val := divSpinMisa
  h_pc_bridge := by rw [divSpinMainPc]; norm_num [divSpinJalIndex, divSpinJalInput]
  h_input_rd := rfl
  h_input_pc := by
    simp [divSpinJalInput, divSpinSailTrace, divSpinJalIndex,
      divSpinState, divSpinRegs, x1, x2, x3, regidx_to_fin, reg_of_fin,
      Std.ExtDHashMap.get?_insert]
  h_input_misa := by
    simp [divSpinSailTrace, divSpinJalIndex, divSpinState, divSpinRegs,
      x1, x2, x3, regidx_to_fin, reg_of_fin, Std.ExtDHashMap.get?_insert]
  h_misa_c := by simp [divSpinMisa]
  h_success := by simp [divSpinJalInput, PureSpec.execute_JAL_pure]
  h_input_imm := rfl

def divSpinProgramDecodes :
    ∀ i : Fin 4, ProgramDecode divSpinAcceptedTrace i (divSpinZiskStep i)
  | ⟨0, _⟩ => divSpinAddiX1ProgramDecode
  | ⟨1, _⟩ => divSpinAddiX2ProgramDecode
  | ⟨2, _⟩ => divSpinDivProgramDecode
  | ⟨3, _⟩ => divSpinJalProgramDecode

def divSpinInputsAgree :
    ∀ i : Fin 4, InputsAgree divSpinAcceptedTrace divSpinSailTrace i
      (divSpinZiskStep i)
  | ⟨0, _⟩ => divSpinAddiX1Inputs
  | ⟨1, _⟩ => divSpinAddiX2Inputs
  | ⟨2, _⟩ => divSpinDivInputs
  | ⟨3, _⟩ => divSpinJalInputs

/-- The two root PC premises for this witness, from the per-row family above
    (`pcSeed_of_inputsAgree` / `inputsAgreeCore_of_inputsAgree`). -/
def divSpinPcSeed : SegmentPcSeed divSpinAcceptedTrace divSpinSailTrace :=
  pcSeed_of_inputsAgree divSpinInputsAgree

def divSpinInputsAgreeCore :
    ∀ i : Fin 4, InputsAgreeCore divSpinAcceptedTrace divSpinSailTrace i (divSpinZiskStep i) :=
  fun i => inputsAgreeCore_of_inputsAgree i (divSpinZiskStep i) (divSpinInputsAgree i)
end ZiskFv.Compliance.DivSpinRootSoundness
