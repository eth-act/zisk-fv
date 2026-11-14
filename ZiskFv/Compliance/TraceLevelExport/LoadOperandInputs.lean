import ZiskFv.Compliance.TraceLevelExport.LoadOperandBinding
import ZiskFv.Compliance.TraceLevelExport.PureInputs

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open LoadOperandBinding

/-- Successful Sail reads and source-derived ROM selectors identify the actual
A value. The x0 branch uses accepted SourceSpec immediate-zero equations; only
nonzero registers use the register-lane bridge. No default value is assumed. -/
private theorem load_a0_of_source {n : Nat}
    (trace : AcceptedZiskTrace n)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (i : Fin trace.numInstructions) (r1 : regidx) (value : BitVec 64)
    (pins : LoadMainASourcePins trace i (storeRegBits r1).toNat)
    (lb : LaneBridge trace state i.val)
    (h_read : read_xreg (regidx_to_fin r1) state = EStateM.Result.ok value state) :
    (mainOfTable trace.program trace.mainTable).a_0 i.val =
      ZiskFv.Trusted.lane_lo value := by
  have h_index : (regidx_to_fin r1).val = (storeRegBits r1).toNat := by
    cases r1 <;> rfl
  have h_zero : (storeRegBits r1).toNat = 0 ↔ regidx_to_fin r1 = 0 := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [h_index] using h
    · intro h
      have hval := congrArg Fin.val h
      simpa only [h_index] using hval
  have h_nonzero : (storeRegBits r1).toNat ≠ 0 ↔ regidx_to_fin r1 ≠ 0 :=
    not_congr h_zero
  have h_small : (storeRegBits r1).toNat < GL_prime :=
    Nat.lt_trans (storeRegBits r1).isLt (by decide)
  have h_cast : ((storeRegBits r1).toNat : FGL) =
      Transpiler.ind (regidx_to_fin r1) := by
    apply Fin.ext
    change (storeRegBits r1).toNat % GL_prime = (regidx_to_fin r1).val
    rw [Nat.mod_eq_of_lt h_small, h_index]
  have h_lane := a_lo_of_laneBridge trace state i.val (regidx_to_fin r1) lb
    (RomDecodeBinding.mainSourceSpec_at trace ⟨i.val, trace.mainTable_index i⟩)
    (by simpa only [mainRowWithRomLd, h_nonzero] using pins.h_a_src_reg)
    (by simpa only [mainRowWithRomLd] using pins.h_a_offset_imm0.trans h_cast)
    (by simpa only [mainRowWithRomLd, h_zero] using pins.h_a_src_imm)
    (by simpa only [mainRowWithRomLd] using pins.h_a_imm1)
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
    state (regidx_to_fin r1) value h_read] at h_lane
  exact h_lane

/-- Reconstruct the seven load A-lane facts from the SAME existing raw/ROM
binding and current register-lane invariant. The public root takes no new
selector certificate, and no protected Decode/Inputs record is extended. -/
noncomputable def loadInputsOfRawSource {n rawLength : Nat}
    (trace : AcceptedZiskTrace n) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions) (zs : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (hbind : RawProgramBinding.ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i zs start addr rawProgram)
    (lb : LaneBridge trace (binding i) i.val)
    (ia : InputsAgreeCore trace binding i zs) : InputsAgreeCore trace binding i zs :=
  match zs, rawDecode, ia with
  | .ld c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_ld_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | .lbu c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_lbu_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | .lhu c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_lhu_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | .lwu c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_lwu_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | .lb c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_lb_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | .lh c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_lh_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | .lw c, raw, inputs => { inputs with
      h_a0_value := load_a0_of_source trace (binding i) i c.r1 inputs.input.r1_val
        (loadMainASource_lw_of_rawProgramDecode trace i c
          start addr rawProgram hbind raw.down.down)
        lb (Classical.choose_spec inputs.h_input_r1) }
  | _, _, inputs => inputs

end ZiskFv.Compliance
