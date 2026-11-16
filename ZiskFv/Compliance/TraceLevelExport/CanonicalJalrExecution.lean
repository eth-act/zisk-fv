import ZiskFv.Compliance.TraceLevelExport.ParsedCanonicalPhysicalState
import ZiskFv.Compliance.AddFaithfulPaddedRootSoundness
import ZiskFv.Completeness.Rv64im.SailDecode.IsaState

/-!
# Concrete Sail execution for the repeated source JALR

This constructs real dependent Sail register storage, not a register-read
certificate. The existing zero-GPR constructor is extended by actual typed
writes of Machine privilege, mseccfg=0 and MISA.M=1. M implies enabled Zmmul;
standalone Zmmul support remains false. These are constructible platform/input
values, not a claim that an upstream reset routine installs these CSRs.

The instruction is the same JALR x1,x2,1 whose checked source lowering has
width2 at both occurrences. Actual generated Sail execution and retirement
are performed twice. This does NOT construct an Accepted4 provider world or
claim the physical-channel StepSound equation without that world.

The final theorem exposes a separate exact interface obstruction: the current
legacy Root's total Fin4 raw-decode/alignment domain cannot describe these two
source instructions. Auxiliary AND rows must not become fake RV instructions.
No protected interface or validator is changed here.
-/

namespace ZiskFv.Compliance.CanonicalSourceParser

open CanonicalExecutionRows SerializedExecutionRows RawProgramBinding
open AddFaithfulPaddedRootSoundness
open ZiskFv.Completeness.SailDecode

/-- All31 tracked GPRs are genuinely present and zero; MISA is then installed
by the already proved actual M-enabling typed write. -/
def repeatJalrInit : PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  withMEnabled
    (write_reg_state
      (write_reg_state (addFaithfulState (0#64)) Register.cur_privilege Privilege.Machine)
      Register.mseccfg (0#64))

def repeatJalrInstruction : instruction :=
  .JALR (1#12, .Regidx (2#5), .Regidx (1#5))

private def repeatJalrInput : PureSpec.JalrInput :=
  { imm := 1#12, rs1_val := 0#64, rd := 1, PC := 0#64 }

/-- The actual non-retired generated Sail post-state: target0 and link4. -/
def repeatJalrPost
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :=
  write_reg_state (write_reg_state state Register.nextPC (0#64)) Register.x1 (4#64)

noncomputable def repeatJalrSecond := retirePC (repeatJalrPost repeatJalrInit)

noncomputable def repeatJalrFinal := retirePC (repeatJalrPost repeatJalrSecond)

theorem repeatJalrInit_regBoot :
    ∀ k : Fin 32, k ≠ 0 → repeatJalrInit.regs.get? (reg_of_fin k) =
      some (cast (by rw [register_type_reg_of_fin_equiv]) (0 : BitVec 64)) := by
  intro k hk
  have boot := addFaithfulRegBoot k hk
  unfold repeatJalrInit withMEnabled
  apply writeReg_read_diff
  · apply writeReg_read_diff
    · apply writeReg_read_diff boot
      fin_cases k <;> decide
    · fin_cases k <;> decide
  · fin_cases k <;> decide

theorem repeatJalrInit_isa : IsaExtensionsEnabled repeatJalrInit :=
  withMEnabled_isaExtensionsEnabled _

theorem repeatJalrInit_zmmul :
    LeanRV64D.Functions.currentlyEnabled extension.Ext_Zmmul repeatJalrInit =
      EStateM.Result.ok true repeatJalrInit :=
  zmmul_enabled_of_isaExtensionsEnabled _ repeatJalrInit_isa

private theorem repeatJalrInit_reads :
    repeatJalrInit.regs.get? Register.PC = some (0#64) ∧
    repeatJalrInit.regs.get? Register.misa = some (4096#64) ∧
    read_xreg (2 : Fin 32) repeatJalrInit = EStateM.Result.ok (0#64) repeatJalrInit ∧
    Sail.readReg Register.cur_privilege repeatJalrInit =
      EStateM.Result.ok Privilege.Machine repeatJalrInit ∧
    Sail.readReg Register.mseccfg repeatJalrInit =
      EStateM.Result.ok (0#64) repeatJalrInit := by
  simp [repeatJalrInit, withMEnabled, write_reg_state, addFaithfulState,
    addFaithfulRegs, addFaithfulZeroRegs, addFaithfulMisa, x1,
    regidx_to_fin, read_xreg, reg_of_fin, Sail.readReg, PreSail.readReg,
    Std.ExtDHashMap.get?_insert]

private theorem repeatJalr_execute
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (pc : state.regs.get? Register.PC = some (0#64))
    (misa : state.regs.get? Register.misa = some (4096#64))
    (rs1 : read_xreg (2 : Fin 32) state = EStateM.Result.ok (0#64) state)
    (privilege : Sail.readReg Register.cur_privilege state =
      EStateM.Result.ok Privilege.Machine state)
    (security : Sail.readReg Register.mseccfg state = EStateM.Result.ok (0#64) state) :
    execute_instruction repeatJalrInstruction state =
      EStateM.Result.ok (ExecutionResult.Retire_Success ()) (repeatJalrPost state) := by
  unfold execute_instruction repeatJalrInstruction
  rw [PureSpec.execute_JALR_pure_equiv (state := state) (misa := 4096#64)
    (mseccfg := 0#64) repeatJalrInput (1#12) (.Regidx (2#5)) (.Regidx (1#5))
    rfl rfl (by simpa [regidx_to_fin] using rs1) pc misa (by decide) privilege security]
  simp [repeatJalrInput, PureSpec.execute_JALR_pure, repeatJalrPost,
    write_xreg, reg_of_fin, writeReg_state_success]

theorem repeatJalr_first_execution :
    execute_instruction repeatJalrInstruction repeatJalrInit =
      EStateM.Result.ok (ExecutionResult.Retire_Success ()) (repeatJalrPost repeatJalrInit) :=
  repeatJalr_execute repeatJalrInit repeatJalrInit_reads.1 repeatJalrInit_reads.2.1
    repeatJalrInit_reads.2.2.1 repeatJalrInit_reads.2.2.2.1 repeatJalrInit_reads.2.2.2.2

/-- The actual generated Sail encoder returns the exact checked source word
on this same state. Kernel reduction only; no ext_decode direction is asserted. -/
theorem repeatJalr_actual_encoder :
    SailEncodesToIn repeatJalrInit repeatJalrInstruction (repeatJalrRawProgram 0) := by
  rfl

private theorem repeatJalrSecond_reads :
    repeatJalrSecond.regs.get? Register.PC = some (0#64) ∧
    repeatJalrSecond.regs.get? Register.misa = some (4096#64) ∧
    read_xreg (2 : Fin 32) repeatJalrSecond = EStateM.Result.ok (0#64) repeatJalrSecond ∧
    Sail.readReg Register.cur_privilege repeatJalrSecond =
      EStateM.Result.ok Privilege.Machine repeatJalrSecond ∧
    Sail.readReg Register.mseccfg repeatJalrSecond =
      EStateM.Result.ok (0#64) repeatJalrSecond := by
  simp [repeatJalrSecond, retirePC, repeatJalrPost, repeatJalrInit, withMEnabled,
    write_reg_state, addFaithfulState, addFaithfulRegs, addFaithfulZeroRegs,
    addFaithfulMisa, x1, regidx_to_fin, read_xreg, reg_of_fin,
    Sail.readReg, PreSail.readReg, Std.ExtDHashMap.get?_insert]

/-- Two real generated Sail steps for the actual source word and width2+2.
The architectural continuation is executable, not a firstSound promise.
Physical-channel equivalence still requires the same actual Accepted world. -/
theorem repeatedJalr_actual_sail_execution :
    SailEncodesToIn repeatJalrInit repeatJalrInstruction (repeatJalrRawProgram 0) ∧
    sourceEnd repeatJalrLowerings = 4 ∧
    execute_instruction repeatJalrInstruction repeatJalrInit =
      EStateM.Result.ok (ExecutionResult.Retire_Success ()) (repeatJalrPost repeatJalrInit) ∧
    execute_instruction repeatJalrInstruction repeatJalrSecond =
      EStateM.Result.ok (ExecutionResult.Retire_Success ()) (repeatJalrPost repeatJalrSecond) ∧
    repeatJalrSecond.regs.get? Register.PC = some (0#64) ∧
    repeatJalrSecond.regs.get? Register.x1 = some (4#64) ∧
    repeatJalrSecond.regs.get? Register.x2 = some (0#64) ∧
    repeatJalrSecond.mem = repeatJalrInit.mem ∧
    repeatJalrFinal.regs.get? Register.PC = some (0#64) ∧
    repeatJalrFinal.regs.get? Register.x1 = some (4#64) ∧
    repeatJalrFinal.regs.get? Register.x2 = some (0#64) ∧
    repeatJalrFinal.mem = repeatJalrInit.mem := by
  refine ⟨repeatJalr_actual_encoder, repeatJalr_sourceEnd, repeatJalr_first_execution, ?_,
    repeatJalrSecond_reads.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact repeatJalr_execute repeatJalrSecond repeatJalrSecond_reads.1
      repeatJalrSecond_reads.2.1 repeatJalrSecond_reads.2.2.1
      repeatJalrSecond_reads.2.2.2.1 repeatJalrSecond_reads.2.2.2.2
  all_goals simp [repeatJalrFinal, repeatJalrSecond, retirePC, repeatJalrPost, repeatJalrInit,
    withMEnabled, write_reg_state, addFaithfulState, addFaithfulRegs,
    addFaithfulZeroRegs, x1, regidx_to_fin, Std.ExtDHashMap.get?_insert]

/-- Exact structural exclusion, using only existing current-Root premises.
Its total Fin4 family cannot encode two real width2 words at physical0/2. -/
theorem repeatedJalr_no_legacy_total_domain
    (trace : AcceptedZiskTrace 4)
    (steps : ∀ i : Fin 4, ZiskStep trace i)
    (start : Fin 1 → Fin trace.programLength)
    (binding : ProgramRowsBinding trace start (fun _ => 0) repeatJalrRawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start (fun _ => 0)
      repeatJalrRawProgram)
    (aligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start (fun _ => 0)
        repeatJalrRawProgram binding (rawDecodes i)))) : False := by
  obtain ⟨selected, lowerings, _, starts, _⟩ :=
    RawDecodeRowLowering.old_raw_source_widths_and_placement trace steps start (fun _ => 0)
      repeatJalrRawProgram binding rawDecodes aligned
  have rows : (lowerings (0 : Fin 4)).rows = repeatJalrLowering.rows := by
    apply Aeneas.Std.Result.ok.inj
    exact (lowerings (0 : Fin 4)).source.symm.trans repeatJalrLowering.source
  have width : (lowerings (0 : Fin 4)).width = 2 := by
    change (lowerings (0 : Fin 4)).rows.row_count.val = 2
    rw [rows]
    exact repeatJalrLowerings_width 0
  have next := prefix_succ (sourceWidth lowerings) (0 : Fin 4)
  change sourceStart lowerings (1 : Fin 4) =
    sourceStart lowerings (0 : Fin 4) + (lowerings (0 : Fin 4)).width at next
  rw [starts 0, starts 1, width] at next
  norm_num at next

end ZiskFv.Compliance.CanonicalSourceParser
