import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLoweringRegister
import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLoweringMemoryMext
import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLoweringControl

/-!
# Existing executed-word evidence determines actual source widths

This is a comparison theorem on the existing same-world accepted trace,
ProgramRowsBinding, and RawProgramDecode domain. Its parser success is a
conclusion, not a new root binder. All63 dispatch arms are consumed below.
The final numerical comparison uses the existing StepRowsAligned premise;
it does not establish mapped Sail/PC/register/memory continuity or replace
any public root/validator/dispatch/extraction interface.
-/

namespace ZiskFv.Compliance.RawDecodeRowLowering

open RawProgramBinding
open CanonicalExecutionRows
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

/-- Every existing executed-word raw-decode arm supplies a successful accepted
source lowering, with the exact width of its existing decode-selected producer. -/
theorem sourceWidth_of_rawProgramDecode {n rawLength : Nat}
    (trace : AcceptedZiskTrace n) (i : Fin trace.numInstructions)
    (step : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i step start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram
      (stepProducerRow i step (rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i step start addr rawProgram
          binding rawDecode)) + 1 - i.val) := by
  cases step with
  | sub c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sub trace i c addr rawProgram rawDecode.down.down
  | and c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_and trace i c addr rawProgram rawDecode.down.down
  | or c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_or trace i c addr rawProgram rawDecode.down.down
  | xor c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_xor trace i c addr rawProgram rawDecode.down.down
  | slt c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_slt trace i c addr rawProgram rawDecode.down.down
  | sltu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sltu trace i c addr rawProgram rawDecode.down.down
  | andi c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_andi trace i c addr rawProgram rawDecode.down.down
  | ori c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_ori trace i c addr rawProgram rawDecode.down.down
  | xori c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_xori trace i c addr rawProgram rawDecode.down.down
  | slti c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_slti trace i c addr rawProgram rawDecode.down.down
  | sltiu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sltiu trace i c addr rawProgram rawDecode.down.down
  | sll c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sll trace i c addr rawProgram rawDecode.down.down
  | srl c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_srl trace i c addr rawProgram rawDecode.down.down
  | sra c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sra trace i c addr rawProgram rawDecode.down.down
  | slli c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_slli trace i c addr rawProgram rawDecode.down.down
  | srli c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_srli trace i c addr rawProgram rawDecode.down.down
  | srai c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_srai trace i c addr rawProgram rawDecode.down.down
  | add c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_add trace i c addr rawProgram rawDecode.down.down
  | addi c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_addi trace i c addr rawProgram rawDecode.down.down
  | subw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_subw trace i c addr rawProgram rawDecode.down.down
  | addw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_addw trace i c addr rawProgram rawDecode.down.down
  | addiw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_addiw trace i c addr rawProgram rawDecode.down.down
  | sllw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sllw trace i c addr rawProgram rawDecode.down.down
  | srlw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_srlw trace i c addr rawProgram rawDecode.down.down
  | sraw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sraw trace i c addr rawProgram rawDecode.down.down
  | slliw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_slliw trace i c addr rawProgram rawDecode.down.down
  | srliw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_srliw trace i c addr rawProgram rawDecode.down.down
  | sraiw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sraiw trace i c addr rawProgram rawDecode.down.down
  | mul c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_mul trace i c addr rawProgram rawDecode.down.down
  | mulh c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_mulh trace i c addr rawProgram rawDecode.down.down
  | mulhsu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_mulhsu trace i c addr rawProgram rawDecode.down.down
  | mulw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_mulw trace i c addr rawProgram rawDecode.down.down
  | mulhu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_mulhu trace i c addr rawProgram rawDecode.down.down
  | div c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_div trace i c addr rawProgram rawDecode.down.down
  | rem c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_rem trace i c addr rawProgram rawDecode.down.down
  | divw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_divw trace i c addr rawProgram rawDecode.down.down
  | remw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_remw trace i c addr rawProgram rawDecode.down.down
  | divu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_divu trace i c addr rawProgram rawDecode.down.down
  | divuw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_divuw trace i c addr rawProgram rawDecode.down.down
  | remu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_remu trace i c addr rawProgram rawDecode.down.down
  | remuw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_remuw trace i c addr rawProgram rawDecode.down.down
  | beq c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_beq trace i c start addr rawProgram rawDecode.down.down
  | bne c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_bne trace i c start addr rawProgram rawDecode.down.down
  | blt c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_blt trace i c start addr rawProgram rawDecode.down.down
  | bge c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_bge trace i c start addr rawProgram rawDecode.down.down
  | bltu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_bltu trace i c start addr rawProgram rawDecode.down.down
  | bgeu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_bgeu trace i c start addr rawProgram rawDecode.down.down
  | lui c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lui trace i c start addr rawProgram rawDecode.down.down
  | auipc c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_auipc trace i c start addr rawProgram rawDecode.down.down
  | jal c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_jal trace i c start addr rawProgram rawDecode.down.down
  | jalr c =>
      cases rawDecode with
      | up rawDecode =>
        cases rawDecode with
        | up evidence => exact sourceWidth_jalr trace i c start addr rawProgram binding evidence
  | sb c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sb trace i c addr rawProgram rawDecode.down.down
  | sh c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sh trace i c addr rawProgram rawDecode.down.down
  | sw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sw trace i c addr rawProgram rawDecode.down.down
  | sd c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_sd trace i c addr rawProgram rawDecode.down.down
  | ld c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_ld trace i c addr rawProgram rawDecode.down.down
  | lbu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lbu trace i c addr rawProgram rawDecode.down.down
  | lhu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lhu trace i c addr rawProgram rawDecode.down.down
  | lwu c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lwu trace i c addr rawProgram rawDecode.down.down
  | lb c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lb trace i c addr rawProgram rawDecode.down.down
  | lh c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lh trace i c addr rawProgram rawDecode.down.down
  | lw c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_lw trace i c addr rawProgram rawDecode.down.down
  | fence c => simpa only [stepProducerRow, Nat.add_sub_cancel_left] using
      sourceWidth_fence trace i c start addr rawProgram rawDecode.down.down

/-- On the old supported placement domain, choosing the source widths from
existing raw evidence computes exactly the old starts and final producer end.
No successful-parser/placement promise is requested from the caller. -/
theorem old_raw_source_widths_and_placement {n rawLength : Nat}
    (trace : AcceptedZiskTrace n) (steps : ∀ i, ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (rawDecodes : ∀ i, RawProgramDecode trace i (steps i) start addr rawProgram)
    (aligned : StepRowsAligned trace steps (fun i => rowDecode_of_programDecode trace i
      (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
        binding (rawDecodes i)))) :
    ∃ selected : Fin n → Fin rawLength,
      ∃ lowering : ∀ i, SuccessfulRowLowering (rawProgram (selected i)),
        (∀ i, addr (selected i) = (mainOfTable trace.program trace.mainTable).pc i.val ∧
          (lowering i).width = legacyWidth steps (fun i => rowDecode_of_programDecode trace i
            (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
              binding (rawDecodes i))) i) ∧
        (∀ i, sourceStart lowering i = i.val) ∧
        (∀ last : Fin n, last.val + 1 = n → sourceEnd lowering =
          stepProducerRow last (steps last) (rowDecode_of_programDecode trace last
            (programDecode_of_rawProgramDecode trace last (steps last) start addr
              rawProgram binding (rawDecodes last))) + 1) := by
  classical
  have h := fun i => sourceWidth_of_rawProgramDecode trace i (steps i) start addr
    rawProgram binding (rawDecodes i)
  let selected (i : Fin n) : Fin rawLength := Classical.choose (h i)
  have hselected (i : Fin n) := Classical.choose_spec (h i)
  let lowering (i : Fin n) : SuccessfulRowLowering (rawProgram (selected i)) :=
    Classical.choose (hselected i).2
  have hwidth (i : Fin n) := Classical.choose_spec (hselected i).2
  have widths : sourceWidth lowering = legacyWidth steps
      (fun i => rowDecode_of_programDecode trace i
        (programDecode_of_rawProgramDecode trace i (steps i) start addr rawProgram
          binding (rawDecodes i))) := by
    funext i
    exact hwidth i
  refine ⟨selected, lowering, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hselected i).1, hwidth i⟩
  · intro i
    unfold sourceStart
    rw [widths]
    exact legacy_start_eq_index steps _ aligned i
  · intro last hfinal
    unfold sourceEnd
    rw [widths]
    exact (legacy_canonical_prefix steps _ aligned last hfinal).1

end ZiskFv.Compliance.RawDecodeRowLowering
