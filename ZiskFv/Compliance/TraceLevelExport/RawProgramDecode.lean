import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingImmediate
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingCopyb
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingMext
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingLoadStore
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingControl
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingJalr

namespace ZiskFv.Compliance

open RawProgramBinding

/-- Raw-word evidence for the production lowering of the opcode selected by one
    execution step. Control-flow evidence also sees the architectural-to-physical
    start map because those constructors state their lookup directly. -/
def RawProgramDecode {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (zs : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) : Type 1 :=
  match zs with
  | .sub c => ULift.{1} (PLift (RawProgramDecode_sub trace i c addr rawProgram))
  | .and c => ULift.{1} (PLift (RawProgramDecode_and trace i c addr rawProgram))
  | .or c => ULift.{1} (PLift (RawProgramDecode_or trace i c addr rawProgram))
  | .xor c => ULift.{1} (PLift (RawProgramDecode_xor trace i c addr rawProgram))
  | .slt c => ULift.{1} (PLift (RawProgramDecode_slt trace i c addr rawProgram))
  | .sltu c => ULift.{1} (PLift (RawProgramDecode_sltu trace i c addr rawProgram))
  | .andi c => ULift.{1} (PLift (RawProgramDecode_andi trace i c addr rawProgram))
  | .ori c => ULift.{1} (PLift (RawProgramDecode_ori trace i c addr rawProgram))
  | .xori c => ULift.{1} (PLift (RawProgramDecode_xori trace i c addr rawProgram))
  | .slti c => ULift.{1} (PLift (RawProgramDecode_slti trace i c addr rawProgram))
  | .sltiu c => ULift.{1} (PLift (RawProgramDecode_sltiu trace i c addr rawProgram))
  | .sll c => ULift.{1} (PLift (RawProgramDecode_sll trace i c addr rawProgram))
  | .srl c => ULift.{1} (PLift (RawProgramDecode_srl trace i c addr rawProgram))
  | .sra c => ULift.{1} (PLift (RawProgramDecode_sra trace i c addr rawProgram))
  | .slli c => ULift.{1} (PLift (RawProgramDecode_slli trace i c addr rawProgram))
  | .srli c => ULift.{1} (PLift (RawProgramDecode_srli trace i c addr rawProgram))
  | .srai c => ULift.{1} (PLift (RawProgramDecode_srai trace i c addr rawProgram))
  | .add c => ULift.{1} (PLift (RawProgramDecode_add trace i c addr rawProgram))
  | .addi c => ULift.{1} (PLift (RawProgramDecode_addi trace i c addr rawProgram))
  | .subw c => ULift.{1} (PLift (RawProgramDecode_subw trace i c addr rawProgram))
  | .addw c => ULift.{1} (PLift (RawProgramDecode_addw trace i c addr rawProgram))
  | .addiw c => ULift.{1} (PLift (RawProgramDecode_addiw trace i c addr rawProgram))
  | .sllw c => ULift.{1} (PLift (RawProgramDecode_sllw trace i c addr rawProgram))
  | .srlw c => ULift.{1} (PLift (RawProgramDecode_srlw trace i c addr rawProgram))
  | .sraw c => ULift.{1} (PLift (RawProgramDecode_sraw trace i c addr rawProgram))
  | .slliw c => ULift.{1} (PLift (RawProgramDecode_slliw trace i c addr rawProgram))
  | .srliw c => ULift.{1} (PLift (RawProgramDecode_srliw trace i c addr rawProgram))
  | .sraiw c => ULift.{1} (PLift (RawProgramDecode_sraiw trace i c addr rawProgram))
  | .mul c => ULift.{1} (PLift (RawProgramDecode_mul trace i c addr rawProgram))
  | .mulh c => ULift.{1} (PLift (RawProgramDecode_mulh trace i c addr rawProgram))
  | .mulhsu c => ULift.{1} (PLift (RawProgramDecode_mulhsu trace i c addr rawProgram))
  | .mulw c => ULift.{1} (PLift (RawProgramDecode_mulw trace i c addr rawProgram))
  | .mulhu c => ULift.{1} (PLift (RawProgramDecode_mulhu trace i c addr rawProgram))
  | .div c => ULift.{1} (PLift (RawProgramDecode_div trace i c addr rawProgram))
  | .rem c => ULift.{1} (PLift (RawProgramDecode_rem trace i c addr rawProgram))
  | .divw c => ULift.{1} (PLift (RawProgramDecode_divw trace i c addr rawProgram))
  | .remw c => ULift.{1} (PLift (RawProgramDecode_remw trace i c addr rawProgram))
  | .divu c => ULift.{1} (PLift (RawProgramDecode_divu trace i c addr rawProgram))
  | .divuw c => ULift.{1} (PLift (RawProgramDecode_divuw trace i c addr rawProgram))
  | .remu c => ULift.{1} (PLift (RawProgramDecode_remu trace i c addr rawProgram))
  | .remuw c => ULift.{1} (PLift (RawProgramDecode_remuw trace i c addr rawProgram))
  | .beq c => ULift.{1} (PLift (RawProgramDecode_beq trace i c start addr rawProgram))
  | .bne c => ULift.{1} (PLift (RawProgramDecode_bne trace i c start addr rawProgram))
  | .blt c => ULift.{1} (PLift (RawProgramDecode_blt trace i c start addr rawProgram))
  | .bge c => ULift.{1} (PLift (RawProgramDecode_bge trace i c start addr rawProgram))
  | .bltu c => ULift.{1} (PLift (RawProgramDecode_bltu trace i c start addr rawProgram))
  | .bgeu c => ULift.{1} (PLift (RawProgramDecode_bgeu trace i c start addr rawProgram))
  | .lui c => ULift.{1} (PLift (RawProgramDecode_lui trace i c start addr rawProgram))
  | .auipc c => ULift.{1} (PLift (RawProgramDecode_auipc trace i c start addr rawProgram))
  | .jal c => ULift.{1} (PLift (RawProgramDecode_jal trace i c start addr rawProgram))
  | .jalr c => ULift.{1} (PLift (RawProgramDecode_jalr trace i c start addr rawProgram))
  | .sb c => ULift.{1} (PLift (RawProgramDecode_sb trace i c addr rawProgram))
  | .sh c => ULift.{1} (PLift (RawProgramDecode_sh trace i c addr rawProgram))
  | .sw c => ULift.{1} (PLift (RawProgramDecode_sw trace i c addr rawProgram))
  | .sd c => ULift.{1} (PLift (RawProgramDecode_sd trace i c addr rawProgram))
  | .ld c => ULift.{1} (PLift (RawProgramDecode_ld trace i c addr rawProgram))
  | .lbu c => ULift.{1} (PLift (RawProgramDecode_lbu trace i c addr rawProgram))
  | .lhu c => ULift.{1} (PLift (RawProgramDecode_lhu trace i c addr rawProgram))
  | .lwu c => ULift.{1} (PLift (RawProgramDecode_lwu trace i c addr rawProgram))
  | .lb c => ULift.{1} (PLift (RawProgramDecode_lb trace i c addr rawProgram))
  | .lh c => ULift.{1} (PLift (RawProgramDecode_lh trace i c addr rawProgram))
  | .lw c => ULift.{1} (PLift (RawProgramDecode_lw trace i c addr rawProgram))
  | .fence c => ULift.{1} (PLift (RawProgramDecode_fence trace i c start addr rawProgram))

/-- Construct the committed-program decode bundle directly from raw-word
    evidence and the single production-lowering certificate. -/
noncomputable def programDecode_of_rawProgramDecode {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (zs : ZiskStep trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode trace i zs start addr rawProgram) :
    ProgramDecode trace i zs := by
  cases zs with
  | sub c => exact ProgramDecode_sub_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | and c => exact ProgramDecode_and_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | or c => exact ProgramDecode_or_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | xor c => exact ProgramDecode_xor_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | slt c => exact ProgramDecode_slt_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sltu c => exact ProgramDecode_sltu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | andi c => exact ProgramDecode_andi_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | ori c => exact ProgramDecode_ori_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | xori c => exact ProgramDecode_xori_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | slti c => exact ProgramDecode_slti_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sltiu c => exact ProgramDecode_sltiu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sll c => exact ProgramDecode_sll_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | srl c => exact ProgramDecode_srl_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sra c => exact ProgramDecode_sra_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | slli c => exact ProgramDecode_slli_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | srli c => exact ProgramDecode_srli_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | srai c => exact ProgramDecode_srai_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | add c => exact ProgramDecode_add_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | addi c => exact ProgramDecode_addi_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | subw c => exact ProgramDecode_subw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | addw c => exact ProgramDecode_addw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | addiw c => exact ProgramDecode_addiw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sllw c => exact ProgramDecode_sllw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | srlw c => exact ProgramDecode_srlw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sraw c => exact ProgramDecode_sraw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | slliw c => exact ProgramDecode_slliw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | srliw c => exact ProgramDecode_srliw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sraiw c => exact ProgramDecode_sraiw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | mul c => exact ProgramDecode_mul_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | mulh c => exact ProgramDecode_mulh_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | mulhsu c => exact ProgramDecode_mulhsu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | mulw c => exact ProgramDecode_mulw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | mulhu c => exact ProgramDecode_mulhu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | div c => exact ProgramDecode_div_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | rem c => exact ProgramDecode_rem_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | divw c => exact ProgramDecode_divw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | remw c => exact ProgramDecode_remw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | divu c => exact ProgramDecode_divu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | divuw c => exact ProgramDecode_divuw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | remu c => exact ProgramDecode_remu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | remuw c => exact ProgramDecode_remuw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | beq c => exact ProgramDecode_beq_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | bne c => exact ProgramDecode_bne_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | blt c => exact ProgramDecode_blt_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | bge c => exact ProgramDecode_bge_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | bltu c => exact ProgramDecode_bltu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | bgeu c => exact ProgramDecode_bgeu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lui c => exact ProgramDecode_lui_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | auipc c => exact ProgramDecode_auipc_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | jal c => exact ProgramDecode_jal_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | jalr c => exact ProgramDecode_jalr_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sb c => exact ProgramDecode_sb_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sh c => exact ProgramDecode_sh_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sw c => exact ProgramDecode_sw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | sd c => exact ProgramDecode_sd_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | ld c => exact ProgramDecode_ld_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lbu c => exact ProgramDecode_lbu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lhu c => exact ProgramDecode_lhu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lwu c => exact ProgramDecode_lwu_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lb c => exact ProgramDecode_lb_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lh c => exact ProgramDecode_lh_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | lw c => exact ProgramDecode_lw_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down
  | fence c => exact ProgramDecode_fence_from_rawProgram trace i c start addr rawProgram hbind rawDecode.down.down

end ZiskFv.Compliance
