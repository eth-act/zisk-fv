import ZiskFv.Compliance.TraceLevelExport.Dispatcher
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingImmediate
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingLoadStore
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingControl
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingCopyb
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingMext

/-!
# Raw-program row-decode dispatch (issue #159, BLOCK 3 WIRING)

This module is the additive bridge that makes `root_soundness`'s `rowDecodes`
hypothesis **derivable from the raw RISC-V program**, rather than caller-asserted.

`RowDecode ziskTrace i zs` (block 1) is the per-op `Decode_<op> ziskTrace i c`
type: it carries the ROM-backed decode-column pins (op / flags / jmp / ind_width)
as *assumed* equalities on the committed `trace.program`.  Block 3's per-op
`Decode_<op>_from_rawProgram` bridges (the 63-op sweep) instead **derive** those
columns from `rawProgram` through the real Aeneas transpile pipeline
(decode #164 → lower #111/block 2 → serialize), consuming only the single
op-shaped raw-word fact `hLine`, the index bound `h_idx`, and the SAME non-ROM
operand witnesses block 1 already carried.

`RawRowDecode ziskTrace i rawProgram zs` mirrors `RowDecode` but dispatches to the
per-op bundle `RawDecode_<op>` packaging exactly those thinner per-op hypotheses
(everything `Decode_<op>_from_rawProgram` needs EXCEPT the op-agnostic, shared
`rawProgram` / `ProgramBinding`).  `rowDecode_of_rawRowDecode` consumes the shared
`ProgramBinding` certificate once and rebuilds `RowDecode` per row;
`rowDecodes_of_rawProgram` lifts it over all instructions.  The headline endpoint
`root_soundness_rawProgram` (in `ZiskFv/Soundness.lean`) feeds the result to
`root_soundness` unchanged.

Sound: NO `sorry` / new axiom / `native_decide`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).
-/

namespace ZiskFv.Compliance

set_option maxHeartbeats 1600000

/-- Per-op raw-decode bundle, dispatched on the row's `ZiskStep`.  Each arm is the
    per-op `RawDecode_<op>` record: the genuinely THINNER per-op hypotheses each
    `Decode_<op>_from_rawProgram` needs — `h_idx`, the op-shaped raw-word fact
    `hLine`, and the unchanged non-ROM operand witnesses — EXCEPT the op-agnostic
    shared `rawProgram` (threaded here as a parameter) and `ProgramBinding` (the
    shared certificate, supplied once to `rowDecode_of_rawRowDecode`).  The
    ROM-backed decode columns that `RowDecode`/`Decode_<op>` *assume* are absent
    here: they become DERIVED. -/
def RawRowDecode (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    (rawProgram : Fin numInstructions → BitVec 32) : ZiskStep ziskTrace i → Type
  | .sub c => RawProgramBinding.RawDecode_sub ziskTrace i c rawProgram
  | .and c => RawProgramBinding.RawDecode_and ziskTrace i c rawProgram
  | .or c => RawProgramBinding.RawDecode_or ziskTrace i c rawProgram
  | .xor c => RawProgramBinding.RawDecode_xor ziskTrace i c rawProgram
  | .slt c => RawProgramBinding.RawDecode_slt ziskTrace i c rawProgram
  | .sltu c => RawProgramBinding.RawDecode_sltu ziskTrace i c rawProgram
  | .andi c => RawProgramBinding.RawDecode_andi ziskTrace i c rawProgram
  | .ori c => RawProgramBinding.RawDecode_ori ziskTrace i c rawProgram
  | .xori c => RawProgramBinding.RawDecode_xori ziskTrace i c rawProgram
  | .slti c => RawProgramBinding.RawDecode_slti ziskTrace i c rawProgram
  | .sltiu c => RawProgramBinding.RawDecode_sltiu ziskTrace i c rawProgram
  | .sll c => RawProgramBinding.RawDecode_sll ziskTrace i c rawProgram
  | .srl c => RawProgramBinding.RawDecode_srl ziskTrace i c rawProgram
  | .sra c => RawProgramBinding.RawDecode_sra ziskTrace i c rawProgram
  | .slli c => RawProgramBinding.RawDecode_slli ziskTrace i c rawProgram
  | .srli c => RawProgramBinding.RawDecode_srli ziskTrace i c rawProgram
  | .srai c => RawProgramBinding.RawDecode_srai ziskTrace i c rawProgram
  | .add c => RawProgramBinding.RawDecode_add ziskTrace i c rawProgram
  | .addi c => RawProgramBinding.RawDecode_addi ziskTrace i c rawProgram
  | .subw c => RawProgramBinding.RawDecode_subw ziskTrace i c rawProgram
  | .addw c => RawProgramBinding.RawDecode_addw ziskTrace i c rawProgram
  | .addiw c => RawProgramBinding.RawDecode_addiw ziskTrace i c rawProgram
  | .sllw c => RawProgramBinding.RawDecode_sllw ziskTrace i c rawProgram
  | .srlw c => RawProgramBinding.RawDecode_srlw ziskTrace i c rawProgram
  | .sraw c => RawProgramBinding.RawDecode_sraw ziskTrace i c rawProgram
  | .slliw c => RawProgramBinding.RawDecode_slliw ziskTrace i c rawProgram
  | .srliw c => RawProgramBinding.RawDecode_srliw ziskTrace i c rawProgram
  | .sraiw c => RawProgramBinding.RawDecode_sraiw ziskTrace i c rawProgram
  | .mul c => RawProgramBinding.RawDecode_mul ziskTrace i c rawProgram
  | .mulh c => RawProgramBinding.RawDecode_mulh ziskTrace i c rawProgram
  | .mulhsu c => RawProgramBinding.RawDecode_mulhsu ziskTrace i c rawProgram
  | .mulw c => RawProgramBinding.RawDecode_mulw ziskTrace i c rawProgram
  | .mulhu c => RawProgramBinding.RawDecode_mulhu ziskTrace i c rawProgram
  | .div c => RawProgramBinding.RawDecode_div ziskTrace i c rawProgram
  | .rem c => RawProgramBinding.RawDecode_rem ziskTrace i c rawProgram
  | .divw c => RawProgramBinding.RawDecode_divw ziskTrace i c rawProgram
  | .remw c => RawProgramBinding.RawDecode_remw ziskTrace i c rawProgram
  | .divu c => RawProgramBinding.RawDecode_divu ziskTrace i c rawProgram
  | .divuw c => RawProgramBinding.RawDecode_divuw ziskTrace i c rawProgram
  | .remu c => RawProgramBinding.RawDecode_remu ziskTrace i c rawProgram
  | .remuw c => RawProgramBinding.RawDecode_remuw ziskTrace i c rawProgram
  | .beq c => RawProgramBinding.RawDecode_beq ziskTrace i c rawProgram
  | .bne c => RawProgramBinding.RawDecode_bne ziskTrace i c rawProgram
  | .blt c => RawProgramBinding.RawDecode_blt ziskTrace i c rawProgram
  | .bge c => RawProgramBinding.RawDecode_bge ziskTrace i c rawProgram
  | .bltu c => RawProgramBinding.RawDecode_bltu ziskTrace i c rawProgram
  | .bgeu c => RawProgramBinding.RawDecode_bgeu ziskTrace i c rawProgram
  | .lui c => RawProgramBinding.RawDecode_lui ziskTrace i c rawProgram
  | .auipc c => RawProgramBinding.RawDecode_auipc ziskTrace i c rawProgram
  | .jal c => RawProgramBinding.RawDecode_jal ziskTrace i c rawProgram
  | .jalr c => RawProgramBinding.RawDecode_jalr ziskTrace i c rawProgram
  | .sb c => RawProgramBinding.RawDecode_sb ziskTrace i c rawProgram
  | .sh c => RawProgramBinding.RawDecode_sh ziskTrace i c rawProgram
  | .sw c => RawProgramBinding.RawDecode_sw ziskTrace i c rawProgram
  | .sd c => RawProgramBinding.RawDecode_sd ziskTrace i c rawProgram
  | .ld c => RawProgramBinding.RawDecode_ld ziskTrace i c rawProgram
  | .lbu c => RawProgramBinding.RawDecode_lbu ziskTrace i c rawProgram
  | .lhu c => RawProgramBinding.RawDecode_lhu ziskTrace i c rawProgram
  | .lwu c => RawProgramBinding.RawDecode_lwu ziskTrace i c rawProgram
  | .lb c => RawProgramBinding.RawDecode_lb ziskTrace i c rawProgram
  | .lh c => RawProgramBinding.RawDecode_lh ziskTrace i c rawProgram
  | .lw c => RawProgramBinding.RawDecode_lw ziskTrace i c rawProgram
  | .fence c => RawProgramBinding.RawDecode_fence ziskTrace i c rawProgram

/-- Rebuild block 1's `RowDecode` for one row from its thinner `RawRowDecode`
    bundle plus the shared op-agnostic `ProgramBinding` certificate, by applying
    the matching per-op `Decode_<op>_from_rawProgram_b` bridge. -/
noncomputable def rowDecode_of_rawRowDecode (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    (rawProgram : Fin numInstructions → BitVec 32)
    (hbind : RawProgramBinding.ProgramBinding ziskTrace rawProgram)
    {zs : ZiskStep ziskTrace i}
    (b : RawRowDecode ziskTrace i rawProgram zs) : RowDecode ziskTrace i zs := by
  cases zs with
  | sub c => exact RawProgramBinding.Decode_sub_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | and c => exact RawProgramBinding.Decode_and_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | or c => exact RawProgramBinding.Decode_or_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | xor c => exact RawProgramBinding.Decode_xor_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | slt c => exact RawProgramBinding.Decode_slt_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sltu c => exact RawProgramBinding.Decode_sltu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | andi c => exact RawProgramBinding.Decode_andi_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | ori c => exact RawProgramBinding.Decode_ori_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | xori c => exact RawProgramBinding.Decode_xori_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | slti c => exact RawProgramBinding.Decode_slti_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sltiu c => exact RawProgramBinding.Decode_sltiu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sll c => exact RawProgramBinding.Decode_sll_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | srl c => exact RawProgramBinding.Decode_srl_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sra c => exact RawProgramBinding.Decode_sra_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | slli c => exact RawProgramBinding.Decode_slli_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | srli c => exact RawProgramBinding.Decode_srli_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | srai c => exact RawProgramBinding.Decode_srai_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | add c => exact RawProgramBinding.Decode_add_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | addi c => exact RawProgramBinding.Decode_addi_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | subw c => exact RawProgramBinding.Decode_subw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | addw c => exact RawProgramBinding.Decode_addw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | addiw c => exact RawProgramBinding.Decode_addiw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sllw c => exact RawProgramBinding.Decode_sllw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | srlw c => exact RawProgramBinding.Decode_srlw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sraw c => exact RawProgramBinding.Decode_sraw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | slliw c => exact RawProgramBinding.Decode_slliw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | srliw c => exact RawProgramBinding.Decode_srliw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sraiw c => exact RawProgramBinding.Decode_sraiw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | mul c => exact RawProgramBinding.Decode_mul_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | mulh c => exact RawProgramBinding.Decode_mulh_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | mulhsu c => exact RawProgramBinding.Decode_mulhsu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | mulw c => exact RawProgramBinding.Decode_mulw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | mulhu c => exact RawProgramBinding.Decode_mulhu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | div c => exact RawProgramBinding.Decode_div_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | rem c => exact RawProgramBinding.Decode_rem_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | divw c => exact RawProgramBinding.Decode_divw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | remw c => exact RawProgramBinding.Decode_remw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | divu c => exact RawProgramBinding.Decode_divu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | divuw c => exact RawProgramBinding.Decode_divuw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | remu c => exact RawProgramBinding.Decode_remu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | remuw c => exact RawProgramBinding.Decode_remuw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | beq c => exact RawProgramBinding.Decode_beq_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | bne c => exact RawProgramBinding.Decode_bne_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | blt c => exact RawProgramBinding.Decode_blt_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | bge c => exact RawProgramBinding.Decode_bge_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | bltu c => exact RawProgramBinding.Decode_bltu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | bgeu c => exact RawProgramBinding.Decode_bgeu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lui c => exact RawProgramBinding.Decode_lui_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | auipc c => exact RawProgramBinding.Decode_auipc_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | jal c => exact RawProgramBinding.Decode_jal_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | jalr c => exact RawProgramBinding.Decode_jalr_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sb c => exact RawProgramBinding.Decode_sb_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sh c => exact RawProgramBinding.Decode_sh_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sw c => exact RawProgramBinding.Decode_sw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | sd c => exact RawProgramBinding.Decode_sd_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | ld c => exact RawProgramBinding.Decode_ld_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lbu c => exact RawProgramBinding.Decode_lbu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lhu c => exact RawProgramBinding.Decode_lhu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lwu c => exact RawProgramBinding.Decode_lwu_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lb c => exact RawProgramBinding.Decode_lb_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lh c => exact RawProgramBinding.Decode_lh_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | lw c => exact RawProgramBinding.Decode_lw_from_rawProgram_b ziskTrace i c rawProgram hbind b
  | fence c => exact RawProgramBinding.Decode_fence_from_rawProgram_b ziskTrace i c rawProgram hbind b

/-- Lift `rowDecode_of_rawRowDecode` over every instruction: given the shared
    `rawProgram` + `ProgramBinding` and a per-row `RawRowDecode`, produce the
    full `rowDecodes` family `root_soundness` consumes. -/
noncomputable def rowDecodes_of_rawProgram (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin numInstructions, ZiskStep ziskTrace i)
    (rawProgram : Fin numInstructions → BitVec 32)
    (hbind : RawProgramBinding.ProgramBinding ziskTrace rawProgram)
    (rawRowDecodes : ∀ i : Fin numInstructions, RawRowDecode ziskTrace i rawProgram (ziskStep i)) :
    ∀ i : Fin numInstructions, RowDecode ziskTrace i (ziskStep i) :=
  fun i => rowDecode_of_rawRowDecode ziskTrace i rawProgram hbind (rawRowDecodes i)

end ZiskFv.Compliance
