import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.ConstructionLogic
import ZiskFv.Compliance.ConstructionCompare
import ZiskFv.Compliance.ConstructionIType
import ZiskFv.Compliance.ConstructionShift
import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.Compliance.ConstructionWAlu
import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.ConstructionAuipc
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.TraceLevelExport.Base
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl
import ZiskFv.Compliance.TraceLevelExport.EnvOf

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open Interaction

-- The M-extension row-computing defs are reducible/semireducible; structure-field
-- elaboration would otherwise whnf-reduce the full per-row ArithMul/ArithDiv
-- computation (a runaway). `seal` blocks that locally without touching the
-- committed construction proofs (which keep the defs as-is in their oleans).
seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

/-! ## Strengthened control-flow + U-type arms (branches, JAL/JALR, LUI/AUIPC)

These arms reach the same channel-balance conclusion as the 22 above, but via a
DIRECT lift rather than an explicit `OpEnvelope`/global-theorem invocation: the
matching `construction_<op>_sound` already proves the `bus_effect`-form per-step
conclusion over the real trace row, and `state_effect_via_channels` is `@[reducible]`-
defeq to `bus_effect.2`.  Hence `rw [state_effect_via_channels_eq_bus_effect_2]`
followed by the construction theorem yields the EXACT channel-balance proposition
the OLD global theorem produces for these arms (for branches this IS the
`Equivalence.<B>.equiv_<B>` the global dispatcher `zisk_riscv_compliant_program_bus_branch`
itself dispatches to; for LUI/AUIPC/JAL/JALR it is the channel-balance lift of the
same concrete `eRdLui` rd-write entry the `bus_effect`-form arm uses).

Non-vacuity: `execRow` (and `exec_row` for branches) remains a genuine ∀-binder
inside each `RowData_<op>`; no `False.elim`, no contradictory binder; the
conclusion is over the real `mainOfTable` row.  These are strictly stronger than
the corresponding `bus_effect`-form arms (channel-balance form, same data). -/

/-- Strengthened `beq` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.beq` from the trace's `RowData_beq` (the same
    `BranchInstrOperands` + `BranchPromises` `construction_beq_sound` builds) and
    invoke `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_branch`
    conjunct.  `aeneasBridgeTrust` is flat decode pins carried as `RowData_beq`
    residuals; `NoKnownDefect` comes from the threaded `h_known_arm`. -/
theorem stepStrong_beq
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_beq trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .beq .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BEQ)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.beq_input.imm d.beq_input.r1_val d.beq_input.r2_val d.beq_input.PC
      ops.misa_val
      (PureSpec.execute_BEQ_pure d.beq_input).nextPC
      (PureSpec.execute_BEQ_pure d.beq_input).throws
      (PureSpec.execute_BEQ_pure d.beq_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.beq d.beq_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bne` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bne
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_bne trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bne .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BNE)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bne_input.imm d.bne_input.r1_val d.bne_input.r2_val d.bne_input.PC
      ops.misa_val
      (PureSpec.execute_BNE_pure d.bne_input).nextPC
      (PureSpec.execute_BNE_pure d.bne_input).throws
      (PureSpec.execute_BNE_pure d.bne_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bne d.bne_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `blt` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_blt
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_blt trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .blt .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLT)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.blt_input.imm d.blt_input.r1_val d.blt_input.r2_val d.blt_input.PC
      ops.misa_val
      (PureSpec.execute_BLT_pure d.blt_input).nextPC
      (PureSpec.execute_BLT_pure d.blt_input).throws
      (PureSpec.execute_BLT_pure d.blt_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.blt d.blt_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bge` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bge
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_bge trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bge .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGE)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bge_input.imm d.bge_input.r1_val d.bge_input.r2_val d.bge_input.PC
      ops.misa_val
      (PureSpec.execute_BGE_pure d.bge_input).nextPC
      (PureSpec.execute_BGE_pure d.bge_input).throws
      (PureSpec.execute_BGE_pure d.bge_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bge d.bge_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bltu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bltu
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_bltu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bltu .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BLTU)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bltu_input.imm d.bltu_input.r1_val d.bltu_input.r2_val d.bltu_input.PC
      ops.misa_val
      (PureSpec.execute_BLTU_pure d.bltu_input).nextPC
      (PureSpec.execute_BLTU_pure d.bltu_input).throws
      (PureSpec.execute_BLTU_pure d.bltu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bltu d.bltu_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bgeu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bgeu
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_bgeu trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .bgeu .. => True | _ => False)) :
    execute_instruction (instruction.BTYPE (d.imm, d.r2, d.r1, bop.BGEU)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨d.exec_row, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.imm, d.r1, d.r2, d.misa_val, d.exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.bgeu_input.imm d.bgeu_input.r1_val d.bgeu_input.r2_val d.bgeu_input.PC
      ops.misa_val
      (PureSpec.execute_BGEU_pure d.bgeu_input).nextPC
      (PureSpec.execute_BGEU_pure d.bgeu_input).throws
      (PureSpec.execute_BGEU_pure d.bgeu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.h_input_imm
      input_r1_eq := d.h_input_r1
      input_r2_eq := d.h_input_r2
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      not_throws := d.h_not_throws
      success := d.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bgeu d.bgeu_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_main_active, d.h_main_op, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `lui` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.lui` from the trace's `RowData_lui` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_nomem` conjunct.

    The `OpEnvelope.lui` arm's `provenance`/`row_mode` are BUILT from the five
    Main-row mode pins already carried as `RowData_lui` residuals
    (`mainRowProvenance_of_pins` + `luiRowMode_of_extracted_shape`).  This is PATH
    1 (trace-built): the consumed provenance fields reduce to exactly those five
    honest decode residuals, so the conversion adds no trust over the prior
    direct-lift arm.  `aeneasBridgeTrust` is the LUI tuple
    `⟨⟨provenance⟩, row_mode, h_imm_lo_nat, h_imm_hi_nat⟩`; `memoryTimeline`
    trivially; `NoKnownDefect` from the threaded `h_known_arm` (non-defect). -/
theorem stepStrong_lui
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_lui trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .lui .. => True | _ => False)) :
    execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.LUI)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the LUI Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, h_b0, _h_c1, h_b1, _h_set_flag, h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_lui_subset :
      ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_b0, h_b1, h_clear_flag, h_handshake⟩
  -- (b1) provenance + row_mode built from the five decode pins.
  let provenance : ZiskFv.Compliance.MainRowProvenance m i.val :=
    mainRowProvenance_of_pins m i.val ZiskFv.Compliance.ExtractedConst.opCopyB
      false false false false
      (by simpa [ZiskFv.Trusted.OP_COPYB, ZiskFv.Compliance.natF,
        ZiskFv.Compliance.ExtractedConst.opCopyB] using d.h_main_op)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_main_active)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_m32)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_set_pc)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_store_pc)
  let row_mode : ZiskFv.Compliance.MainRowProvenance.LuiRowMode provenance :=
    { op_eq := rfl, internal_eq := rfl, m32_eq := rfl, set_pc_eq := rfl, store_pc_eq := rfl }
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.UTypePromises
      state d.lui_input.imm d.lui_input.rd d.lui_input.PC
      (PureSpec.execute_LUI_pure d.lui_input).nextPC
      d.imm d.rd d.execRow e_rd (d.lui_input.PC + 4#64) :=
    { input_imm_eq := d.h_input_imm
      input_rd_eq := d.h_input_rd
      input_pc_eq := d.h_input_pc
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      nextPC_eq := rfl
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lui d.lui_input d.imm d.rd next_pc d.execRow e_rd store_pc_mem
      provenance row_mode h_lui_subset d.h_imm_lo_nat d.h_imm_hi_nat promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨⟨provenance⟩, row_mode, d.h_imm_lo_nat, d.h_imm_hi_nat⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.1

/-- Strengthened `auipc` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.auipc` from the trace's `RowData_auipc` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_nomem` conjunct.

    Same PATH-1 provenance construction as `stepStrong_lui`: the AUIPC
    `provenance`/`row_mode` are BUILT from the five mode pins
    (`mainRowProvenance_of_pins` + `auipcRowMode_of_extracted_shape`-shape record).
    `aeneasBridgeTrust` is the AUIPC tuple
    `⟨⟨provenance⟩, row_mode, h_offset_bridge, h_pc_bridge⟩`; `NoKnownDefect` from
    the threaded `h_known_arm` (non-defect). -/
theorem stepStrong_auipc
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_auipc trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .auipc .. => True | _ => False)) :
    execute_instruction (instruction.UTYPE (d.imm, d.rd, uop.AUIPC)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the AUIPC Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨h_c0, _h_b0, h_c1, _h_b1, h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_auipc_subset :
      ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0, h_c1, h_set_flag, h_handshake⟩
  -- (b1) provenance + row_mode built from the five decode pins.
  let provenance : ZiskFv.Compliance.MainRowProvenance m i.val :=
    mainRowProvenance_of_pins m i.val ZiskFv.Compliance.ExtractedConst.opFlag
      false false false true
      (by simpa [ZiskFv.Trusted.OP_FLAG, ZiskFv.Compliance.natF,
        ZiskFv.Compliance.ExtractedConst.opFlag] using d.h_main_op)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_main_active)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_m32)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_set_pc)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_store_pc)
  let row_mode : ZiskFv.Compliance.MainRowProvenance.AuipcRowMode provenance :=
    { op_eq := rfl, internal_eq := rfl, m32_eq := rfl, set_pc_eq := rfl, store_pc_eq := rfl }
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.UTypePromises
      state d.auipc_input.imm d.auipc_input.rd d.auipc_input.PC
      (PureSpec.execute_AUIPC_pure d.auipc_input).nextPC
      d.imm d.rd d.execRow e_rd (PureSpec.execute_AUIPC_pure d.auipc_input).nextPC :=
    { input_imm_eq := d.h_input_imm
      input_rd_eq := d.h_input_rd
      input_pc_eq := d.h_input_pc
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      nextPC_eq := rfl
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.auipc d.auipc_input d.imm d.rd d.execRow e_rd
      (PureSpec.execute_AUIPC_pure d.auipc_input).nextPC next_pc store_pc_mem
      provenance row_mode h_auipc_subset d.h_offset_bridge d.h_pc_bridge promises
      d.h_no_wrap d.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨⟨provenance⟩, row_mode, d.h_offset_bridge, d.h_pc_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.1

/-- Strengthened `jal` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.jal` from the trace's `RowData_jal` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.

    Same PATH-1 provenance construction as `stepStrong_lui`/`stepStrong_auipc`:
    the JAL `provenance`/`row_mode` are BUILT from the five mode pins
    (`mainRowProvenance_of_pins`).  `aeneasBridgeTrust` is the JAL tuple
    `⟨⟨provenance⟩, row_mode, h_jmp2, h_pc_bridge⟩`; `NoKnownDefect` from the
    threaded `h_known_arm` (non-defect). -/
theorem stepStrong_jal
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_jal trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .jal .. => True | _ => False)) :
    execute_instruction (instruction.JAL (d.imm, d.rd)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the JAL Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨h_c0, _h_b0, h_c1, _h_b1, h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0, h_c1, h_set_flag, h_handshake⟩
  -- (b1) provenance + row_mode built from the five decode pins.
  let provenance : ZiskFv.Compliance.MainRowProvenance m i.val :=
    mainRowProvenance_of_pins m i.val ZiskFv.Compliance.ExtractedConst.opFlag
      false false false true
      (by simpa [ZiskFv.Trusted.OP_FLAG, ZiskFv.Compliance.natF,
        ZiskFv.Compliance.ExtractedConst.opFlag] using d.h_main_op)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_main_active)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_m32)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_set_pc)
      (by simpa [ZiskFv.Compliance.boolF] using d.h_store_pc)
  let row_mode : ZiskFv.Compliance.MainRowProvenance.JalRowMode provenance :=
    { op_eq := rfl, internal_eq := rfl, m32_eq := rfl, set_pc_eq := rfl, store_pc_eq := rfl }
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state d.jal_input.PC d.jal_input.rd d.misa_val
      (PureSpec.execute_JAL_pure d.jal_input).success
      (PureSpec.execute_JAL_pure d.jal_input).nextPC
      d.rd d.execRow e_rd d.nextPC_val :=
    { input_rd_eq := d.h_input_rd
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      success := d.h_success
      nextPC_option := d.h_nextPC_option
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.jal d.jal_input d.imm d.rd d.misa_val next_pc d.execRow e_rd
      d.nextPC_val store_pc_mem provenance row_mode h_jal_subset d.h_jmp2 d.h_pc_bridge
      promises d.h_input_imm d.h_not_throws d.h_pc_bound d.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨⟨provenance⟩, row_mode, d.h_jmp2, d.h_pc_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `jalr` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.jalr` from the trace's `RowData_jalr` (mirroring
    `construction_jalr_sound`'s internal `next_pc` / `e_rd` / `store_pc_mem` /
    `pins` / `h_jalr_subset` / `promises` derivations) and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.  The threaded `h_known_arm : EnvNoKnownDefectFor …` discharges
    `NoKnownDefect`.  JALR's `aeneasBridgeTrust` is flat decode pins already in
    `RowData_jalr` (no `MainRowProvenance`). -/
theorem stepStrong_jalr
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_jalr trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .jalr .. => True | _ => False)) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.JALR (d.imm, d.rs1, d.rd))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.execRow, [eRdLui trace binding i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the JALR Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, _h_b0, _h_c1, _h_b1, _h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m i.val
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m i.val
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m i.val
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_handshake⟩
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.h_main_active, d.h_main_op⟩
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state d.jalr_input.PC d.jalr_input.rd d.misa_val
      (PureSpec.execute_JALR_pure d.jalr_input).success
      (PureSpec.execute_JALR_pure d.jalr_input).nextPC
      d.rd d.execRow e_rd d.nextPC_val :=
    { input_rd_eq := d.h_input_rd
      input_pc_eq := d.h_input_pc
      input_misa_eq := d.h_input_misa
      misa_c_zero := d.h_misa_c
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      success := d.h_success
      nextPC_option := d.h_nextPC_option
      rd_idx := d.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.jalr d.jalr_input d.imm d.rs1 d.rd d.misa_val d.mseccfg d.execRow e_rd
      d.nextPC_val next_pc store_pc_mem pins d.h_flag d.h_m32 d.h_set_pc d.h_store_pc
      h_jalr_subset promises d.h_input_imm d.h_input_rs1 d.h_cur_privilege d.h_mseccfg
      d.h_link_bridge d.h_pc_bound d.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.h_flag, d.h_m32, d.h_set_pc, d.h_store_pc, d.h_link_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-! ## Strengthened store arms (SB/SH/SW/SD, channel-balance form) — OpEnvelope route

CONVERTED from the direct-lift route to the OpEnvelope route: each arm CONSTRUCTS
`OpEnvelope.<store>` from the trace's committed Main row and invokes
`zisk_riscv_compliant_program_bus`, projecting `exec_eq_remaining` (the 12th
conjunct).

The store `OpEnvelope.<store>` constructor carries `{mainRowVar : Var
MainRowWithRom}` / `{mainEnv : Environment}` implicit binders whose `eval mainEnv
mainRowVar` appears in five hypotheses (`h_main_row`/`h_main_spec`/`h_store_pc`/
`h_main_c_match`/`h_addr2`).  We instantiate `mainRowVar := mainConstVar
(mainRowWithRomSt …)` and `mainEnv := emptyEnv`; by `eval_mainConstVar` this
`eval` reduces to the concrete trace row `mainRowWithRomSt trace binding i`, so the
five hypotheses become exactly the facts `construction_<store>_sound` already
proves (Spec at the row, `store_pc = 0`, the self-referential `c`-emission match,
the `addr2` bridge).  This `mainConstVar`-of-the-real-row pattern is the analogue
of the M-ext/control "placeholder-env + real row" build and sidesteps the prior
whnf BLOWUP (the `Eq.mpr` cast over a free `MainRowWithRom` motive) because the row
is a `.const` literal of the committed trace row, not an opaque eval-binder.

Non-vacuous: `execRow` is a genuine ∀-binder; the `c`-emission match is
`matches_memory_entry_refl` over the real `busSt` row; the high-byte RMW residuals
(`h_m*`, the #76 sub-doubleword preservation reads) are carried verbatim as
`RowData_<store>` binders, NOT laundered. -/

/-- Empty environment used only to instantiate the store `OpEnvelope` arms'
    `{mainEnv}` implicit binder; `eval_mainConstVar` makes the choice irrelevant. -/
private def emptyMainEnv : Environment FGL :=
  { get := fun _ => 0, data := fun _ _ => #[] }

/-- Strengthened `sb` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sb
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_sb trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sb .. => True | _ => False)) :
    execute_instruction (instruction.STORE
        (d.sb_input.imm, regidx.Regidx d.sb_input.r2, regidx.Regidx d.sb_input.r1, 1))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace binding i d.execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.sb_input.r2_val := d.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.sb_input.r2_val := d.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.regs.mstatus d.regs.pmaRegion d.regs.misa d.regs.mseccfg
      (PureSpec.sb_state_assumptions d.sb_input state)
      (PureSpec.execute_STOREB_pure d.sb_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.h_risc_v_assumptions
      opcode_assumptions_ := d.h_opcode_assumptions
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sb d.sb_input d.regs bus pins d.h_main_ind_width d.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace binding i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.h_addr2)
      h_b0' h_b1' d.h_m1 d.h_m2 d.h_m3 d.h_m4 d.h_m5 d.h_m6 d.h_m7
  have h_bridge : env.aeneasBridgeTrust := ⟨d.h_main_ind_width, h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sh` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sh
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_sh trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sh .. => True | _ => False)) :
    execute_instruction (instruction.STORE
        (d.sh_input.imm, regidx.Regidx d.sh_input.r2, regidx.Regidx d.sh_input.r1, 2))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace binding i d.execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.sh_input.r2_val := d.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.sh_input.r2_val := d.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.regs.mstatus d.regs.pmaRegion d.regs.misa d.regs.mseccfg
      (PureSpec.sh_state_assumptions d.sh_input state)
      (PureSpec.execute_STOREH_pure d.sh_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.h_risc_v_assumptions
      opcode_assumptions_ := d.h_opcode_assumptions
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sh d.sh_input d.regs bus pins d.h_main_ind_width d.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace binding i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.h_addr2)
      h_b0' h_b1' d.h_m2 d.h_m3 d.h_m4 d.h_m5 d.h_m6 d.h_m7
  have h_bridge : env.aeneasBridgeTrust := ⟨d.h_main_ind_width, h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sw` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sw
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_sw trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sw .. => True | _ => False)) :
    execute_instruction (instruction.STORE
        (d.sw_input.imm, regidx.Regidx d.sw_input.r2, regidx.Regidx d.sw_input.r1, 4))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace binding i d.execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.sw_input.r2_val := d.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.sw_input.r2_val := d.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.regs.mstatus d.regs.pmaRegion d.regs.misa d.regs.mseccfg
      (PureSpec.sw_state_assumptions d.sw_input state)
      (PureSpec.execute_STOREW_pure d.sw_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.h_risc_v_assumptions
      opcode_assumptions_ := d.h_opcode_assumptions
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sw d.sw_input d.regs bus pins d.h_main_ind_width d.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace binding i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.h_addr2)
      h_b0' h_b1' d.h_m4 d.h_m5 d.h_m6 d.h_m7
  have h_bridge : env.aeneasBridgeTrust := ⟨d.h_main_ind_width, h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sd` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sd
    (trace : AcceptedZiskTrace) (binding : SailTrace trace) (i : Fin trace.numInstructions)
    (d : RowData_sd trace binding i)
    (h_known_arm : EnvNoKnownDefectFor
      (state := binding i)
      (m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      (r := i.val) (fun env => match env with | .sd .. => True | _ => False)) :
    execute_instruction (instruction.STORE
        (d.sd_input.imm, regidx.Regidx d.sd_input.r2, regidx.Regidx d.sd_input.r1, 8))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace binding i d.execRow).exec_row,
           [ (busSt trace binding i d.execRow).e0
           , (busSt trace binding i d.execRow).e1
           , (busSt trace binding i d.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace binding i d.execRow
  have h_core : (mainRowWithRomSt trace binding i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace binding i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace binding i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.h_main_active, d.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace binding i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.sd_input.r2_val := d.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.sd_input.r2_val := d.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.regs.mstatus d.regs.pmaRegion d.regs.misa d.regs.mseccfg
      (PureSpec.sd_state_assumptions d.sd_input state)
      (PureSpec.execute_STORED_pure d.sd_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.h_risc_v_assumptions
      opcode_assumptions_ := d.h_opcode_assumptions
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sd d.sd_input d.regs bus pins d.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace binding i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.h_addr2)
      h_b0' h_b1'
  have h_bridge : env.aeneasBridgeTrust := ⟨h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := h_known_arm env trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.1


end ZiskFv.Compliance
