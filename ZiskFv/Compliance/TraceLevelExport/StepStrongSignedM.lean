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

/-- Strengthened `mul` step (channel-balance form), via the OpEnvelope route.

    MUL is the signed low-half multiply (op `180`), a former defect-gated op now
    landed on the OpEnvelope route.  CONSTRUCT `OpEnvelope.mul` (= the shared
    `mulEnvOf`) from the trace's `RowData_mul` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining` conjunct.
    `aeneasBridgeTrust` is the 7-tuple of Main decode pins; the memory-timeline
    obligation is trivial (the rd-write is the unified-memory rd lane already
    witnessed by `arith_mem`).

    The `NoKnownDefect` obligation is supplied DIRECTLY by the caller as
    `h_known : Defects.NoKnownDefect (mulEnvOf …)` (= `RowOutsideDefectRegion`'s mul
    arm) — the GENUINE `NoKnownDefect` of the SPECIFIC env this proof feeds to the
    global theorem, NOT a selector-∀ and NOT a contradictory `False`-binder.  It is
    SATISFIABLE: for an honest MUL row (`RowData_mul.h_not_forge`, i.e.
    `np = na XOR nb`) the row is outside the forge shape, so `NoKnownDefect` is TRUE
    and the caller proves it.  Non-vacuous: the narrowed MUL exclusion is exactly
    the two exceptional product-sign shapes the ArithTable admits for op 180, so an
    honest signed MUL row supplies all binders. -/
theorem stepStrong_mul
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i)
    (h_known : ¬ Defects.SignedMulForge d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd,
           { result_part := VectorHalf.Low
             signed_rs1 := d.toClaim.srs1
             signed_rs2 := d.toClaim.srs2 }))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := mulEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  -- The threaded `¬ SignedMulForge` obligation is (defeq, via
  -- `signedMulForge_iff_mulShape`) `¬ MaliciousSignedMulWitnessShape env`; the
  -- DIV/REM and FENCE shapes are vacuous for a `.mul` env.
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env h_known (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `mulh` step (channel-balance form), via the OpEnvelope route.

    MULH is the signed × signed high multiply (op 181), a former defect-gated op
    now landed on the OpEnvelope route.  CONSTRUCT `OpEnvelope.mulh` (= `mulhEnvOf`)
    from the trace's `RowData_mulh` and invoke `zisk_riscv_compliant_program_bus`,
    projecting the `exec_eq_remaining` conjunct.  The `NoKnownDefect` obligation is
    the GENUINE `NoKnownDefect (mulhEnvOf …)` of the SPECIFIC env, SATISFIABLE for
    an honest MULH row (`RowData_mulh.h_not_forge`).  High-half operand sign facts
    are derived in the compliance wrapper from indexed Arith range evidence.
    Non-vacuous. -/
theorem stepStrong_mulh
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i)
    (h_known : ¬ Defects.SignedMulForge d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := mulhEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env h_known (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `mulhsu` step (channel-balance form), via the OpEnvelope route.
    Companion of `stepStrong_mulh` for the signed × unsigned high multiply
    (op 179). -/
theorem stepStrong_mulhsu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i)
    (h_known : ¬ Defects.SignedMulForge d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := mulhsuEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env h_known (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `div` step (channel-balance form), via the OpEnvelope route.

    DIV is the signed 64-bit division (op `184`), a former defect-gated op now
    landed on the OpEnvelope route.  CONSTRUCT `OpEnvelope.div` (= the shared
    `divEnvOf`) from the trace's `RowData_div` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining` conjunct.
    `aeneasBridgeTrust` is the 7-tuple of Main decode pins; the memory-timeline
    obligation is trivial (the rd-write is the unified-memory rd lane already
    witnessed by `arith_mem`).

    The `NoKnownDefect` obligation is supplied DIRECTLY by the caller as
    `h_known : Defects.NoKnownDefect (divEnvOf …)` (= `RowOutsideDefectRegion`'s div
    arm) — the GENUINE `NoKnownDefect` of the SPECIFIC env this proof feeds to the
    global theorem, NOT a selector-∀ and NOT a contradictory `False`-binder.  It is
    SATISFIABLE: for an honest signed DIV row (`RowData_div.h_not_forge`, i.e.
    nonzero-divisor `|r| ≠ |op2|`) the row is outside the `|r| = |op2|`
    `LT_ABS_NP` false-positive, so `NoKnownDefect` is TRUE and the caller proves
    it.  Non-vacuous: the narrowed DIV exclusion is exactly the genuine circuit-bug
    forge (codygunton/zisk#5), and divisor-zero rows are handled by
    `h_boundary`; signed overflow is handled by the signed DIV bridge. -/
theorem stepStrong_div
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_div trace binding i)
    (h_known : ¬ Defects.DivRemForge d.toInputs.div_input.r2_val d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, false))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := divEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  -- The threaded `¬ DivRemForge` obligation is (defeq, via
  -- `divRemForge_iff_divShape`) `¬ ArithDivDynamicWitnessShape env`; the
  -- signed-MUL and FENCE shapes are vacuous for a `.div` env.
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) h_known trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `rem` step (channel-balance form), via the OpEnvelope route.
    Companion of `stepStrong_div` for the signed 64-bit remainder (op `185`,
    secondary ArithDiv lane).  Same OpEnvelope-route pattern; the caller-supplied
    `h_known` is the GENUINE `NoKnownDefect (remEnvOf …)`, SATISFIABLE for an honest
    signed REM row (`RowData_rem.h_not_forge`).  Non-vacuous. -/
theorem stepStrong_rem
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i)
    (h_known : ¬ Defects.DivRemForge d.toInputs.rem_input.r2_val d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, false))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := remEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) h_known trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `divw` step (channel-balance form), via the OpEnvelope route.
    W-mode analogue of `stepStrong_div` (signed 32-bit division, op `188`,
    `m32 = 1`).  Carries the W-mode chunk-zero pins + sign-extension choice via
    `RowData_divw`; the caller-supplied `h_known` is the GENUINE
    `NoKnownDefect (divwEnvOf …)`, SATISFIABLE for an honest signed DIVW row
    (`RowData_divw.h_not_forge`, `|r₃₂| ≠ |op2₃₂|`).  Non-vacuous. -/
theorem stepStrong_divw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i)
    (h_known : ¬ Defects.DivRemForgeW d.toInputs.divw_input.r2_val d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, false))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := divwEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) h_known trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `remw` step (channel-balance form), via the OpEnvelope route.
    W-mode analogue of `stepStrong_rem` (signed 32-bit remainder, op `189`,
    `m32 = 1`, secondary lane).  Non-vacuous (`RowData_remw.h_not_forge`). -/
theorem stepStrong_remw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i)
    (h_known : ¬ Defects.DivRemForgeW d.toInputs.remw_input.r2_val d.toInputs.v d.toInputs.r_a) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, false))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨d.toClaim.bus.exec_row, [d.toClaim.bus.e0, d.toClaim.bus.e1, d.toClaim.bus.e2]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := remwEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) h_known trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `fence` step (channel-balance form), via the OpEnvelope route.

    FENCE is the FENCE-decode-gap opcode.  CONSTRUCT `OpEnvelope.fence` (= the
    shared `fenceEnvOf`) from the trace's `RowData_fence` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_nomem` conjunct
    (`.2.2.2.1`).  `aeneasBridgeTrust` is the two flat decode pins; the
    memory-timeline obligation is trivial (FENCE has no memory entry).

    The `NoKnownDefect` obligation is supplied DIRECTLY by the caller as
    `h_known : Defects.NoKnownDefect (fenceEnvOf …)` (= `RowOutsideDefectRegion`'s fence
    arm) — the GENUINE `NoKnownDefect` of the SPECIFIC env this proof feeds to the
    old theorem, NOT a selector-∀ and NOT a contradictory `False`-binder.  It is
    SATISFIABLE: for an honest FENCE row (`RowData_fence.h_fm_zero` / `h_rs_x0` /
    `h_rd_x0`) the env is the honest env, so `NoKnownDefect` is TRUE and the caller
    proves it.  Non-vacuous: the malicious FENCE shapes are excluded exactly by the
    honest-shape pins the caller supplies, as the FENCE defect ledger documents. -/
theorem stepStrong_fence
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_fence trace binding i)
    (h_known : Defects.FenceKnownGood d.toClaim.fm d.toClaim.rs d.toClaim.rd) :
    execute_instruction (instruction.FENCE (d.toClaim.fm, d.toClaim.fenceP, d.toClaim.fenceS, d.toClaim.rs, d.toClaim.rd)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let env : OpEnvelope state m i.val := fenceEnvOf trace binding i d
  have h_bridge : env.aeneasBridgeTrust := ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  -- The threaded `FenceKnownGood` obligation is (defeq, via
  -- `fenceKnownGood_iff_fenceShape`) `FenceKnownGoodShape env`; the signed-MUL
  -- and DIV/REM shapes are vacuous for a `.fence` env.
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) h_known
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.1


end ZiskFv.Compliance
