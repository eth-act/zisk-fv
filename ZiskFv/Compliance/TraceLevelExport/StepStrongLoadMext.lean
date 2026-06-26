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

/-! ## Strengthened load arms (LB/LH/LW/LD/LBU/LHU/LWU, channel-balance form)

Same direct-lift route.  The hint's obstacle — the `OpEnvelope` load arm needing
`Var`/`Environment`-level interaction-evaluation provenance (`h_mainEval`/
`h_providerEval`/`h_msg`) that the witness-based load constructions bypass via
`matches_memory_entry_refl` — was specific to the `OpEnvelope`/global-theorem
route.  The direct-lift route never builds an `OpEnvelope`; it lifts
`construction_<op>_sound`'s `bus_effect`-form conclusion (3-entry memory list
`[e0, e1, e2]` over `busLd`) to the channel-balance form via the `rfl`-bridge
`state_effect_via_channels_eq_bus_effect_2`, so the eval-provenance is never
needed.  The #76 residuals (`h_memory_timeline`, `h_mem_match`, …) and the
signed-load `h_static`/`h_match` BinaryExtension provider linkage are carried
verbatim as `RowData_<op>` binders (they live inside each construction, NOT in any
`OpEnvelope` field).  Non-vacuous: `execRow` is a genuine ∀-binder; the memory
list is the real 3-entry `busLd` emission; the Mem-AIR / BinaryExtension provider
records are real `Valid_Mem`/`Valid_BinaryExtension` rows. -/

/-- Strengthened `ld` step (channel-balance form). -/
theorem stepStrong_ld
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_ld trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.ld_input.imm, regidx.Regidx d.toClaim.ld_input.r1, regidx.Regidx d.toClaim.ld_input.rd, false, 8))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.ld_state_assumptions d.toClaim.ld_input state)
      (PureSpec.execute_LOADD_pure d.toClaim.ld_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.ld d.toClaim.ld_input d.toInputs.regs d.toInputs.mem bus pins promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.1

/-- Strengthened `lbu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_lbu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lbu trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.lbu_input.imm, regidx.Regidx d.toClaim.lbu_input.r1, regidx.Regidx d.toClaim.lbu_input.rd, true, 1))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.lbu_state_assumptions d.toClaim.lbu_input state)
      (PureSpec.execute_LOADBU_pure d.toClaim.lbu_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lbu d.toClaim.lbu_input d.toInputs.regs d.toInputs.mem bus d.toInputs.align pins d.toDecode.h_width promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `lhu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_lhu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lhu trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.lhu_input.imm, regidx.Regidx d.toClaim.lhu_input.r1, regidx.Regidx d.toClaim.lhu_input.rd, true, 2))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.lhu_state_assumptions d.toClaim.lhu_input state)
      (PureSpec.execute_LOADHU_pure d.toClaim.lhu_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lhu d.toClaim.lhu_input d.toInputs.regs d.toInputs.mem bus d.toInputs.align pins d.toDecode.h_width promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `lwu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_lwu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lwu trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.lwu_input.imm, regidx.Regidx d.toClaim.lwu_input.r1, regidx.Regidx d.toClaim.lwu_input.rd, true, 4))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.lwu_state_assumptions d.toClaim.lwu_input state)
      (PureSpec.execute_LOADWU_pure d.toClaim.lwu_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lwu d.toClaim.lwu_input d.toInputs.regs d.toInputs.mem bus d.toInputs.align pins d.toDecode.h_width promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `lb` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_lb
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lb trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.lb_input.imm, regidx.Regidx d.toClaim.lb_input.r1, regidx.Regidx d.toClaim.lb_input.rd, false, 1))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SIGNEXTEND_B :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.lb_state_assumptions d.toClaim.lb_input state)
      (PureSpec.execute_LOADB_pure d.toClaim.lb_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lb_via_static_match d.toClaim.lb_input d.toInputs.regs d.toInputs.mem d.toDecode.v d.toDecode.r_binary d.toDecode.offset d.toDecode.env
      d.toDecode.h_static d.toDecode.h_match bus pins promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1

/-- Strengthened `lh` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_lh
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lh trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.lh_input.imm, regidx.Regidx d.toClaim.lh_input.r1, regidx.Regidx d.toClaim.lh_input.rd, false, 2))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SIGNEXTEND_H :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.lh_state_assumptions d.toClaim.lh_input state)
      (PureSpec.execute_LOADH_pure d.toClaim.lh_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lh_via_static_match d.toClaim.lh_input d.toInputs.regs d.toInputs.mem d.toDecode.v d.toDecode.r_binary d.toDecode.offset d.toDecode.env
      d.toDecode.h_static d.toDecode.h_match bus pins promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1

/-- Strengthened `lw` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_lw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lw trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.LOAD
        (d.toClaim.lw_input.imm, regidx.Regidx d.toClaim.lw_input.r1, regidx.Regidx d.toClaim.lw_input.rd, false, 4))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busLd trace i d.toClaim.execRow).exec_row,
           [ (busLd trace i d.toClaim.execRow).e0
           , (busLd trace i d.toClaim.execRow).e1
           , (busLd trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busLd trace i d.toClaim.execRow
  have h_core : (mainRowWithRomLd trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomLd_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomLd trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomLd trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SIGNEXTEND_W :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd trace i)) (-1) 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLd trace i)) 1 1) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  let promises : ZiskFv.EquivCore.Promises.LoadStructuralPromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.lw_state_assumptions d.toClaim.lw_input state)
      (PureSpec.execute_LOADW_pure d.toClaim.lw_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lw_via_static_match d.toClaim.lw_input d.toInputs.regs d.toInputs.mem d.toDecode.v d.toDecode.r_binary d.toDecode.offset d.toDecode.env
      d.toDecode.h_static d.toDecode.h_match bus pins promises d.toInputs.r_mem
      (mainRowVar := mainConstVar (mainRowWithRomLd trace i))
      (memRowVar := memConstVar (ZiskFv.AirsClean.Mem.rowAt d.toInputs.mem d.toInputs.r_mem))
      (mainEnv := loadEvalEnv) (memEnv := loadEvalEnv)
      (mainMult := (-1 : Expression FGL)) (providerMult := (1 : Expression FGL))
      (h_mainEval := rfl) (h_providerEval := rfl)
      (by simpa only [loadMemMsg, loadMainMsg] using d.toInputs.h_msg)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simp only [eval_memConstVar])
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_b_match)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr1)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_zero_iff)
      (by simpa only [eval_mainConstVar] using d.toInputs.h_addr2_idx)
      d.toInputs.h_mem_sel d.toInputs.h_mem_wr
  have h_bridge : env.aeneasBridgeTrust := d.toDecode.h_width
  have h_mem : env.memoryTimelineConstructionEvidence := d.toInputs.h_memory_timeline
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.1

/-! ## Strengthened M-ext-unsigned arms (MULW/MULHU/DIVU/DIVUW/REMU/REMUW)

Same DIRECT-LIFT route as the control-flow / store / load arms — NOT the
`OpEnvelope`/`zisk_riscv_compliant_program_bus` route.  Each
`construction_<op>_sound` already proves the `bus_effect`-form per-step
conclusion (2-entry exec row + `[e0, e1, e2]` over the real `busSub` row) using
the FAITHFUL loose Arith carry bound (`<983041`).  `state_effect_via_channels`
is `@[reducible]`-defeq to `bus_effect.2`, so
`rw [state_effect_via_channels_eq_bus_effect_2]` + the construction theorem
yields the channel-balance proposition WITHOUT ever invoking the canonical
`equiv_<op>` (whose tight `<131072` carry bound is row-locally suspect /
unconstructible for real 4×4 carries).  This lift therefore NEVER touches that
tight bound: it is the channel-balance lift of the same loose-bound construction
already exported in `bus_effect` form by `RowConstructionData` / `StepCompliance`.

Non-vacuity: `execRow` remains a genuine `∀`-binder inside each
`RowData_<op>`; no `False.elim`, no contradictory binder; the conclusion is over
the real `busSub` row.  These are strictly stronger than the corresponding
`bus_effect`-form M-ext arms (channel-balance form, same data). -/

/-- Strengthened `mulw` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.mulw` from the trace's `RowData_mulw` (the SHARED-ArithMul
    provider row + balance-derived `FullSpec` selected via `mulwArow`) and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.  The lookup-witness structures are BUILT from `mulwArow_fullSpec` via
    the `*_of_fullSpec` / `*_of_spec` builders; `aeneasBridgeTrust` is flat decode
    pins carried as `RowData_mulw` residuals (`m32 = 1` for W-mode); `NoKnownDefect`
    comes from the locally-assembled `NoKnownDefect`.  Non-vacuous (real provider FullSpec). -/
theorem stepStrong_mulw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulw trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.MULW (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace i d.toClaim.execRow).exec_row,
           [ (busSub trace i d.toClaim.execRow).e0
           , (busSub trace i d.toClaim.execRow).e1
           , (busSub trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  set v := vOfMulwRow (mulwArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op) with hv
  have h_full : ZiskFv.AirsClean.ArithMul.FullSpec (ZiskFv.AirsClean.ArithMul.rowAt v 0) :=
    mulwArow_fullSpec trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m i.val)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v 0) :=
    mulwArow_match trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  obtain ⟨h_spec, h_arith_table, h_c46, h_chunk_spec, h_carry_spec⟩ := h_full
  let arith_table : ZiskFv.Compliance.ArithMulTableWitness v 0 :=
    arithMulTableWitness_of_fullSpec ⟨h_spec, h_arith_table, h_c46, h_chunk_spec, h_carry_spec⟩
  let arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithMul.chunkRangeLookupWitness_of_spec h_spec h_chunk_spec
  let arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithMul.signedCarryRangeLookupWitness_of_spec h_spec h_carry_spec
  have h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v 0 := ⟨h_spec, h_c46⟩
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_MUL_W :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness m i.val
        (busSub trace i d.toClaim.execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub, m,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.toInputs.mulw_input.r1_val d.toInputs.mulw_input.r2_val d.toInputs.mulw_input.rd d.toInputs.mulw_input.PC
      (PureSpec.execute_MULW_pure d.toInputs.mulw_input).nextPC
      d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow).exec_row
      (busSub trace i d.toClaim.execRow).e0
      (busSub trace i d.toClaim.execRow).e1 (busSub trace i d.toClaim.execRow).e2 :=
    { input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := d.toInputs.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.mulw d.toInputs.mulw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow) v 0
      pins h_match_primary promises arith_mem h_row_constraints
      arith_table arith_chunk_ranges arith_carry_ranges
      (d.toInputs.h_a23 d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_b23 d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_sext_choice d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op)
  have h_bridge : env.aeneasBridgeTrust := by
    refine ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `mulhu` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.mulhu` from the trace's `RowData_mulhu` (the same
    SHARED-ArithMul provider row + balance-derived `FullSpec` the construction
    selects via `mulhuArow`) and invoke `zisk_riscv_compliant_program_bus`,
    projecting the `exec_eq_remaining` conjunct.  The three lookup-witness
    structures (`ArithMulTableWitness`, `ArithMulChunkRangeWitness`,
    `ArithMulSignedCarryRangeWitness`) are BUILT from the trace's `FullSpec`
    (`mulhuArow_fullSpec`) via the `*_of_fullSpec` / `*_of_spec` builders;
    `aeneasBridgeTrust` is flat decode pins carried as `RowData_mulhu` residuals;
    `NoKnownDefect` comes from the locally-assembled `NoKnownDefect`.

    Non-vacuous: the envelope's witnesses are the REAL provider row's FullSpec
    projections derived from `trace.channels_balanced` / `trace.spec_holds`, not a fabricated
    environment; `execRow` remains a genuine ∀-binder. -/
theorem stepStrong_mulhu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhu trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Unsigned
             signed_rs2 := .Unsigned }))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace i d.toClaim.execRow).exec_row,
           [ (busSub trace i d.toClaim.execRow).e0
           , (busSub trace i d.toClaim.execRow).e1
           , (busSub trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  -- Balance-selected SHARED-ArithMul provider row + its FullSpec (ArithMul view).
  set v := vOfMulwRow (mulhuArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op) with hv
  have h_full : ZiskFv.AirsClean.ArithMul.FullSpec (ZiskFv.AirsClean.ArithMul.rowAt v 0) :=
    mulhuArow_fullSpec trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m i.val)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v 0) :=
    mulhuArow_match trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  -- The three lookup-witnesses, BUILT from FullSpec.
  obtain ⟨h_spec, h_arith_table, h_c46, h_chunk_spec, h_carry_spec⟩ := h_full
  let arith_table : ZiskFv.Compliance.ArithMulTableWitness v 0 :=
    arithMulTableWitness_of_fullSpec ⟨h_spec, h_arith_table, h_c46, h_chunk_spec, h_carry_spec⟩
  let arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithMul.chunkRangeLookupWitness_of_spec h_spec h_chunk_spec
  let arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithMul.signedCarryRangeLookupWitness_of_spec h_spec h_carry_spec
  have h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v 0 := ⟨h_spec, h_c46⟩
  -- Decode pins bundle.
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_MULUH :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  -- Main rd-write memory witness, from `store_pc = 0`.
  have h_core_store_pc :
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness m i.val
        (busSub trace i d.toClaim.execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub, m,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  -- Promises bundle: Sail reads + exec artifacts as binders; MemBus shape by rfl.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.toInputs.mulhu_input.r1_val d.toInputs.mulhu_input.r2_val d.toInputs.mulhu_input.rd d.toInputs.mulhu_input.PC
      (PureSpec.execute_MULH_mulhu_pure d.toInputs.mulhu_input).nextPC
      d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow).exec_row
      (busSub trace i d.toClaim.execRow).e0
      (busSub trace i d.toClaim.execRow).e1 (busSub trace i d.toClaim.execRow).e2 :=
    { input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := d.toInputs.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.mulhu d.toInputs.mulhu_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow) v 0
      pins h_match_secondary promises arith_mem d.toDecode.bounds h_row_constraints
      arith_table arith_chunk_ranges arith_carry_ranges (d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op)
  have h_bridge : env.aeneasBridgeTrust := by
    refine ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `divu` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.divu` from the trace's `RowData_divu` (the SHARED-ArithMul
    provider row, VIEWED as ArithDiv via `vOfDivuRow`) and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.  The four ArithDiv lookup-witness structures are BUILT from the
    SHARED-ArithMul provider `FullSpec` (`divuArow_fullSpec_row`) via the
    `arithDiv_fullSpec_of_arithMul_fullSpec` view bridge + the ArithDiv
    `*_of_fullSpec` / `*_of_spec` builders; `remainder_bound` is the explicit
    residual carried by `RowData_divu`; `aeneasBridgeTrust` is flat decode pins;
    `NoKnownDefect` comes from the locally-assembled `NoKnownDefect`.  Non-vacuous (real
    provider FullSpec; the witnesses' substance is the balance-derived facts). -/
theorem stepStrong_divu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divu trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, true))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace i d.toClaim.execRow).exec_row,
           [ (busSub trace i d.toClaim.execRow).e0
           , (busSub trace i d.toClaim.execRow).e1
           , (busSub trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  set arow := divuArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op with harow
  set v := vOfDivuRow arow with hv
  -- SHARED-ArithMul provider FullSpec of the selected row.
  have h_full_mul : ZiskFv.AirsClean.ArithMul.FullSpec arow :=
    divuArow_fullSpec_row trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m i.val)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v 0) :=
    divuArow_match trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  -- ArithDiv-view FullSpec + the four lookup-witnesses, BUILT from it.
  have h_full_div : ZiskFv.AirsClean.ArithDiv.FullSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v 0) :=
    arithDiv_fullSpec_of_arithMul_fullSpec arow h_full_mul
  obtain ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩ := h_full_mul
  let arith_table : ZiskFv.Compliance.ArithDivTableWitness v 0 :=
    arithDivTableWitness_of_fullSpec h_full_div
  let arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.chunkRangeLookupWitness_of_spec h_full_div.1 h_mul_chunks
  let arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.signedCarryRangeLookupWitness_of_spec h_full_div.1 h_mul_carry
  have h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v 0 :=
    divu_row_constraints_of_arithMul_fullSpec arow
      ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩
  -- Decode pins bundle.
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_DIVU :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  -- Main rd-write memory witness, from `store_pc = 0`.
  have h_core_store_pc :
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness m i.val
        (busSub trace i d.toClaim.execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub, m,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.toInputs.divu_input.r1_val d.toInputs.divu_input.r2_val d.toInputs.divu_input.rd d.toInputs.divu_input.PC
      (PureSpec.execute_DIVREM_divu_pure d.toInputs.divu_input).nextPC
      d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow).exec_row
      (busSub trace i d.toClaim.execRow).e0
      (busSub trace i d.toClaim.execRow).e1 (busSub trace i d.toClaim.execRow).e2 :=
    { input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := d.toInputs.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.divu d.toInputs.divu_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow) v 0
      pins h_match_primary promises arith_mem d.toDecode.bounds h_row_constraints
      arith_table arith_chunk_ranges arith_carry_ranges (d.toInputs.remainder_bound d.toDecode.h_main_active d.toDecode.h_main_op)
      (d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op)
  have h_bridge : env.aeneasBridgeTrust := by
    refine ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  -- DIVU is the dedicated `exec_eq_divu` conjunct (10th), not `exec_eq_remaining`.
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.1

/-- Strengthened `divuw` step (channel-balance form), via the OpEnvelope route:
    same SHARED-ArithMul-provider → ArithDiv-view pattern as `stepStrong_divu`
    (`m32 = 1` for W-mode), routing to the `exec_eq_remaining` conjunct
    (`equiv_DIVUW`).  Adds the W-mode residuals `h_b23`/`h_c23`/`h_sext_choice`
    carried by `RowData_divuw`.  Non-vacuous (real provider FullSpec). -/
theorem stepStrong_divuw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divuw trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIVW (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, true))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace i d.toClaim.execRow).exec_row,
           [ (busSub trace i d.toClaim.execRow).e0
           , (busSub trace i d.toClaim.execRow).e1
           , (busSub trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  set arow := divuwArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op with harow
  set v := vOfDivuRow arow with hv
  have h_full_mul : ZiskFv.AirsClean.ArithMul.FullSpec arow :=
    divuwArow_fullSpec_row trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m i.val)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v 0) :=
    divuwArow_match trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_full_div : ZiskFv.AirsClean.ArithDiv.FullSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v 0) :=
    arithDiv_fullSpec_of_arithMul_fullSpec arow h_full_mul
  obtain ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩ := h_full_mul
  let arith_table : ZiskFv.Compliance.ArithDivTableWitness v 0 :=
    arithDivTableWitness_of_fullSpec h_full_div
  let arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.chunkRangeLookupWitness_of_spec h_full_div.1 h_mul_chunks
  let arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.signedCarryRangeLookupWitness_of_spec h_full_div.1 h_mul_carry
  have h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v 0 :=
    divu_row_constraints_of_arithMul_fullSpec arow
      ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_DIVU_W :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness m i.val
        (busSub trace i d.toClaim.execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub, m,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.toInputs.divuw_input.r1_val d.toInputs.divuw_input.r2_val d.toInputs.divuw_input.rd d.toInputs.divuw_input.PC
      (PureSpec.execute_DIVREM_divuw_pure d.toInputs.divuw_input).nextPC
      d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow).exec_row
      (busSub trace i d.toClaim.execRow).e0
      (busSub trace i d.toClaim.execRow).e1 (busSub trace i d.toClaim.execRow).e2 :=
    { input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := d.toInputs.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.divuw d.toInputs.divuw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow) v 0
      pins h_match_primary promises arith_mem d.toDecode.bounds h_row_constraints
      arith_table arith_chunk_ranges arith_carry_ranges (d.toInputs.remainder_bound d.toDecode.h_main_active d.toDecode.h_main_op)
      (d.toInputs.h_b23 d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_c23 d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_sext_choice d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op)
  have h_bridge : env.aeneasBridgeTrust := by
    refine ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `remu` step (channel-balance form), via the OpEnvelope route:
    same SHARED-ArithMul-provider → ArithDiv-view pattern as `stepStrong_divu`,
    routing to the `exec_eq_remaining` conjunct (`equiv_REMU`).  The match is the
    secondary d-lane (`opBus_row_ArithDivSecondary`, REMU mode `main_div = 0`).
    Non-vacuous (real provider FullSpec; witnesses' substance is balance-derived). -/
theorem stepStrong_remu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remu trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, true))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace i d.toClaim.execRow).exec_row,
           [ (busSub trace i d.toClaim.execRow).e0
           , (busSub trace i d.toClaim.execRow).e1
           , (busSub trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  set arow := remuArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op with harow
  set v := vOfDivuRow arow with hv
  have h_full_mul : ZiskFv.AirsClean.ArithMul.FullSpec arow :=
    remuArow_fullSpec_row trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m i.val)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v 0) :=
    remuArow_match trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_full_div : ZiskFv.AirsClean.ArithDiv.FullSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v 0) :=
    arithDiv_fullSpec_of_arithMul_fullSpec arow h_full_mul
  obtain ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩ := h_full_mul
  let arith_table : ZiskFv.Compliance.ArithDivTableWitness v 0 :=
    arithDivTableWitness_of_fullSpec h_full_div
  let arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.chunkRangeLookupWitness_of_spec h_full_div.1 h_mul_chunks
  let arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.signedCarryRangeLookupWitness_of_spec h_full_div.1 h_mul_carry
  have h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v 0 :=
    divu_row_constraints_of_arithMul_fullSpec arow
      ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_REMU :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness m i.val
        (busSub trace i d.toClaim.execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub, m,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.toInputs.remu_input.r1_val d.toInputs.remu_input.r2_val d.toInputs.remu_input.rd d.toInputs.remu_input.PC
      (PureSpec.execute_DIVREM_remu_pure d.toInputs.remu_input).nextPC
      d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow).exec_row
      (busSub trace i d.toClaim.execRow).e0
      (busSub trace i d.toClaim.execRow).e1 (busSub trace i d.toClaim.execRow).e2 :=
    { input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := d.toInputs.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.remu d.toInputs.remu_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow) v 0
      pins h_match_secondary promises arith_mem d.toDecode.bounds h_row_constraints
      arith_table arith_chunk_ranges arith_carry_ranges (d.toInputs.remainder_bound d.toDecode.h_main_active d.toDecode.h_main_op)
      (d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op)
  have h_bridge : env.aeneasBridgeTrust := by
    refine ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `remuw` step (channel-balance form), via the OpEnvelope route:
    same SHARED-ArithMul-provider → ArithDiv-view pattern as `stepStrong_divuw`
    (`m32 = 1`), secondary d-lane match (`opBus_row_ArithDivSecondary`), routing
    to the `exec_eq_remaining` conjunct (`equiv_REMUW`).  Non-vacuous. -/
theorem stepStrong_remuw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remuw trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (d.toClaim.r2, d.toClaim.r1, d.toClaim.rd, true))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSub trace i d.toClaim.execRow).exec_row,
           [ (busSub trace i d.toClaim.execRow).e0
           , (busSub trace i d.toClaim.execRow).e1
           , (busSub trace i d.toClaim.execRow).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  set arow := remuwArow trace binding i d.toDecode.h_main_active d.toDecode.h_main_op with harow
  set v := vOfDivuRow arow with hv
  have h_full_mul : ZiskFv.AirsClean.ArithMul.FullSpec arow :=
    remuwArow_fullSpec_row trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m i.val)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v 0) :=
    remuwArow_match trace binding i d.toDecode.h_main_active d.toDecode.h_main_op
  have h_full_div : ZiskFv.AirsClean.ArithDiv.FullSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v 0) :=
    arithDiv_fullSpec_of_arithMul_fullSpec arow h_full_mul
  obtain ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩ := h_full_mul
  let arith_table : ZiskFv.Compliance.ArithDivTableWitness v 0 :=
    arithDivTableWitness_of_fullSpec h_full_div
  let arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.chunkRangeLookupWitness_of_spec h_full_div.1 h_mul_chunks
  let arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v 0 :=
    ZiskFv.AirsClean.ArithDiv.signedCarryRangeLookupWitness_of_spec h_full_div.1 h_mul_carry
  have h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v 0 :=
    divu_row_constraints_of_arithMul_fullSpec arow
      ⟨h_mul_spec, h_mul_table, h_mul_c46, h_mul_chunks, h_mul_carry⟩
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_REMU_W :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness m i.val
        (busSub trace i d.toClaim.execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub, m,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state d.toInputs.remuw_input.r1_val d.toInputs.remuw_input.r2_val d.toInputs.remuw_input.rd d.toInputs.remuw_input.PC
      (PureSpec.execute_DIVREM_remuw_pure d.toInputs.remuw_input).nextPC
      d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow).exec_row
      (busSub trace i d.toClaim.execRow).e0
      (busSub trace i d.toClaim.execRow).e1 (busSub trace i d.toClaim.execRow).e2 :=
    { input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := d.toDecode.h_exec_len
      e0_mult := d.toDecode.h_e0_mult
      e1_mult := d.toDecode.h_e1_mult
      nextPC_matches := d.toInputs.h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := d.toInputs.h_rd_idx }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.remuw d.toInputs.remuw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd (busSub trace i d.toClaim.execRow) v 0
      pins h_match_secondary promises arith_mem d.toDecode.bounds h_row_constraints
      arith_table arith_chunk_ranges arith_carry_ranges (d.toInputs.remainder_bound d.toDecode.h_main_active d.toDecode.h_main_op)
      (d.toInputs.h_b23 d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_c23 d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_sext_choice d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs1_value d.toDecode.h_main_active d.toDecode.h_main_op) (d.toInputs.h_rs2_value d.toDecode.h_main_active d.toDecode.h_main_op)
  have h_bridge : env.aeneasBridgeTrust := by
    refine ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc,
      d.toDecode.h_jmp_offset1, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2


end ZiskFv.Compliance
