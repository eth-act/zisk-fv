import ZiskFv.Compliance.TraceLevelExport.RegisterWriteProviderRanges
import ZiskFv.Compliance.TraceLevelExport.RegisterWriteControlRanges
import ZiskFv.Compliance.TraceLevelExport.RegisterCoverageBridge
import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterFold
import ZiskFv.Compliance.TraceLevelExport.PureInputs

/-!
# Bounds of genuine source-selected physical register writes

Provider byte/chunk witnesses and the retained source defect domain bound the
ACTUAL producer entry of one real architectural step. In particular expanded
JALR uses its actual terminal physical row, not equality with the start entry.
The following source-prefix consumer derives coverage from the same successful
lowerings and accepted raw Main rows, never from a total physical step family.
-/

namespace ZiskFv.Compliance.PhysicalRegisterWriteRanges

open ZiskFv.AirsClean.FullEnsemble (mainTableRowAtOrZero mainOfTable mainOfTable_pc
  mainOfTable_store_pc mainOfTable_jmp_offset2 mainOfTable_jmp_offset1 mainOfTable_is_external_op
  mainOfTable_op mainOfTable_b_0 mainOfTable_b_1 mainOfTable_c_0 mainOfTable_c_1
  mainOfTable_set_pc mainOfTable_flag mainOfTable_segment_l1)
open ZiskFv.AirsClean.Main (cMemMessage rowAt)
open ZiskFv.Channels.MemoryBus (MemBusMessage.toEntry)

private lemma load_b_active_of_mem_message
    {n : ℕ} {trace : AcceptedZiskTrace n} (i : Fin n)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) (r_mem : ℕ)
    (h_msg : loadMemMsg (ZiskFv.AirsClean.Mem.rowAt mem r_mem) =
      loadMainMsg (mainRowWithRomLd trace i))
    (h_b_src_ind : (mainRowWithRomLd trace i).rom.b_src_ind = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    -((mainRowWithRomLd trace i).rom.b_src_mem
      + (mainRowWithRomLd trace i).rom.b_src_ind
      + (mainRowWithRomLd trace i).rom.b_src_reg) = (-1 : FGL) := by
  have h_mem_op := congrArg (fun message => message[0]!) h_msg
  simp [loadMemMsg, loadMainMsg, ChannelInteraction.toRaw,
    Channel.emitted, emitted, AbstractInteraction.eval, toElements,
    ProvableStruct.componentsToElements,
    ProvableStruct.toComponents, ProvableStruct.components,
    ZiskFv.AirsClean.Mem.memBusMessageExpr,
    ZiskFv.AirsClean.Main.bMemMessageExpr, ZiskFv.AirsClean.Main.bMemOpExpr,
    ZiskFv.AirsClean.Mem.rowAt, loadEvalEnv, mainConstVar, memConstVar,
    Expression.eval,
    h_mem_wr] at h_mem_op
  obtain ⟨_, _, _, _, _, _, _, _, h_b_src_mem_bool, _, _, _, _,
    h_b_src_reg_bool, _⟩ :=
    RomDecodeBinding.mainRow_flags_boolean trace
      ⟨i.val, trace.mainTable_index i⟩
  change (mainRowWithRomLd trace i).rom.b_src_mem *
    (1 - (mainRowWithRomLd trace i).rom.b_src_mem) = 0 at h_b_src_mem_bool
  change (mainRowWithRomLd trace i).rom.b_src_reg *
    (1 - (mainRowWithRomLd trace i).rom.b_src_reg) = 0 at h_b_src_reg_bool
  have h_b_src_mem : (mainRowWithRomLd trace i).rom.b_src_mem = 0 ∨
      (mainRowWithRomLd trace i).rom.b_src_mem = 1 := by
    rcases mul_eq_zero.mp h_b_src_mem_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  have h_b_src_reg : (mainRowWithRomLd trace i).rom.b_src_reg = 0 ∨
      (mainRowWithRomLd trace i).rom.b_src_reg = 1 := by
    rcases mul_eq_zero.mp h_b_src_reg_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  rcases h_b_src_mem with h_b_src_mem | h_b_src_mem <;>
    rcases h_b_src_reg with h_b_src_reg | h_b_src_reg <;>
    rw [h_b_src_mem, h_b_src_ind, h_b_src_reg] at h_mem_op ⊢
  · rfl
  all_goals
    have h_impossible := congrArg Fin.val h_mem_op
    norm_num at h_impossible

private lemma copyb_entry_range_of_e1_range
    {n : ℕ} {trace : AcceptedZiskTrace n} {sailTrace : SailTrace n}
    (i : Fin n)
    (h_main_active : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0)
    (h_main_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    (h_e1_range : ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      (busLd trace i (Pilot.execRowOf trace i)).e1) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  let row := mainTableRowAtOrZero trace.program trace.mainTable i.val
  let e1 := (busLd trace i (Pilot.execRowOf trace i)).e1
  have h_core := mainRowWithRomLd_core trace sailTrace i
  have h_spec : ZiskFv.AirsClean.Main.Spec row.core := by
    rw [h_core]
    exact mainSpec_at trace sailTrace i
  obtain ⟨_, _, _, _, _, _, h_copy0, h_copy1⟩ :=
    ZiskFv.AirsClean.Main.load_emission_lane_copy_bundle_of_messages row h_spec h_sp
  have h_active_row : row.core.is_external_op = 0 := by
    simpa [row, mainOfTable_is_external_op] using h_main_active
  have h_op_row : row.core.op = ZiskFv.Trusted.OP_COPYB := by
    simpa [row, mainOfTable_op] using h_main_op
  have h_bc0 : row.core.b_0 = row.core.c_0 := by
    simp only [ZiskFv.Airs.Main.internal_op1_copies_b0] at h_copy0
    rw [h_active_row, h_op_row] at h_copy0
    norm_num [ZiskFv.Trusted.OP_COPYB] at h_copy0 ⊢
    linear_combination h_copy0
  have h_bc1 : row.core.b_1 = row.core.c_1 := by
    simp only [ZiskFv.Airs.Main.internal_op1_copies_b1] at h_copy1
    rw [h_active_row, h_op_row] at h_copy1
    norm_num [ZiskFv.Trusted.OP_COPYB] at h_copy1 ⊢
    linear_combination h_copy1
  have h_emit :
      (mainOfTable trace.program trace.mainTable).b_0 i.val =
          ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ (mainOfTable trace.program trace.mainTable).b_1 i.val =
          ZiskFv.Airs.MemoryBus.memory_entry_hi e1 := by
    simp [e1, mainRowWithRomLd, mainOfTable_b_0, mainOfTable_b_1]
  apply cMemMessage_chunks_of_store_pc_zero row h_sp
  · rw [← h_bc0, show row.core.b_0 = e1.value_0 from h_emit.1]
    exact h_e1_range.1
  · rw [← h_bc1, show row.core.b_1 = e1.value_1 from h_emit.2]
    exact h_e1_range.2

private lemma copyb_narrow_entry_range
    {n : ℕ} {trace : AcceptedZiskTrace n} {sailTrace : SailTrace n}
    (i : Fin n)
    (width : FGL)
    (h_width_one_or_two : width = 1 ∨ width = 2)
    (h_main_width : (mainOfTable trace.program trace.mainTable).ind_width i.val = width)
    (h_main_active : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 0)
    (h_main_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_COPYB)
    (h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0)
    (align : ZiskFv.Compliance.MemAlignWitness
      (mainOfTable trace.program trace.mainTable) i.val
      (busLd trace i (Pilot.execRowOf trace i)).e1) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) := by
  let row := mainTableRowAtOrZero trace.program trace.mainTable i.val
  let e1 := (busLd trace i (Pilot.execRowOf trace i)).e1
  have h_core := mainRowWithRomLd_core trace sailTrace i
  have h_spec : ZiskFv.AirsClean.Main.Spec row.core := by
    rw [h_core]
    exact mainSpec_at trace sailTrace i
  obtain ⟨_, _, _, _, _, _, h_copy0, h_copy1⟩ :=
    ZiskFv.AirsClean.Main.load_emission_lane_copy_bundle_of_messages row h_spec h_sp
  have h_active_row : row.core.is_external_op = 0 := by
    simpa [row, mainOfTable_is_external_op] using h_main_active
  have h_op_row : row.core.op = ZiskFv.Trusted.OP_COPYB := by
    simpa [row, mainOfTable_op] using h_main_op
  have h_bc0 : row.core.b_0 = row.core.c_0 := by
    simp only [ZiskFv.Airs.Main.internal_op1_copies_b0] at h_copy0
    rw [h_active_row, h_op_row] at h_copy0
    norm_num [ZiskFv.Trusted.OP_COPYB] at h_copy0 ⊢
    linear_combination h_copy0
  have h_bc1 : row.core.b_1 = row.core.c_1 := by
    simp only [ZiskFv.Airs.Main.internal_op1_copies_b1] at h_copy1
    rw [h_active_row, h_op_row] at h_copy1
    norm_num [ZiskFv.Trusted.OP_COPYB] at h_copy1 ⊢
    linear_combination h_copy1
  have h_emit :
      (mainOfTable trace.program trace.mainTable).b_0 i.val =
          ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ (mainOfTable trace.program trace.mainTable).b_1 i.val =
          ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2 ∧ e1.multiplicity = -1 := by
    simp [e1, mainRowWithRomLd, mainOfTable_b_0, mainOfTable_b_1]
  have h_zero :=
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_subdoubleword_load_high_bytes_zero
      (mainOfTable trace.program trace.mainTable) align.mab align.marb align.ma i.val e1
      h_emit
      (h_width_one_or_two.elim (fun h => Or.inl (h_main_width.trans h))
        (fun h => Or.inr (Or.inl (h_main_width.trans h))))
      align.provider
  apply cMemMessage_chunks_of_store_pc_zero row h_sp
  · rw [← h_bc0]
    rcases h_width_one_or_two with h_width | h_width
    · exact Nat.lt_trans ((h_zero.1 (h_main_width.trans h_width)).2) (by norm_num)
    · exact Nat.lt_trans ((h_zero.2.1 (h_main_width.trans h_width)).2) (by norm_num)
  · rw [← h_bc1]
    rcases h_width_one_or_two with h_width | h_width
    · rw [show row.core.b_1 = e1.value_1 from h_emit.2.1,
        (h_zero.1 (h_main_width.trans h_width)).1]
      decide
    · rw [show row.core.b_1 = e1.value_1 from h_emit.2.1,
        (h_zero.2.1 (h_main_width.trans h_width)).1]
      decide

/-- All 63 original source routes, at the actual producer. Inputs and defect
facts are the retained per-real-step facts, not added physical range promises. -/
theorem real_stepRegWrite_entry_range
    {n : Nat} {trace : AcceptedZiskTrace n} {sailTrace : SailTrace n}
    (i : Fin n) (zs : ZiskStep trace i) (rd : RowDecode trace i zs)
    (ia : InputsAgreeCore trace sailTrace i zs)
    (hAvoid : RowOutsideDefectRegion trace i zs)
    (h_mem_present : ZiskStepLoadMemoryRows trace i zs → MutableMemPresent trace.witness)
    {entry : Interaction.MemoryBusEntry FGL}
    (he : stepRegWrite (stepChannelOutput i zs rd) = some entry)
    (h_ptr : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range entry := by
  have producerEntry : entry = (cMemMessage
      (mainTableRowAtOrZero trace.program trace.mainTable
        (stepProducerRow i zs rd))).toEntry 1 1 := by
    rcases stepRegWrite_eq_none_or_cMemMessage i zs rd with none | some
    · rw [none] at he
      cases he
    · exact Option.some.inj (he.symm.trans some)
  cases zs with
  | beq c => exact nomatch he
  | bne c => exact nomatch he
  | blt c => exact nomatch he
  | bge c => exact nomatch he
  | bltu c => exact nomatch he
  | bgeu c => exact nomatch he
  | sb c => exact nomatch he
  | sh c => exact nomatch he
  | sw c => exact nomatch he
  | sd c => exact nomatch he
  | fence c => exact nomatch he
  | jal c => exact jal_actual_producer_entry_range i c rd hAvoid he h_ptr
  | auipc c => exact auipc_actual_producer_entry_range i c rd hAvoid he h_ptr
  | lui c => exact lui_actual_producer_entry_range i c rd he h_ptr
  | jalr c => exact jalr_actual_producer_entry_range i c rd hAvoid he h_ptr
  | and c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 14 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_AND_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_AND = 14 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | or c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inl h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 15 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_OR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_OR = 15 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | xor c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inr h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := mode_pins_of_emit_op_eq_16_of_static_spec
      _ h_spec_facts h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_XOR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_XOR = 16 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | andi c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_AND := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 14 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_AND_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_AND = 14 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | ori c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_OR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inl h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      _ h_spec_facts 15 (by norm_num) h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_OR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_OR = 15 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | xori c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_XOR := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_logic_provided trace i h_ieo (Or.inr (Or.inr h_op))
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_pins := mode_pins_of_emit_op_eq_16_of_static_spec
      _ h_spec_facts h_core h_op_eq.symm
    have h_carry := ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_XOR_row_of_static_facts
      _ h_core h_wf (by rw [show ZiskFv.Airs.Tables.BinaryTable.OP_XOR = 16 from rfl]; exact h_pins.2.2)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | sub c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_sub_provided trace i h_ieo h_op
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_add_sub_entry_range _ h_spec_facts h_core h_wf
      11 (by norm_num) h_op_eq.symm (Or.inr rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | add c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD := by
      have := rd.h_main_op; exact this
    obtain ⟨_, h_disj⟩ := main_request_add_provided trace i h_ieo h_op
    rcases h_disj with ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ |
        ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩
    · have h_row := (hspec pr hpr)
      rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
      have h_spec_facts := h_row.2
      have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
      have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
      have h_op_eq := hmatch.2.1
      simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
      rw [h_op] at h_op_eq
      have h_carry := binary_static_add_sub_entry_range _ h_spec_facts h_core h_wf
        10 (by norm_num) h_op_eq.symm (Or.inl rfl)
      exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
    · exact binaryAdd_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | addi c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD := by
      have := rd.h_main_op; exact this
    obtain ⟨_, h_disj⟩ := main_request_add_provided trace i h_ieo h_op
    rcases h_disj with ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ |
        ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩
    · have h_row := (hspec pr hpr)
      rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
      have h_spec_facts := h_row.2
      have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
      have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
      have h_op_eq := hmatch.2.1
      simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
      rw [h_op] at h_op_eq
      have h_carry := binary_static_add_sub_entry_range _ h_spec_facts h_core h_wf
        10 (by norm_num) h_op_eq.symm (Or.inl rfl)
      exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
    · exact binaryAdd_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | slt c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 7 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LT h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | sltu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inr h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 6 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LTU h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | slti c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LT := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 7 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LT h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | sltiu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_LTU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_compare_provided trace i h_ieo (Or.inr h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    exact entry_range_of_provider_match i h_sp hmatch
      (binary_static_compare_c_lo_lt _ h_spec_facts h_core h_wf 6 (by norm_num) h_op_eq.symm
        (fun h => ZiskFv.EquivCore.Bridge.Binary.c_byte_zero_of_chain_wf_LTU h))
      (binary_static_opBus_c_hi_lt _ h_spec_facts)
  | addw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_w_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_w_mode_carry_7_zero _ h_spec_facts h_core h_wf
      26 h_op_eq.symm (Or.inl rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | subw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SUB_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_w_provided trace i h_ieo (Or.inr h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_w_mode_carry_7_zero _ h_spec_facts h_core h_wf
      27 h_op_eq.symm (Or.inr rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | addiw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_w_provided trace i h_ieo (Or.inl h_op)
    have h_row := (hspec pr hpr)
    rw [hcomp, ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_row
    have h_spec_facts := h_row.2
    have h_core := ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_row.1
    have h_wf := ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_spec_facts
    have h_op_eq := hmatch.2.1
    simp only [ZiskFv.Airs.OperationBus.opBus_row_Main] at h_op_eq
    rw [h_op] at h_op_eq
    have h_carry := binary_static_w_mode_carry_7_zero _ h_spec_facts h_core h_wf
      26 h_op_eq.symm (Or.inl rfl)
    exact binary_static_entry_range i h_sp hpt hpr hcomp hspec hmatch h_carry
  | mulw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | mulhu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulhu_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | mulh c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulh_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | mulhsu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mulhsu_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | div c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_div_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | divu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_divu_provided trace i h_ieo (Or.inl h_op)
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | divuw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_divuw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | remu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_remu_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | remuw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_remuw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | sll c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inl h_op)
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch (Or.inl h_op)
  | srl c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inl h_op))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch (Or.inr (Or.inl h_op))
  | sra c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inr (Or.inl h_op)))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inl h_op)))
  | slli c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inl h_op)
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch (Or.inl h_op)
  | srli c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inl h_op))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch (Or.inr (Or.inl h_op))
  | srai c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inr (Or.inl h_op)))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inl h_op)))
  | sllw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inr (Or.inr (Or.inl h_op))))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inr (Or.inl h_op))))
  | srlw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_op)))))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_op)))))
  | sraw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_op)))))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_op)))))
  | slliw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SLL_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inr (Or.inr (Or.inl h_op))))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inr (Or.inl h_op))))
  | srliw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRL_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_op)))))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_op)))))
  | sraiw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_SRA_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_shift_provided trace i h_ieo
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_op)))))
    exact binExt_shift_entry_range i h_sp hpt hpr hcomp hspec hmatch
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_op)))))
  | mul c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MUL := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_mul_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | rem c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_rem_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | divw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_DIV_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_divw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | remw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_ieo : (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1 := by
      have := rd.h_main_active; exact this
    have h_op : (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REM_W := by
      have := rd.h_main_op; exact this
    obtain ⟨pt, hpt, pr, hpr, hcomp, hspec, hmatch⟩ :=
      main_request_remw_provided trace i h_ieo h_op
    exact arithMul_entry_range i h_sp hpt hpr hcomp hspec hmatch
  | lb c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    exact binExt_sext_entry_range i h_sp rd.v rd.r_binary rd.offset rd.env rd.h_static rd.h_match
      (Or.inl rd.h_main_op)
  | lh c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    exact binExt_sext_entry_range i h_sp rd.v rd.r_binary rd.offset rd.env rd.h_static rd.h_match
      (Or.inr (Or.inl rd.h_main_op))
  | lw c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    exact binExt_sext_entry_range i h_sp rd.v rd.r_binary rd.offset rd.env rd.h_static rd.h_match
      (Or.inr (Or.inr rd.h_main_op))
  | lbu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    exact copyb_narrow_entry_range (sailTrace := sailTrace) i 1 (Or.inl rfl) rd.h_width
      rd.h_main_active rd.h_main_op h_sp ia.align
  | lhu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    exact copyb_narrow_entry_range (sailTrace := sailTrace) i 2 (Or.inr rfl) rd.h_width
      rd.h_main_active rd.h_main_op h_sp ia.align
  | ld c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_active := load_b_active_of_mem_message i ia.mem ia.r_mem ia.h_msg
      rd.h_b_src_ind ia.h_mem_wr
    have h_e1_range := trace.loadBMem_entry_chunks_in_range
      (h_mem_present trivial) i rd.h_b_src_ind h_active
    exact copyb_entry_range_of_e1_range (sailTrace := sailTrace) i
      rd.h_main_active rd.h_main_op h_sp h_e1_range
  | lwu c =>
    rw [producerEntry] at he h_ptr ⊢
    have h_sp : (mainTableRowAtOrZero trace.program trace.mainTable i.val).core.store_pc = 0 := by
      have := rd.h_store_pc; simp only [mainOfTable_store_pc] at this; exact this
    have h_active := load_b_active_of_mem_message i ia.mem ia.r_mem ia.h_msg
      rd.h_b_src_ind ia.h_mem_wr
    have h_e1_range := trace.loadBMem_entry_chunks_in_range
      (h_mem_present trivial) i rd.h_b_src_ind h_active
    exact copyb_entry_range_of_e1_range (sailTrace := sailTrace) i
      rd.h_main_active rd.h_main_op h_sp h_e1_range

end ZiskFv.Compliance.PhysicalRegisterWriteRanges
