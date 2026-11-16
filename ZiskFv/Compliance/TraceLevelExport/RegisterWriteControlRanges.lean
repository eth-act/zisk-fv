import ZiskFv.Compliance.TraceLevelExport.Dispatcher
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement

/-!
Actual producer-entry bounds for the four control/immediate register writers.
Only one architectural source start is decoded. In particular, the JALR entry
is the terminal physical row's entry, not the source row's entry. Its expanded
lowering uses the accepted Main PC transition from the ADD to the AND row.
-/

namespace ZiskFv.Compliance.PhysicalRegisterWriteRanges

open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.Main (cMemMessage)
open ZiskFv.Channels.MemoryBus (MemBusMessage)
open ZiskFv.Airs.MemoryBus

set_option maxHeartbeats 2000000

/-- The lane witness is constructed from the actual physical C message. -/
private noncomputable def control_store_pc_witness
    {n : Nat} (trace : AcceptedZiskTrace n)
    (r : Fin trace.mainTable.table.length) :
    StorePcMemoryWitness (mainOfTable trace.program trace.mainTable) r.val
      (eRdAt trace r) where
  row := mainRowWithRomAt trace r
  row_eq := by
    have h := rowAt_mainOfTable trace.program trace.mainTable r
    simpa [mainRowWithRomAt, mainTableRowAtOrZero_get (idx := r)] using h.symm
  rd_write_match := matches_memory_entry_refl _

private theorem control_store_pc_chunks
    {n : Nat} (trace : AcceptedZiskTrace n)
    (r : Fin trace.mainTable.table.length)
    (h_sp : (mainOfTable trace.program trace.mainTable).store_pc r.val = 1)
    (h_val : ((mainOfTable trace.program trace.mainTable).pc r.val
      + (mainOfTable trace.program trace.mainTable).jmp_offset2 r.val).val
        < 4294967296) :
    memory_entry_chunks_in_range (eRdAt trace r) := by
  obtain ⟨h_lo, h_hi⟩ := (control_store_pc_witness trace r).lanes
  simp only [store_pc_lanes_match_lo, h_sp, one_mul, sub_add_cancel] at h_lo
  simp only [store_pc_lanes_match_hi, h_sp, sub_self, zero_mul] at h_hi
  change (memory_entry_lo (eRdAt trace r)).val < 4294967296 ∧
    (memory_entry_hi (eRdAt trace r)).val < 4294967296
  rw [h_lo, h_hi]
  exact ⟨h_val, by decide⟩

private theorem control_val_add_intCast_of_nonneg_lt {a : FGL} {z : Int}
    (h_nonneg : 0 ≤ (a.val : Int) + z)
    (h_lt : (a.val : Int) + z < GL_prime) :
    (a + (z : FGL)).val = ((a.val : Int) + z).toNat := by
  have h_a := a.isLt
  change (a.val + (z : FGL).val) % GL_prime = _
  have h_zv : (z : FGL).val = (z % (GL_prime : Int)).toNat := by
    simp only [Fin.val_intCast]
    norm_cast
  rw [h_zv]
  omega

private theorem control_add_intCast_lt_of_bitvec_lt
    {pc : FGL} {offset : BitVec 64}
    (h_nonneg : 0 ≤ (pc.val : Int) + offset.toInt)
    (h_lt : (pc.val : Int) + offset.toInt < GL_prime)
    (h_bound : (BitVec.ofNat 64 pc.val + offset).toNat < 4294967296) :
    (pc + (offset.toInt : FGL)).val < 4294967296 := by
  rw [control_val_add_intCast_of_nonneg_lt h_nonneg h_lt]
  have h_pc_lt := pc.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : pc.val < 2 ^ 64)] at h_bound
  rw [BitVec.toInt_eq_toNat_bmod] at h_nonneg h_lt ⊢
  have h_off_lt : offset.toNat < 2 ^ 64 := offset.isLt
  simp only [Int.bmod] at h_nonneg h_lt ⊢
  split at h_nonneg <;> split at h_lt <;> split <;> omega

/-- JAL's actual single-row producer entry. Only its existing source range
avoidance is used; no Sail state, register-read agreement, or new range oracle
is needed. -/
theorem jal_actual_producer_entry_range
    {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (c : Claim_jal trace i)
    (rd : RowDecode trace i (.jal c))
    (hAvoid : RowOutsideDefectRegion trace i (.jal c))
    {entry : Interaction.MemoryBusEntry FGL}
    (he : stepRegWrite (stepChannelOutput i (.jal c) rd) = some entry)
    (_h_ptr : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    memory_entry_chunks_in_range entry := by
  have h_write : stepRegWrite (stepChannelOutput i (.jal c) rd) =
      some (eRdLui trace i) := by
    simp [stepRegWrite, stepChannelOutput, eRdLui, MemBusMessage.toEntry]
  have h_entry := Option.some.inj (h_write.symm.trans he)
  rw [← h_entry]
  apply control_store_pc_chunks trace ⟨i.val, trace.mainTable_index i⟩ rd.h_store_pc
  rw [rd.h_jmp2]
  let pc : BitVec 64 := BitVec.ofNat 64 (mainPcVal trace i)
  have h_pc : mainPcVal trace i = pc.toNat := by
    dsimp [pc, mainPcVal]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (Fin.isLt _)
      ZiskFv.PackedBitVec.WidePCNoWrap.GL_prime_lt_pow_64
  have h_link := jalr_link_bridge_scalar
    ((mainOfTable trace.program trace.mainTable).pc i.val)
    ((mainOfTable trace.program trace.mainTable).pc i.val) 4 pc
    rfl h_pc (by rw [← h_pc]; exact hAvoid.h_pc_bound)
  rw [h_link]
  exact hAvoid.h_pc_offset_lt_2_32 pc h_pc

/-- AUIPC retains precisely the existing signed-offset/no-wrap source domain. -/
theorem auipc_actual_producer_entry_range
    {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (c : Claim_auipc trace i)
    (rd : RowDecode trace i (.auipc c))
    (hAvoid : RowOutsideDefectRegion trace i (.auipc c))
    {entry : Interaction.MemoryBusEntry FGL}
    (he : stepRegWrite (stepChannelOutput i (.auipc c) rd) = some entry)
    (_h_ptr : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    memory_entry_chunks_in_range entry := by
  have h_write : stepRegWrite (stepChannelOutput i (.auipc c) rd) =
      some (eRdLui trace i) := by
    simp [stepRegWrite, stepChannelOutput, eRdLui, MemBusMessage.toEntry]
  have h_entry := Option.some.inj (h_write.symm.trans he)
  rw [← h_entry]
  apply control_store_pc_chunks trace ⟨i.val, trace.mainTable_index i⟩ rd.h_store_pc
  rw [rd.h_jmp_offset2_imm]
  apply control_add_intCast_lt_of_bitvec_lt hAvoid.h_target_nonneg hAvoid.h_target_lt
  exact hAvoid.h_pc_offset_lt_2_32
    (BitVec.ofNat 64 (mainPcVal trace i)) (by
      unfold mainPcVal
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.lt_trans (Fin.isLt _)
        ZiskFv.PackedBitVec.WidePCNoWrap.GL_prime_lt_pow_64)

/-- LUI chunks come from the real decoded immediate and Main's internal COPYB
constraints. This needs no PC-range avoidance at all. -/
theorem lui_actual_producer_entry_range
    {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (c : Claim_lui trace i)
    (rd : RowDecode trace i (.lui c))
    {entry : Interaction.MemoryBusEntry FGL}
    (he : stepRegWrite (stepChannelOutput i (.lui c) rd) = some entry)
    (_h_ptr : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    memory_entry_chunks_in_range entry := by
  have h_write : stepRegWrite (stepChannelOutput i (.lui c) rd) =
      some (eRdLui trace i) := by
    simp [stepRegWrite, stepChannelOutput, eRdLui, MemBusMessage.toEntry]
  have h_entry := Option.some.inj (h_write.symm.trans he)
  rw [← h_entry]
  let m := mainOfTable trace.program trace.mainTable
  have h_spec := mainSpec_at_physical trace ⟨i.val, trace.mainTable_index i⟩
  have h_op : m.op i.val = (1 : FGL) := by
    rw [show m.op i.val = ZiskFv.Trusted.OP_COPYB from rd.h_main_op]
    rfl
  have h_lo := h_spec.2.2.2.2.1
  have h_hi := h_spec.2.2.2.2.2.1
  change (1 - m.is_external_op i.val) * m.op i.val *
    (m.b_0 i.val - m.c_0 i.val) = 0 at h_lo
  change (1 - m.is_external_op i.val) * m.op i.val *
    (m.b_1 i.val - m.c_1 i.val) = 0 at h_hi
  rw [rd.h_main_active, h_op] at h_lo h_hi
  simp only [sub_zero, one_mul] at h_lo h_hi
  have h_c0 : m.c_0 i.val = m.b_0 i.val := (sub_eq_zero.mp h_lo).symm
  have h_c1 : m.c_1 i.val = m.b_1 i.val := (sub_eq_zero.mp h_hi).symm
  obtain ⟨h_lane_lo, h_lane_hi⟩ :=
    (control_store_pc_witness trace ⟨i.val, trace.mainTable_index i⟩).lanes
  simp only [store_pc_lanes_match_lo, rd.h_store_pc, zero_mul, zero_add] at h_lane_lo
  simp only [store_pc_lanes_match_hi, rd.h_store_pc, sub_zero, one_mul] at h_lane_hi
  change (memory_entry_lo (eRdLui trace i)).val < 4294967296 ∧
    (memory_entry_hi (eRdLui trace i)).val < 4294967296
  rw [h_lane_lo, h_lane_hi, h_c0, h_c1, rd.h_imm_lo_nat, rd.h_imm_hi_nat]
  constructor
  · exact (c.imm ++ (0 : BitVec 12)).isLt
  · exact Nat.div_lt_of_lt_mul (by
      have h := (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).isLt
      omega)

/-- JALR bounds the entry at `rd.rows.finish = stepProducerRow i (.jalr c) rd`.
The destination guard activates store-PC from actual address/decode evidence.
Both aligned and expanded two-row lowerings are constructive; in the latter
case Main's real transition proves `pc(finish) = pc(start) + 1`, and the final
row's decoded offset `3` therefore stores the original link `pc(start) + 4`.
No equality between the start and finish C messages is assumed. -/
theorem jalr_actual_producer_entry_range
    {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (c : Claim_jalr trace i)
    (rd : RowDecode trace i (.jalr c))
    (hAvoid : RowOutsideDefectRegion trace i (.jalr c))
    {entry : Interaction.MemoryBusEntry FGL}
    (he : stepRegWrite (stepChannelOutput i (.jalr c) rd) = some entry)
    (h_ptr : Transpiler.wrap_to_regidx entry.ptr ≠ 0) :
    memory_entry_chunks_in_range entry := by
  have h_write : stepRegWrite (stepChannelOutput i (.jalr c) rd) =
      some (eRdAt trace rd.rows.finish) := by
    simp [stepRegWrite, stepChannelOutput, eRdAt, MemBusMessage.toEntry]
  have h_entry := Option.some.inj (h_write.symm.trans he)
  rw [← h_entry] at h_ptr ⊢
  let m := mainOfTable trace.program trace.mainTable
  let finish := rd.rows.finish
  have h_rd_nonzero : (regidx_to_fin c.rd).val ≠ 0 := by
    intro h_zero
    apply h_ptr
    have h_addr := (RomDecodeBinding.mainAddressSpec_at trace finish).2.2.1
    change Transpiler.wrap_to_regidx (mainRowWithRomAt trace finish).rom.addr2 = 0
    rw [h_addr, rd.h_store_ind, rd.h_store_offset, if_pos h_zero]
    simp [Transpiler.wrap_to_regidx]
  have h_store_pc : m.store_pc finish.val = 1 := by
    simpa [ZiskFv.AirsClean.boolF, h_rd_nonzero] using rd.h_store_pc
  -- This is a real register-store source, not an assumed active C selector.
  have _h_store_reg : (mainRowWithRomAt trace finish).rom.store_reg = 1 := by
    simpa [ZiskFv.AirsClean.boolF, h_rd_nonzero] using rd.h_store_reg
  apply control_store_pc_chunks trace finish h_store_pc
  let pc : BitVec 64 := BitVec.ofNat 64 (mainPcVal trace i)
  have h_pc : mainPcVal trace i = pc.toNat := by
    dsimp [pc, mainPcVal]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    exact Nat.lt_trans (Fin.isLt _)
      ZiskFv.PackedBitVec.WidePCNoWrap.GL_prime_lt_pow_64
  have h_pc_bound : pc.toNat < GL_prime - 4 := by
    rw [← h_pc]
    exact hAvoid.h_pc_bound
  have h_link : (m.pc finish.val + m.jmp_offset2 finish.val).val =
      (pc + 4#64).toNat := by
    rcases rd.rows.lowering with h_aligned | h_unaligned
    · obtain ⟨h_start_finish, _⟩ := h_aligned
      have hsf : rd.rows.start.val = finish.val := congrArg Fin.val h_start_finish
      have h_finish_jmp2 : m.jmp_offset2 finish.val = 4 := by
        rcases rd.h_jmp2 with h | h
        · exact h.2
        · rw [hsf] at h
          omega
      have h_finish_pc : (m.pc finish.val).val = pc.toNat := by
        rw [← hsf, rd.rows.architectural_start]
        exact h_pc
      exact jalr_link_bridge_scalar (m.pc finish.val) (m.pc finish.val)
        (m.jmp_offset2 finish.val) pc (by rw [h_finish_jmp2]) h_finish_pc h_pc_bound
    · have h_adj := h_unaligned.1
      have h_start_flag := h_unaligned.2.2.2.2.2.1
      have h_start_set_pc := h_unaligned.2.2.2.2.2.2.1
      have h_start_jmp2 := h_unaligned.2.2.2.2.2.2.2.1
      have h_finish_jmp2 : m.jmp_offset2 finish.val = 3 := by
        rcases rd.h_jmp2 with h | h
        · rw [h.1] at h_adj
          omega
        · exact h.2
      have h_start_pc : (m.pc rd.rows.start.val).val = pc.toNat := by
        rw [rd.rows.architectural_start]
        exact h_pc
      have h_seg := trace.mainTable_fixed.segment_l1_succ rd.rows.start.val
        (by simpa [h_adj] using finish.isLt)
      have h_hand := trace.mainTransition_to_next_pc rd.rows.start.val
        (by simpa [h_adj] using finish.isLt) h_seg
      have h_pc_step := ZiskFv.Airs.Main.pc_handshake_branch m rd.rows.start.val
        (m.pc (rd.rows.start.val + 1)) h_start_set_pc h_hand
      rw [h_start_flag, h_start_jmp2] at h_pc_step
      simp only [zero_mul, add_zero] at h_pc_step
      have h_total : m.pc finish.val + m.jmp_offset2 finish.val =
          m.pc rd.rows.start.val + 4 := by
        rw [h_finish_jmp2]
        have h_finish_pc : m.pc finish.val = m.pc rd.rows.start.val + 1 := by
          simpa [h_adj] using h_pc_step
        rw [h_finish_pc]
        ring
      exact jalr_link_bridge_scalar (m.pc rd.rows.start.val) (m.pc finish.val)
        (m.jmp_offset2 finish.val) pc h_total h_start_pc h_pc_bound
  rw [h_link]
  exact hAvoid.h_pc_offset_lt_2_32 pc h_pc

end ZiskFv.Compliance.PhysicalRegisterWriteRanges
