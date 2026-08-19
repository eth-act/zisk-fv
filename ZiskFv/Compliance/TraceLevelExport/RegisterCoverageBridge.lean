import ZiskFv.Compliance.RegisterPushCounting
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding

/-!
# The register coverage bridge — #330 S3

`a_columns_of_bootWalk` says the a-columns of a register-reading Main row either are `(0, 0)` or
match a c-slot on the backward walk. `RegAgree` says the ZisK register file and the Sail registers
agree at every step. This module closes the gap: it connects the walk's c-slot value to the
register file, proving that the a-columns equal the lane decomposition of the register value.
-/

namespace ZiskFv.Compliance

open Air.Flat (Table)
open ZiskFv.AirsClean.FullEnsemble (mainTableRowAtOrZero mainTableRowAtOrZero_get)
open ZiskFv.AirsClean.Main (MainRowWithRom cMemMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep RegSupplies
  readTimestamp_lt_of_regSupplies)

variable {n : Nat}

/-! ## Timestamp monotonicity along `AnswersRegPre` chains

One backward step strictly decreases the read timestamp. -/

theorem timestamp_val_lt_of_answersRegPre_active (trace : AcceptedZiskTrace n)
    {p q : RegWalkStep}
    (h_ap : IsActiveWitnessMainRow trace p) (h_aq : IsActiveWitnessMainRow trace q)
    (h_link : RegWalkStep.AnswersRegPre p q) :
    q.timestamp.val < p.timestamp.val := by
  have h_ts : q.2.readTimestamp q.1 = p.2.prevStep p.1 := by
    have := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_link
    simp [Instantiation.RegSlot.readMessage_timestamp,
      Instantiation.RegSlot.regPreMessage_timestamp] at this
    exact this
  exact readTimestamp_lt_of_regSupplies h_ts.symm
    (regSlot_descent_of_witnessMainRow trace h_ap)
    (regSlot_timestamp_bound_of_witnessMainRow trace h_aq)

/-! ## Elements on an `AnswersRegPre` chain have timestamps bounded by the head. -/

theorem timestamp_val_le_head_of_mem_chain (trace : AcceptedZiskTrace n)
    {path : List RegWalkStep} (h_ne : path ≠ [])
    (h_act : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.AnswersRegPre path)
    {x : RegWalkStep} (hx : x ∈ path) :
    x.timestamp.val ≤ (path.head h_ne).timestamp.val := by
  induction path with
  | nil => contradiction
  | cons a rest ih =>
      simp only [List.head_cons]
      rcases List.mem_cons.mp hx with rfl | hx_rest
      · exact Nat.le_refl _
      · cases rest with
        | nil => contradiction
        | cons b tl =>
            have h_chain_rest : List.IsChain RegWalkStep.AnswersRegPre (b :: tl) :=
              (List.isChain_cons.mp h_chain).2
            have h_le_rest := ih (List.cons_ne_nil b tl)
              (fun q hq => h_act q (List.mem_cons_of_mem _ hq))
              h_chain_rest hx_rest
            have h_link : RegWalkStep.AnswersRegPre a b :=
              (List.isChain_cons_cons.mp h_chain).1
            have h_lt := timestamp_val_lt_of_answersRegPre_active trace
              (h_act a List.mem_cons_self)
              (h_act b (List.mem_cons_of_mem _ List.mem_cons_self))
              h_link
            simp only [List.head_cons] at h_le_rest
            omega

theorem not_mem_chain_of_timestamp_ge (trace : AcceptedZiskTrace n)
    {path : List RegWalkStep} (h_ne : path ≠ [])
    (h_act : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.AnswersRegPre path)
    {x : RegWalkStep} (h_ne_head : x ≠ path.head h_ne)
    (h_ts : (path.head h_ne).timestamp.val ≤ x.timestamp.val) :
    x ∉ path := by
  intro hx
  have h_le := timestamp_val_le_head_of_mem_chain trace h_ne h_act h_chain hx
  have h_eq : x = path.head h_ne := by
    by_contra h_ne'
    cases path with
    | nil => contradiction
    | cons a rest =>
        simp only [List.head_cons] at h_ts h_le h_ne_head h_ne'
        rcases List.mem_cons.mp hx with rfl | hx_rest
        · exact h_ne' rfl
        · cases rest with
          | nil => contradiction
          | cons b tl =>
              have h_link := (List.isChain_cons_cons.mp h_chain).1
              have h_lt := timestamp_val_lt_of_answersRegPre_active trace
                (h_act a List.mem_cons_self)
                (h_act b (List.mem_cons_of_mem _ List.mem_cons_self))
                h_link
              have h_le_rest := timestamp_val_le_head_of_mem_chain trace
                (List.cons_ne_nil b tl)
                (fun q hq => h_act q (List.mem_cons_of_mem _ hq))
                ((List.isChain_cons.mp h_chain).2)
                hx_rest
              simp only [List.head_cons] at h_le_rest
              omega
  exact h_ne_head h_eq

/-! ## stepRegWrite classification

Every arm's register write is either `none` (branches, FENCE, stores) or
`some (toEntry(cMemMessage(mainTableRowAtOrZero j), 1, 1))` where `j` is
the step's producer row. -/

theorem stepRegWrite_eq_none_or_cMemMessage
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) :
    stepRegWrite (stepChannelOutput i zs rd) = none
    ∨ stepRegWrite (stepChannelOutput i zs rd) =
        some (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (cMemMessage (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable
            (stepProducerRow i zs rd)))
          1 1) := by
  cases zs <;>
    first
      | exact Or.inl rfl
      | exact Or.inr rfl

theorem stepRegWrite_eq_none_or_cMemMessage_at_i
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (rd : RowDecode ziskTrace i zs) :
    stepRegWrite (stepChannelOutput i zs rd) = none
    ∨ ∃ j, stepRegWrite (stepChannelOutput i zs rd) =
        some (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (cMemMessage (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable j))
          1 1)
      ∧ (j = i.val ∨ j = stepProducerRow i zs rd) := by
  cases zs with
  | jalr c => exact Or.inr ⟨_, rfl, Or.inr rfl⟩
  | _ => first | exact Or.inl rfl | exact Or.inr ⟨_, rfl, Or.inl rfl⟩

/-! ## Step-index bridge

`IsActiveWitnessMainRow trace q` gives a row in SOME Main table. By `main_table_unique`,
that table is `trace.mainTable`. The row's index gives a step index. -/

theorem isActiveWitnessMainRow_eq_mainTableRow {n : Nat} (trace : AcceptedZiskTrace n)
    {q : RegWalkStep} (h : IsActiveWitnessMainRow trace q) :
    ∃ index : ℕ, index < trace.mainTable.table.length ∧
      q.1 = mainTableRowAtOrZero trace.program trace.mainTable index := by
  obtain ⟨table, h_table, h_component, index, h_index, h_eq, _⟩ := h
  have h_same : table = trace.mainTable :=
    main_table_unique trace.witness h_table trace.mainTable_mem h_component trace.mainTable_component
  subst h_same
  exact ⟨index, h_index, h_eq⟩

/-! ## Range constraints on cMemMessage entries

The memory-bus entry `(cMemMessage row).toEntry 1 1` carries the register write
value.  For `lane_lo_entryRegValue` to bridge from the entry to the register
file, the entry must satisfy `memory_entry_chunks_in_range` (each 32-bit chunk
has `.val < 2^32`) and `memory_entry_packed_no_wrap` (the packed sum is below
`GL_prime`).

Derivation path (not yet reduced to kernel terms):
* `store_pc = 0` → `value_0 = c_0`, `value_1 = c_1`.  The op-bus balance
  (`trace.channels_balanced` on the OpBusChannel) matches the Main row to a
  provider circuit row whose `c_lo` / `c_hi` are range-checked to 32 bits via
  `ComponentSpecFacts` (e.g. `c_chunks_in_range_of_component_spec_facts`).
* `store_pc = 1` → `value_0 = pc + jmp_offset2`, `value_1 = 0`.  `0` is
  trivially < 2^32.  `(pc + jmp_offset2).val < 2^32` follows from the PC being
  a 32-bit address (the `MainSequentialPcDomain` / `h_pc_offset_lt_2_32`
  domain bounds).
* `packed_no_wrap` follows from `chunks_in_range` since
  `a + b * 2^32 < 2^32 + (2^32 - 1) * 2^32 = 2^64 - 2^32 < GL_prime`. -/

/-! ## Range constraint on register-write entries

The register-write entry `(cMemMessage row).toEntry 1 1` must satisfy chunk-range
and packed-no-wrap for `lane_lo_entryRegValue`. The derivation goes per-arm through
the op-bus balance to each provider's `ComponentSpecFacts` (already used by the
construction proofs, e.g. `c_chunks_in_range_of_component_spec_facts`). This is
stated as a hypothesis `h_entry_range` on `a_column_eq_lane_lo_sail_xreg` and
discharged per-row in the `stepSound_of_programDecodes` induction where the
specific arm's provider match is available. -/

/-! ## No-writes lemma from boot walk

The boot walk's chain gives the register's complete write history:
between any two consecutive chain elements, no write to that register
occurred. This follows from the channel balance bijection. -/

theorem ziskRegFile_eq_lane_lo_of_bootWalk_zero
    {n : Nat} (_trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep _trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode _trace i (ziskStep i))
    (k : ℕ) (_hk : k < n)
    (r : Fin 32) (_hr : r ≠ 0)
    (h_no_writes : ∀ m, m < k → ¬ StepWritesReg ziskStep rowDecodes m r) :
    (0 : FGL) = ZiskFv.Trusted.lane_lo (ziskRegFile ziskStep rowDecodes k r) := by
  have h_eq := ziskRegFile_eq_of_no_writes_between ziskStep rowDecodes r 0 k (Nat.zero_le k)
    (fun m _ hm' => h_no_writes m hm')
  rw [h_eq, ziskRegFile_zero]
  simp [ZiskFv.Trusted.lane_lo]

theorem ziskRegFile_eq_lane_hi_of_bootWalk_zero
    {n : Nat} (_trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep _trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode _trace i (ziskStep i))
    (k : ℕ) (_hk : k < n)
    (r : Fin 32) (_hr : r ≠ 0)
    (h_no_writes : ∀ m, m < k → ¬ StepWritesReg ziskStep rowDecodes m r) :
    (0 : FGL) = ZiskFv.Trusted.lane_hi (ziskRegFile ziskStep rowDecodes k r) := by
  have h_eq := ziskRegFile_eq_of_no_writes_between ziskStep rowDecodes r 0 k (Nat.zero_le k)
    (fun m _ hm' => h_no_writes m hm')
  rw [h_eq, ziskRegFile_zero]
  simp [ZiskFv.Trusted.lane_hi]

theorem cMemMessage_value_eq_lane_lo_of_bootWalk_supplier
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (q : RegWalkStep)
    (h_active : IsActiveWitnessMainRow trace q)
    (h_slot_c : q.2 = Instantiation.RegSlot.c)
    (h_ptr : Transpiler.wrap_to_regidx (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr = r)
    (h_timestamp_lt : q.timestamp.val < (3 + 4 * k : ℕ))
    (h_no_writes_above : ∀ m, q.timestamp.val < 3 + 4 * m → m < k →
      ¬ StepWritesReg ziskStep rowDecodes m r)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_entry_range : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
          = some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) →
        ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)
        ∧ ZiskFv.Airs.MemoryBus.memory_entry_packed_no_wrap
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    (ZiskFv.AirsClean.Main.cMemMessage q.1).value_0 =
      ZiskFv.Trusted.lane_lo (ziskRegFile ziskStep rowDecodes k r) := by
  obtain ⟨j, h_j_lt_table, h_row_eq⟩ := isActiveWitnessMainRow_eq_mainTableRow trace h_active
  have h_q_ts_val : q.timestamp.val = 3 + 4 * j := by
    have h_ms := mainRowAt_main_step trace.mainTable_component h_j_lt_table
    have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_j_lt_table
    have : q.timestamp = (3 : FGL) + (↑j : FGL) * 4 := by
      simp only [Instantiation.RegWalkStep.timestamp, h_slot_c,
        Instantiation.RegSlot.readTimestamp, h_row_eq, h_ms]
    rw [this]
    exact slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap
  have h_j_lt_n : j < n := by omega
  have h_j_lt_k : j < k := by omega
  have h_write : stepRegWrite (stepChannelOutput ⟨j, h_j_lt_n⟩ (ziskStep ⟨j, h_j_lt_n⟩)
      (rowDecodes ⟨j, h_j_lt_n⟩))
    = some ((ZiskFv.AirsClean.Main.cMemMessage
      (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1) := by
    rcases stepRegWrite_eq_none_or_cMemMessage_at_i ⟨j, h_j_lt_n⟩
      (ziskStep ⟨j, h_j_lt_n⟩) (rowDecodes ⟨j, h_j_lt_n⟩) with h_none | ⟨j', h_some, h_j'⟩
    · -- Derive store_reg = 1 from the active c-slot, then contradict h_none.
      have h_sr : (mainTableRowAtOrZero trace.program trace.mainTable j).rom.store_reg = 1 := by
        obtain ⟨_, _, _, _, _, h_eq_row, h_sel⟩ := h_active
        rw [h_slot_c] at h_sel
        simp only [Instantiation.RegSlot.selector] at h_sel
        rwa [← h_row_eq]
      exact absurd h_none (h_stepRegWrite_consistent ⟨j, h_j_lt_n⟩ h_sr).1
    · -- Both sub-cases reduce to stepProducerRow = j via h_stepRegWrite_consistent.
      have h_sr : (mainTableRowAtOrZero trace.program trace.mainTable j).rom.store_reg = 1 := by
        obtain ⟨_, _, _, _, _, h_eq_row, h_sel⟩ := h_active
        rw [h_slot_c] at h_sel
        simp only [Instantiation.RegSlot.selector] at h_sel
        rwa [← h_row_eq]
      have h_pr := (h_stepRegWrite_consistent ⟨j, h_j_lt_n⟩ h_sr).2
      rcases h_j' with rfl | rfl
      · exact h_some
      · rw [h_pr] at h_some; exact h_some
  have h_ptr_eq : Transpiler.wrap_to_regidx
      ((ZiskFv.AirsClean.Main.cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1).ptr = r := by
    rw [← h_row_eq]; exact h_ptr
  have h_regFile_succ := ziskRegFile_succ_of_writes ziskStep rowDecodes j r h_j_lt_n
    _ h_write h_ptr_eq
  have h_no_writes : ∀ m, j + 1 ≤ m → m < k → ¬ StepWritesReg ziskStep rowDecodes m r :=
    fun m hm hm' => h_no_writes_above m (by omega) hm'
  have h_regFile_k := ziskRegFile_eq_of_no_writes_between ziskStep rowDecodes r (j + 1) k
    (by omega) h_no_writes
  have ⟨h_chunks, h_no_wrap⟩ := h_entry_range ⟨j, h_j_lt_n⟩ h_write
  have h_lane := lane_lo_entryRegValue
    ((ZiskFv.AirsClean.Main.cMemMessage
      (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1)
    h_chunks h_no_wrap
  rw [h_regFile_k, h_regFile_succ, ← h_row_eq]
  rw [← h_row_eq] at h_lane
  simpa [ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] using h_lane.symm

theorem cMemMessage_value_eq_lane_hi_of_bootWalk_supplier
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (q : RegWalkStep)
    (h_active : IsActiveWitnessMainRow trace q)
    (h_slot_c : q.2 = Instantiation.RegSlot.c)
    (h_ptr : Transpiler.wrap_to_regidx (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr = r)
    (h_timestamp_lt : q.timestamp.val < (3 + 4 * k : ℕ))
    (h_no_writes_above : ∀ m, q.timestamp.val < 3 + 4 * m → m < k →
      ¬ StepWritesReg ziskStep rowDecodes m r)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_entry_range : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
          = some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) →
        ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)
        ∧ ZiskFv.Airs.MemoryBus.memory_entry_packed_no_wrap
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    (ZiskFv.AirsClean.Main.cMemMessage q.1).value_1 =
      ZiskFv.Trusted.lane_hi (ziskRegFile ziskStep rowDecodes k r) := by
  obtain ⟨j, h_j_lt_table, h_row_eq⟩ := isActiveWitnessMainRow_eq_mainTableRow trace h_active
  have h_q_ts_val : q.timestamp.val = 3 + 4 * j := by
    have h_ms := mainRowAt_main_step trace.mainTable_component h_j_lt_table
    have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_j_lt_table
    have : q.timestamp = (3 : FGL) + (↑j : FGL) * 4 := by
      simp only [Instantiation.RegWalkStep.timestamp, h_slot_c,
        Instantiation.RegSlot.readTimestamp, h_row_eq, h_ms]
    rw [this]
    exact slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap
  have h_j_lt_n : j < n := by omega
  have h_j_lt_k : j < k := by omega
  have h_write : stepRegWrite (stepChannelOutput ⟨j, h_j_lt_n⟩ (ziskStep ⟨j, h_j_lt_n⟩)
      (rowDecodes ⟨j, h_j_lt_n⟩))
    = some ((ZiskFv.AirsClean.Main.cMemMessage
      (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1) := by
    rcases stepRegWrite_eq_none_or_cMemMessage_at_i ⟨j, h_j_lt_n⟩
      (ziskStep ⟨j, h_j_lt_n⟩) (rowDecodes ⟨j, h_j_lt_n⟩) with h_none | ⟨j', h_some, h_j'⟩
    · have h_sr : (mainTableRowAtOrZero trace.program trace.mainTable j).rom.store_reg = 1 := by
        obtain ⟨_, _, _, _, _, h_eq_row, h_sel⟩ := h_active
        rw [h_slot_c] at h_sel
        simp only [Instantiation.RegSlot.selector] at h_sel
        rwa [← h_row_eq]
      exact absurd h_none (h_stepRegWrite_consistent ⟨j, h_j_lt_n⟩ h_sr).1
    · have h_sr : (mainTableRowAtOrZero trace.program trace.mainTable j).rom.store_reg = 1 := by
        obtain ⟨_, _, _, _, _, h_eq_row, h_sel⟩ := h_active
        rw [h_slot_c] at h_sel
        simp only [Instantiation.RegSlot.selector] at h_sel
        rwa [← h_row_eq]
      have h_pr := (h_stepRegWrite_consistent ⟨j, h_j_lt_n⟩ h_sr).2
      rcases h_j' with rfl | rfl
      · exact h_some
      · rw [h_pr] at h_some; exact h_some
  have h_ptr_eq : Transpiler.wrap_to_regidx
      ((ZiskFv.AirsClean.Main.cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1).ptr = r := by
    rw [← h_row_eq]; exact h_ptr
  have h_regFile_succ := ziskRegFile_succ_of_writes ziskStep rowDecodes j r h_j_lt_n
    _ h_write h_ptr_eq
  have h_no_writes : ∀ m, j + 1 ≤ m → m < k → ¬ StepWritesReg ziskStep rowDecodes m r :=
    fun m hm hm' => h_no_writes_above m (by omega) hm'
  have h_regFile_k := ziskRegFile_eq_of_no_writes_between ziskStep rowDecodes r (j + 1) k
    (by omega) h_no_writes
  have ⟨h_chunks, h_no_wrap⟩ := h_entry_range ⟨j, h_j_lt_n⟩ h_write
  have h_lane := lane_hi_entryRegValue
    ((ZiskFv.AirsClean.Main.cMemMessage
      (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1)
    h_chunks h_no_wrap
  rw [h_regFile_k, h_regFile_succ, ← h_row_eq]
  rw [← h_row_eq] at h_lane
  simpa [ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] using h_lane.symm

/-! ## Ptr propagation along `AnswersRegPre` chains

The register address (ptr) is constant along a backward walk: every element reads
the same register that the head targets. This follows from `AddressSpec` (the
address-placement constraint) together with the fact that `mem_op = 3` on every
non-head element forces the indirect flag to zero. -/

private theorem fgl_zero_or_one_of_bool {x : FGL} (h : x * (1 - x) = 0) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

/-- When an active witness row's read message has `mem_op = 3` (register read),
    the read address and the register-pre address agree. For the a-slot this is
    unconditional from `AddressSpec`; for b and c it follows because `mem_op = 3`
    forces the indirect flag to zero. -/
private theorem readMessage_ptr_eq_regPreMessage_ptr_of_memop3
    {n : Nat} (trace : AcceptedZiskTrace n)
    {p : RegWalkStep} (h_active : IsActiveWitnessMainRow trace p)
    (h_memop : (p.2.readMessage p.1).mem_op = 3) :
    (p.2.readMessage p.1).ptr = (p.2.regPreMessage p.1).ptr := by
  obtain ⟨j, h_j_lt, h_row_eq⟩ := isActiveWitnessMainRow_eq_mainTableRow trace h_active
  have h_addr := RomDecodeBinding.mainAddressSpec_at trace ⟨j, h_j_lt⟩
  obtain ⟨_, _, _, _, _, _, _, _, h_bsm, h_stm, h_sti, h_bsi, _, h_bsr, h_str⟩ :=
    RomDecodeBinding.mainRow_flags_boolean trace ⟨j, h_j_lt⟩
  obtain ⟨p_row, p_slot⟩ := p
  rw [h_row_eq] at h_memop ⊢
  cases p_slot with
  | a =>
    simp only [Instantiation.RegSlot.readMessage, Instantiation.RegSlot.regPreMessage,
      ZiskFv.AirsClean.Main.aMemMessage, ZiskFv.AirsClean.Main.aRegPreMessage]
    exact h_addr.1
  | b =>
    simp only [Instantiation.RegSlot.readMessage, Instantiation.RegSlot.regPreMessage,
      ZiskFv.AirsClean.Main.bMemMessage, ZiskFv.AirsClean.Main.bRegPreMessage] at h_memop ⊢
    rw [h_addr.2.1]
    suffices h_bi : (mainTableRowAtOrZero trace.program trace.mainTable j).rom.b_src_ind = 0 by
      rw [h_bi, zero_mul, add_zero]
    rcases fgl_zero_or_one_of_bool h_bsi with h | h
    · exact h
    · exfalso
      rcases fgl_zero_or_one_of_bool h_bsm with hm | hm <;>
        rcases fgl_zero_or_one_of_bool h_bsr with hr | hr <;>
        (simp only [h, hm, hr] at h_memop; revert h_memop; decide)
  | c =>
    simp only [Instantiation.RegSlot.readMessage, Instantiation.RegSlot.regPreMessage,
      ZiskFv.AirsClean.Main.cMemMessage, ZiskFv.AirsClean.Main.cRegPreMessage] at h_memop ⊢
    rw [h_addr.2.2.1]
    suffices h_si : (mainTableRowAtOrZero trace.program trace.mainTable j).rom.store_ind = 0 by
      rw [h_si, zero_mul, add_zero]
    rcases fgl_zero_or_one_of_bool h_sti with h | h
    · exact h
    · exfalso
      rcases fgl_zero_or_one_of_bool h_stm with hm | hm <;>
        rcases fgl_zero_or_one_of_bool h_str with hr | hr <;>
        (simp only [h, hm, hr] at h_memop; revert h_memop; decide)

/-- Every element (except the head) of an `AnswersRegPre` chain of active witness
    rows reads the same register that the head's register-pre message targets. -/
theorem bootWalk_head_ptr {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (path : List RegWalkStep) (p : RegWalkStep),
      path.head? = some p →
      List.IsChain RegWalkStep.AnswersRegPre path →
      (∀ q ∈ path, IsActiveWitnessMainRow trace q) →
      ∀ q ∈ path, q ≠ p →
        (q.2.readMessage q.1).ptr = (p.2.regPreMessage p.1).ptr := by
  intro path
  induction path with
  | nil => intro _ h; simp at h
  | cons a rest ih =>
    intro p h_head h_chain h_sites q h_q h_neq
    have h_p : a = p := by simpa using h_head
    subst h_p
    have h_rest : q ∈ rest := by
      rcases List.mem_cons.mp h_q with rfl | h
      · exact absurd rfl h_neq
      · exact h
    cases rest with
    | nil => exact absurd h_rest List.not_mem_nil
    | cons b rest' =>
      obtain ⟨h_link, h_chain'⟩ := List.isChain_cons_cons.mp h_chain
      have h_link_ptr : (b.2.readMessage b.1).ptr = (a.2.regPreMessage a.1).ptr :=
        congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.ptr h_link
      have h_b_memop : (b.2.readMessage b.1).mem_op = 3 := by
        rw [congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.mem_op h_link]
        cases a.2 <;> rfl
      have h_b_inner := readMessage_ptr_eq_regPreMessage_ptr_of_memop3 trace
        (h_sites b (List.mem_cons_of_mem _ List.mem_cons_self)) h_b_memop
      have h_b_eq : (b.2.regPreMessage b.1).ptr = (a.2.regPreMessage a.1).ptr :=
        h_b_inner ▸ h_link_ptr
      rcases List.mem_cons.mp h_rest with rfl | h_deeper
      · exact h_link_ptr
      · by_cases h_eq_b : q = b
        · exact h_eq_b ▸ h_link_ptr
        · exact (ih b rfl h_chain'
            (fun r hr => h_sites r (List.mem_cons_of_mem _ hr))
            q (List.mem_cons_of_mem _ h_deeper) h_eq_b).trans h_b_eq

/-! ## Strengthened boot walk head value

`bootWalk_head_value` gives two cases but does not say whether the first case excludes
c-slots from the path or whether the second case's q is the first c-slot. This
strengthened version adds those facts, which the chain-completeness argument needs. -/

/-- In the first case, no element after the head has slot `.c`. In the second case,
    every c-slot on the path (other than the head) has timestamp ≤ q's timestamp,
    making q the closest c-slot to the head. -/
theorem bootWalk_head_value_strong {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (path : List RegWalkStep) (p last : RegWalkStep),
      path.head? = some p → path.getLast? = some last →
      (∀ q ∈ path, IsActiveWitnessMainRow trace q) →
      List.IsChain RegWalkStep.AnswersRegPre path →
      BootAnchoredStep trace last →
      ((p.2.regPreMessage p.1).value_0 = 0 ∧ (p.2.regPreMessage p.1).value_1 = 0
          ∧ ∀ q ∈ path, q ≠ p → q.2 ≠ RegSlot.c)
        ∨ ∃ q ∈ path, q.2 = RegSlot.c
            ∧ (p.2.regPreMessage p.1).value_0 = (q.2.readMessage q.1).value_0
            ∧ (p.2.regPreMessage p.1).value_1 = (q.2.readMessage q.1).value_1
            ∧ ∀ q' ∈ path, q' ≠ p → q'.2 = RegSlot.c →
                q'.timestamp.val ≤ q.timestamp.val := by
  intro path
  induction path with
  | nil => intro p last h_head; simp at h_head
  | cons a rest ih =>
      intro p last h_head h_last h_sites h_chain h_boot
      have h_p : a = p := by simpa using h_head
      subst h_p
      match rest with
      | [] =>
          have h_last' : a = last := by simpa using h_last
          subst h_last'
          obtain ⟨btbl, _h_btbl, _h_bcomp, br, _h_br, h_eq⟩ := h_boot
          exact Or.inl ⟨congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_eq,
            congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_eq,
            fun q hq h_ne => absurd (List.mem_singleton.mp hq) h_ne⟩
      | b :: rest' =>
          obtain ⟨h_link, h_chain'⟩ := List.isChain_cons_cons.mp h_chain
          have h_link' : b.2.readMessage b.1 = a.2.regPreMessage a.1 := h_link
          have h_sites_rest : ∀ q ∈ (b :: rest'), IsActiveWitnessMainRow trace q :=
            fun q hq => h_sites q (List.mem_cons_of_mem _ hq)
          by_cases h_c : b.2 = RegSlot.c
          · -- b is the first c-slot: return second case with b
            refine Or.inr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, h_c,
              (congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_link').symm,
              (congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_link').symm,
              fun q' h_q' h_ne' h_c' => ?_⟩
            rcases List.mem_cons.mp h_q' with rfl | h_rest
            · exact absurd rfl h_ne'
            · exact timestamp_val_le_head_of_mem_chain trace (List.cons_ne_nil b rest')
                h_sites_rest h_chain' h_rest
          · obtain ⟨h_v0, h_v1⟩ := readMessage_value_eq_regPre_of_ne_c h_c b.1
            have h_a0 : (a.2.regPreMessage a.1).value_0 = (b.2.regPreMessage b.1).value_0 := by
              rw [← h_v0, ← congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_link']
            have h_a1 : (a.2.regPreMessage a.1).value_1 = (b.2.regPreMessage b.1).value_1 := by
              rw [← h_v1, ← congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_link']
            rcases ih b last rfl (by simpa using h_last) h_sites_rest h_chain' h_boot with
              ⟨h0, h1, h_nc⟩ | ⟨q, h_q, h_qc, h_q0, h_q1, h_max⟩
            · exact Or.inl ⟨h_a0.trans h0, h_a1.trans h1, fun q hq h_ne => by
                rcases List.mem_cons.mp hq with rfl | h_rest
                · exact absurd rfl h_ne
                · rcases List.mem_cons.mp h_rest with rfl | h_deeper
                  · exact h_c
                  · by_cases h_qb : q = b
                    · exact h_qb ▸ h_c
                    · exact h_nc q (List.mem_cons_of_mem _ h_deeper) h_qb⟩
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ h_q, h_qc,
                h_a0.trans h_q0, h_a1.trans h_q1, fun q' h_q' h_ne' h_c' => by
                rcases List.mem_cons.mp h_q' with rfl | h_rest
                · exact absurd rfl h_ne'
                · rcases List.mem_cons.mp h_rest with rfl | h_deeper
                  · exact absurd h_c' h_c
                  · by_cases h_q'b : q' = b
                    · exact absurd (h_q'b ▸ h_c') h_c
                    · exact h_max q' (List.mem_cons_of_mem _ h_deeper) h_q'b h_c'⟩

/-- A boot-anchored step's `regPreMessage.ptr` has `.val < 32`, because the
    RegisterBoundary fixed column `reg` is `natF(index + 1)` with `index < 31`. -/
private theorem bootAnchoredStep_ptr_val_lt {n : Nat} (trace : AcceptedZiskTrace n)
    {p : RegWalkStep} (h : BootAnchoredStep trace p) :
    (p.2.regPreMessage p.1).ptr.val < 32 := by
  obtain ⟨btbl, h_btbl, h_bcomp, br, h_br, h_eq⟩ := h
  rw [h_eq]
  simp only [ZiskFv.AirsClean.RegisterBoundary.bootMessage]
  -- Destructure btbl and subst the component (same pattern as pullCount proof)
  cases btbl with
  | mk component rawRows data raw_uniform_width fixed_domain =>
  change component = ZiskFv.AirsClean.RegisterBoundary.component at h_bcomp
  subst component
  -- Now the table reduces definitionally
  have h_tableRows : (Air.Flat.Table.table ⟨ZiskFv.AirsClean.RegisterBoundary.component,
      rawRows, data, raw_uniform_width, fixed_domain⟩) =
    rawRows.mapIdx fun idx raw =>
      ZiskFv.AirsClean.RegisterBoundary.registerBoundaryFixedColumns.materialize idx raw := rfl
  rw [h_tableRows] at h_br
  obtain ⟨idx, h_idx_lt, h_br_eq⟩ := List.mem_mapIdx.mp h_br
  -- The environment reduces too
  show (eval (Environment.fromArray br data)
    ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reg.val < 32
  rw [show br = ZiskFv.AirsClean.RegisterBoundary.registerBoundaryFixedColumns.materialize idx
      rawRows[idx] from h_br_eq.symm]
  rw [ZiskFv.AirsClean.RegisterBoundary.reg_of_materialize]
  -- Goal: (registerBoundaryFixedColumns.fixedAt 0 idx).val < 32
  simp only [Air.Flat.IndexedFixedColumns.fixedAt,
    ZiskFv.AirsClean.RegisterBoundary.registerBoundaryFixedColumns,
    ZiskFv.AirsClean.RegisterBoundary.registerBoundaryFixedValues,
    ZiskFv.AirsClean.RegisterBoundary.registerBoundaryCapacity]
  simp only [show (0 : ℕ) < 1 from by omega, dite_true]
  rw [Fin.val_natCast]
  have : (idx % 31 + 1) % 18446744069414584321 = idx % 31 + 1 := Nat.mod_eq_of_lt (by omega)
  rw [this]; omega

/-- The register-pre ptr is constant along an `AnswersRegPre` chain of active
    witness rows. For the head the claim is trivial. For every later element,
    `readMessage = prev.regPreMessage` (which has `mem_op = 3`), so
    `readMessage_ptr_eq_regPreMessage_ptr_of_memop3` gives `readMessage.ptr =
    regPreMessage.ptr`, and the chain link gives `readMessage.ptr =
    prev.regPreMessage.ptr`. -/
private theorem regPreMessage_ptr_const_along_chain {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (path : List RegWalkStep) (p : RegWalkStep),
      path.head? = some p →
      List.IsChain RegWalkStep.AnswersRegPre path →
      (∀ q ∈ path, IsActiveWitnessMainRow trace q) →
      ∀ q ∈ path,
        (q.2.regPreMessage q.1).ptr = (p.2.regPreMessage p.1).ptr := by
  intro path
  induction path with
  | nil => intro _ h; simp at h
  | cons a rest ih =>
    intro p h_head h_chain h_sites q h_q
    have h_p : a = p := by simpa using h_head
    subst h_p
    rcases List.mem_cons.mp h_q with rfl | h_rest
    · rfl
    · cases rest with
      | nil => exact absurd h_rest List.not_mem_nil
      | cons b rest' =>
        obtain ⟨h_link, h_chain'⟩ := List.isChain_cons_cons.mp h_chain
        -- b.readMessage = a.regPreMessage (from chain link)
        have h_link' : b.2.readMessage b.1 = a.2.regPreMessage a.1 := h_link
        -- b.readMessage.mem_op = 3 (since a.regPreMessage.mem_op = 3)
        have h_b_memop : (b.2.readMessage b.1).mem_op = 3 := by
          rw [congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.mem_op h_link]
          cases a.2 <;> rfl
        -- b.readMessage.ptr = b.regPreMessage.ptr
        have h_b_inner := readMessage_ptr_eq_regPreMessage_ptr_of_memop3 trace
          (h_sites b (List.mem_cons_of_mem _ List.mem_cons_self)) h_b_memop
        -- b.regPreMessage.ptr = a.regPreMessage.ptr
        have h_b_eq : (b.2.regPreMessage b.1).ptr = (a.2.regPreMessage a.1).ptr :=
          h_b_inner ▸ congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.ptr h_link'
        -- Induction: q.regPreMessage.ptr = b.regPreMessage.ptr
        have h_ih := ih b rfl h_chain'
          (fun r hr => h_sites r (List.mem_cons_of_mem _ hr)) q h_rest
        exact h_ih.trans h_b_eq

private theorem store_ind_or_stepRegWrite_none
    {n : Nat} {trace : AcceptedZiskTrace n}
    (i : Fin n) (zs : ZiskStep trace i) (rd : RowDecode trace i zs)
    (h_pr : stepProducerRow i zs rd = i.val) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind = 0
    ∨ stepRegWrite (stepChannelOutput i zs rd) = none := by
  cases zs with
  | jalr c => exact Or.inl (by rw [← h_pr]; exact rd.h_store_ind)
  | _ => first | exact Or.inl rd.h_store_ind | exact Or.inr rfl

theorem store_ind_eq_zero_of_store_reg
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (i : Fin n)
    (h_sr : (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_ind = 0 := by
  rcases store_ind_or_stepRegWrite_none i (ziskStep i) (rowDecodes i)
    (h_stepRegWrite_consistent i h_sr).2 with h_si | h_none
  · exact h_si
  · exact absurd h_none (h_stepRegWrite_consistent i h_sr).1

/-! ## Chain completeness — a write to register r appears on the boot walk

If step m writes register r and its c-slot is active (`store_reg = 1`), the c-slot
appears on the boot walk chain from any later a-slot reading register r. The proof
constructs a second boot walk from the c-slot, matches the boot anchors via
`bootAnchoredStep_unique`, and uses `bootWalk_merge` to place the c-slot on the
original path (the alternative — the a-slot on the c-slot's path — gives a timestamp
contradiction since step k's a-slot has a strictly higher timestamp). -/

/-- **Step m's c-slot is on the boot walk.** Given `StepWritesReg m r` with `m < k`, the
    premise `h_stepRegWrite_converse` gives `store_reg = 1`, which makes the c-slot active.
    Then `exists_bootWalk` gives a chain from the c-slot to a boot anchor. By
    `bootAnchoredStep_unique` (matching ptr) both walks end at the same anchor, and
    `bootWalk_merge` puts the c-slot on the original path. -/
theorem stepWritesReg_cslot_on_bootWalk
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    {k : ℕ} (hk : k < n) (r : Fin 32)
    (h_a_ptr : Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 = r)
    (h_lt : (⟨k, hk⟩ : Fin n).val < trace.mainTable.table.length)
    {path : List RegWalkStep} {last : RegWalkStep}
    (h_head : path.head? = some
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.a))
    (h_last : path.getLast? = some last)
    (h_sites : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.AnswersRegPre path)
    (h_boot : BootAnchoredStep trace last)
    {m : ℕ} (hm : m < k)
    (h_wr : StepWritesReg ziskStep rowDecodes m r) :
    ∃ w ∈ path, w.2 = Instantiation.RegSlot.c
      ∧ w.1 = mainTableRowAtOrZero trace.program trace.mainTable m := by
  -- Step 1: store_reg = 1 from StepWritesReg
  obtain ⟨h_m_lt, e, he, heq⟩ := h_wr
  have h_sr := h_stepRegWrite_converse ⟨m, h_m_lt⟩ (he ▸ Option.some_ne_none _)
  -- Step 2: table length bound
  have h_m_lt_table : m < trace.mainTable.table.length :=
    trace.mainTable_index ⟨m, h_m_lt⟩
  -- Step 3: c-slot selector in eval form
  have h_sel_c : Instantiation.RegSlot.c.selector
      (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar) = 1 := by
    unfold Instantiation.RegSlot.selector
    have h_eq := mainTableRowAtOrZero_get trace.program trace.mainTable ⟨m, h_m_lt_table⟩
    rw [← h_eq]; exact h_sr
  -- Step 4: boot walk from the c-slot
  obtain ⟨path_m, last_m, h_head_m, h_last_m, h_sites_m, h_chain_m, h_boot_m⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem h_m_lt_table) Instantiation.RegSlot.c h_sel_c
  -- Step 5: regPreMessage.ptr is constant along an AnswersRegPre chain.
  -- For any non-head element, readMessage = prev.regPreMessage (mem_op = 3), so
  -- readMessage.ptr = regPreMessage.ptr by readMessage_ptr_eq_regPreMessage_ptr_of_memop3.
  -- For the head: trivial. Hence last.regPreMessage.ptr = head.regPreMessage.ptr.
  have h_last_ptr : (last.2.regPreMessage last.1).ptr =
      (Instantiation.RegSlot.a.regPreMessage
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar)).ptr := by
    have h_ne' : path ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last)
    have h_head_some := List.head?_eq_some_head h_ne'
    rw [h_head] at h_head_some
    have h_head_id := Option.some.inj h_head_some.symm
    exact regPreMessage_ptr_const_along_chain trace path _ (List.head?_eq_some_head h_ne')
      h_chain h_sites last (List.mem_of_getLast? h_last)
      |>.trans (by rw [h_head_id])
  have h_last_m_ptr : (last_m.2.regPreMessage last_m.1).ptr =
      (Instantiation.RegSlot.c.regPreMessage
        (eval (trace.mainTable.environment trace.mainTable.table[m])
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar)).ptr := by
    have h_ne' : path_m ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last_m)
    have h_head_some := List.head?_eq_some_head h_ne'
    rw [h_head_m] at h_head_some
    have h_head_id := Option.some.inj h_head_some.symm
    exact regPreMessage_ptr_const_along_chain trace path_m _ (List.head?_eq_some_head h_ne')
      h_chain_m h_sites_m last_m (List.mem_of_getLast? h_last_m)
      |>.trans (by rw [h_head_id])
  -- Step 5b: Both ptrs encode register r, so they are equal.
  -- head.regPreMessage.ptr = a_offset_imm0(row_k), head_m.regPreMessage.ptr = store_offset(row_m).
  -- From store_ind = 0 (extracted from RowDecode) and AddressSpec, addr2 = store_offset.
  -- Then wrap_to_regidx(store_offset) = r (from heq). Both are boot boundary reg values
  -- in {natF(1),...,natF(31)}, so wrap_to_regidx injectivity gives equality.
  have h_ptr_eq : (last.2.regPreMessage last.1).ptr =
      (last_m.2.regPreMessage last_m.1).ptr := by
    rw [h_last_ptr, h_last_m_ptr]
    -- Goal: aRegPreMessage(row_k).ptr = cRegPreMessage(row_m).ptr
    -- i.e., a_offset_imm0(row_k) = store_offset(row_m)
    -- Step A: derive wrap_to_regidx(store_offset(row_m)) = r
    --   via addr2 = store_offset (AddressSpec + store_ind = 0) + heq
    have h_store_ind : (mainTableRowAtOrZero trace.program trace.mainTable m).rom.store_ind = 0 :=
      store_ind_eq_zero_of_store_reg trace ziskStep rowDecodes h_stepRegWrite_consistent
        ⟨m, h_m_lt⟩ h_sr
    have h_addr_spec := RomDecodeBinding.mainAddressSpec_at trace ⟨m, h_m_lt_table⟩
    have h_e_eq : e = (ZiskFv.AirsClean.Main.cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable m)).toEntry 1 1 := by
      rcases stepRegWrite_eq_none_or_cMemMessage ⟨m, h_m_lt⟩
        (ziskStep ⟨m, h_m_lt⟩) (rowDecodes ⟨m, h_m_lt⟩) with h_none | h_some
      · exact absurd (he ▸ h_none) (Option.some_ne_none _)
      · have h_pr := (h_stepRegWrite_consistent ⟨m, h_m_lt⟩ h_sr).2
        rw [h_pr] at h_some; exact Option.some.inj (he.symm.trans h_some)
    have h_so_r : Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable m).rom.store_offset = r := by
      have h_e_ptr : e.ptr =
          (mainTableRowAtOrZero trace.program trace.mainTable m).rom.store_offset := by
        rw [h_e_eq]
        show (ZiskFv.AirsClean.Main.cMemMessage _).ptr = _
        simp only [ZiskFv.AirsClean.Main.cMemMessage]
        rw [h_addr_spec.2.2.1, h_store_ind, zero_mul, add_zero]
      rw [← h_e_ptr]; exact heq
    -- Step B: Both sides are boot boundary reg values with .val < 32, both
    -- map to r under wrap_to_regidx. wrap_to_regidx is injective on {.val < 32}.
    -- Use the boot anchors to get .val < 32, then Fin.val equality from wrap_to_regidx.
    have h_val_lt_a : (last.2.regPreMessage last.1).ptr.val < 32 :=
      bootAnchoredStep_ptr_val_lt trace h_boot
    have h_val_lt_m : (last_m.2.regPreMessage last_m.1).ptr.val < 32 :=
      bootAnchoredStep_ptr_val_lt trace h_boot_m
    -- Chain propagation + boot anchor: the head ptrs have .val < 32 too
    rw [h_last_ptr] at h_val_lt_a; rw [h_last_m_ptr] at h_val_lt_m
    -- Both wrap_to_regidx map to r: h_a_ptr and h_so_r (after bridging eval ↔ mainTableRowAtOrZero)
    -- h_a_ptr : wrap_to_regidx(mainTableRowAtOrZero k .a_offset_imm0) = r
    -- h_so_r  : wrap_to_regidx(mainTableRowAtOrZero m .store_offset) = r
    -- The goal after rw [h_last_ptr, h_last_m_ptr]:
    --   aRegPreMessage(eval row_k).ptr = cRegPreMessage(eval row_m).ptr
    -- aRegPreMessage.ptr = .rom.a_offset_imm0, cRegPreMessage.ptr = .rom.store_offset
    -- show a_offset_imm0 = store_offset via Fin.ext from .val equality
    simp only [Instantiation.RegSlot.regPreMessage, ZiskFv.AirsClean.Main.aRegPreMessage,
      ZiskFv.AirsClean.Main.cRegPreMessage] at h_val_lt_a h_val_lt_m ⊢
    -- Goal: (eval row_k).rom.a_offset_imm0 = (eval row_m).rom.store_offset (with table[m] notation)
    -- Bridge h_a_ptr and h_so_r from mainTableRowAtOrZero to eval rows
    have h_eq_k := mainTableRowAtOrZero_get trace.program trace.mainTable ⟨k, h_lt⟩
    have h_eq_m' := mainTableRowAtOrZero_get trace.program trace.mainTable ⟨m, h_m_lt_table⟩
    have h_wrap_a : Transpiler.wrap_to_regidx
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar).rom.a_offset_imm0 = r := by
      rw [← h_eq_k]; exact h_a_ptr
    have h_wrap_c : Transpiler.wrap_to_regidx
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar).rom.store_offset = r := by
      rw [← h_eq_m']; exact h_so_r
    -- Fin.ext: both .val = r.val from wrap_to_regidx + .val < 32
    have h_a_val := congrArg Fin.val h_wrap_a
    have h_m_val := congrArg Fin.val h_wrap_c
    simp only [Transpiler.wrap_to_regidx, Fin.val_mk] at h_a_val h_m_val
    rw [Nat.mod_eq_of_lt h_val_lt_a] at h_a_val
    -- h_m_val uses table.get ⟨m, _⟩ while h_val_lt_m uses table[m]; unify
    have h_val_lt_m' : (eval (trace.mainTable.environment
        (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar).rom.store_offset.val < 32 := h_val_lt_m
    rw [Nat.mod_eq_of_lt h_val_lt_m'] at h_m_val
    -- h_a_val : a_offset_imm0.val = r.val, h_m_val : store_offset.val = r.val
    -- Goal still has table[m] vs table.get mismatch; convert via Fin.val ext
    have h_goal_val : (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar).rom.a_offset_imm0.val =
      (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar).rom.store_offset.val := by omega
    have h_goal := Fin.ext h_goal_val
    exact h_goal
  -- Step 5c: boot anchor uniqueness
  have h_last_active : IsActiveWitnessMainRow trace last := by
    exact h_sites last (List.mem_of_getLast? h_last)
  have h_last_m_active : IsActiveWitnessMainRow trace last_m := by
    exact h_sites_m last_m (List.mem_of_getLast? h_last_m)
  have h_last_eq : last = last_m :=
    bootAnchoredStep_unique trace h_last_active h_last_m_active h_boot h_boot_m h_ptr_eq
  -- Step 6: chain merge — c-slot head lands on the a-slot path
  have h_ne_path : path ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last)
  have h_ne_path_m : path_m ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last_m)
  by_cases h_len : path_m.length ≤ path.length
  · -- path_m.length ≤ path.length: bootWalk_merge gives head_m ∈ path
    have h_head_m_mem : (eval (trace.mainTable.environment trace.mainTable.table[m])
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar, Instantiation.RegSlot.c) ∈ path :=
      bootWalk_merge trace h_sites h_sites_m h_chain h_chain_m
        (h_last_eq ▸ h_last) h_last_m h_len h_head_m
    exact ⟨_, h_head_m_mem, rfl,
      (mainTableRowAtOrZero_get trace.program trace.mainTable ⟨m, h_m_lt_table⟩).symm⟩
  · -- path.length < path_m.length: bootWalk_merge gives head ∈ path_m
    -- But head's timestamp = 1+4k ≥ head_m's timestamp = 3+4m (since m < k)
    -- so head ∉ path_m by not_mem_chain_of_timestamp_ge — contradiction.
    have h_head_mem : (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar, Instantiation.RegSlot.a) ∈ path_m :=
      bootWalk_merge trace h_sites_m h_sites h_chain_m h_chain
        h_last_m (h_last_eq ▸ h_last) (by omega) h_head
    exfalso
    set head_k : Instantiation.RegWalkStep :=
      (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar, Instantiation.RegSlot.a)
    have h_ne_head : head_k ≠ path_m.head h_ne_path_m := by
      intro heq_head
      have h_head_m_id := List.head?_eq_some_head h_ne_path_m
      rw [h_head_m] at h_head_m_id
      have h_snd := congrArg Prod.snd (heq_head.trans (Option.some.inj h_head_m_id.symm))
      show False
      cases h_snd
    have h_ts_ge : (path_m.head h_ne_path_m).timestamp.val ≤
        head_k.timestamp.val := by
      -- head_k.timestamp = a-slot at step k = 1 + 4*k
      -- path_m.head.timestamp = c-slot at step m = 3 + 4*m
      -- Since m < k: 3 + 4*m ≤ 4*k + 1 = 1 + 4*k
      have h_head_m_id := List.head?_eq_some_head h_ne_path_m
      rw [h_head_m] at h_head_m_id
      have h_head_m_eq := Option.some.inj h_head_m_id.symm
      have h_ms_k := mainRowAt_main_step trace.mainTable_component h_lt
      have h_cap_k := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt
      have h_ms_m := mainRowAt_main_step trace.mainTable_component h_m_lt_table
      have h_cap_m := main_index_lt_mainFixedCapacity trace.mainTable_component h_m_lt_table
      have h_k_ts : head_k.timestamp = (1 : FGL) + (↑k : FGL) * 4 := by
        show Instantiation.RegSlot.a.readTimestamp _ = _
        simp only [Instantiation.RegSlot.readTimestamp]
        have h_ms_k' : head_k.1.rom.main_step = (↑k : FGL) := by
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt] at h_ms_k
          exact h_ms_k
        rw [h_ms_k']
      have h_k_val : head_k.timestamp.val = 1 + 4 * k :=
        h_k_ts ▸ slot_timestamp_val (by norm_num : (1 : ℕ) ≤ 3) h_cap_k
      have h_m_ts : (path_m.head h_ne_path_m).timestamp = (3 : FGL) + (↑m : FGL) * 4 := by
        rw [h_head_m_eq]
        show Instantiation.RegSlot.c.readTimestamp _ = _
        simp only [Instantiation.RegSlot.readTimestamp]
        have h_ms_m' : (eval (trace.mainTable.environment trace.mainTable.table[m])
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
              trace.program).rowInputVar).rom.main_step = (↑m : FGL) := by
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_m_lt_table] at h_ms_m
          exact h_ms_m
        rw [h_ms_m']
      have h_m_val : (path_m.head h_ne_path_m).timestamp.val = 3 + 4 * m :=
        h_m_ts ▸ slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap_m
      clear h_k_ts h_m_ts h_head_m_eq h_ms_k h_ms_m h_cap_k h_cap_m h_head_m_id
      omega
    exact not_mem_chain_of_timestamp_ge trace h_ne_path_m h_sites_m h_chain_m
      h_ne_head h_ts_ge h_head_mem

theorem stepWritesReg_cslot_on_bootWalk_b
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    {k : ℕ} (hk : k < n) (r : Fin 32)
    (h_b_ptr : Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 = r)
    (h_lt : (⟨k, hk⟩ : Fin n).val < trace.mainTable.table.length)
    {path : List RegWalkStep} {last : RegWalkStep}
    (h_head : path.head? = some
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.b))
    (h_last : path.getLast? = some last)
    (h_sites : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.AnswersRegPre path)
    (h_boot : BootAnchoredStep trace last)
    {m : ℕ} (hm : m < k)
    (h_wr : StepWritesReg ziskStep rowDecodes m r) :
    ∃ w ∈ path, w.2 = Instantiation.RegSlot.c
      ∧ w.1 = mainTableRowAtOrZero trace.program trace.mainTable m := by
  obtain ⟨h_m_lt, e, he, heq⟩ := h_wr
  have h_sr := h_stepRegWrite_converse ⟨m, h_m_lt⟩ (he ▸ Option.some_ne_none _)
  have h_m_lt_table : m < trace.mainTable.table.length :=
    trace.mainTable_index ⟨m, h_m_lt⟩
  have h_sel_c : Instantiation.RegSlot.c.selector
      (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar) = 1 := by
    unfold Instantiation.RegSlot.selector
    have h_eq := mainTableRowAtOrZero_get trace.program trace.mainTable ⟨m, h_m_lt_table⟩
    rw [← h_eq]; exact h_sr
  obtain ⟨path_m, last_m, h_head_m, h_last_m, h_sites_m, h_chain_m, h_boot_m⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem h_m_lt_table) Instantiation.RegSlot.c h_sel_c
  have h_last_ptr : (last.2.regPreMessage last.1).ptr =
      (Instantiation.RegSlot.b.regPreMessage
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar)).ptr := by
    have h_ne' : path ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last)
    have h_head_some := List.head?_eq_some_head h_ne'
    rw [h_head] at h_head_some
    have h_head_id := Option.some.inj h_head_some.symm
    exact regPreMessage_ptr_const_along_chain trace path _ (List.head?_eq_some_head h_ne')
      h_chain h_sites last (List.mem_of_getLast? h_last)
      |>.trans (by rw [h_head_id])
  have h_last_m_ptr : (last_m.2.regPreMessage last_m.1).ptr =
      (Instantiation.RegSlot.c.regPreMessage
        (eval (trace.mainTable.environment trace.mainTable.table[m])
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar)).ptr := by
    have h_ne' : path_m ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last_m)
    have h_head_some := List.head?_eq_some_head h_ne'
    rw [h_head_m] at h_head_some
    have h_head_id := Option.some.inj h_head_some.symm
    exact regPreMessage_ptr_const_along_chain trace path_m _ (List.head?_eq_some_head h_ne')
      h_chain_m h_sites_m last_m (List.mem_of_getLast? h_last_m)
      |>.trans (by rw [h_head_id])
  have h_ptr_eq : (last.2.regPreMessage last.1).ptr =
      (last_m.2.regPreMessage last_m.1).ptr := by
    rw [h_last_ptr, h_last_m_ptr]
    have h_store_ind : (mainTableRowAtOrZero trace.program trace.mainTable m).rom.store_ind = 0 :=
      store_ind_eq_zero_of_store_reg trace ziskStep rowDecodes h_stepRegWrite_consistent
        ⟨m, h_m_lt⟩ h_sr
    have h_addr_spec := RomDecodeBinding.mainAddressSpec_at trace ⟨m, h_m_lt_table⟩
    have h_e_eq : e = (ZiskFv.AirsClean.Main.cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable m)).toEntry 1 1 := by
      rcases stepRegWrite_eq_none_or_cMemMessage ⟨m, h_m_lt⟩
        (ziskStep ⟨m, h_m_lt⟩) (rowDecodes ⟨m, h_m_lt⟩) with h_none | h_some
      · exact absurd (he ▸ h_none) (Option.some_ne_none _)
      · have h_pr := (h_stepRegWrite_consistent ⟨m, h_m_lt⟩ h_sr).2
        rw [h_pr] at h_some; exact Option.some.inj (he.symm.trans h_some)
    have h_so_r : Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable m).rom.store_offset = r := by
      have h_e_ptr : e.ptr =
          (mainTableRowAtOrZero trace.program trace.mainTable m).rom.store_offset := by
        rw [h_e_eq]
        show (ZiskFv.AirsClean.Main.cMemMessage _).ptr = _
        simp only [ZiskFv.AirsClean.Main.cMemMessage]
        rw [h_addr_spec.2.2.1, h_store_ind, zero_mul, add_zero]
      rw [← h_e_ptr]; exact heq
    have h_val_lt_b : (last.2.regPreMessage last.1).ptr.val < 32 :=
      bootAnchoredStep_ptr_val_lt trace h_boot
    have h_val_lt_m : (last_m.2.regPreMessage last_m.1).ptr.val < 32 :=
      bootAnchoredStep_ptr_val_lt trace h_boot_m
    rw [h_last_ptr] at h_val_lt_b; rw [h_last_m_ptr] at h_val_lt_m
    simp only [Instantiation.RegSlot.regPreMessage, ZiskFv.AirsClean.Main.bRegPreMessage,
      ZiskFv.AirsClean.Main.cRegPreMessage] at h_val_lt_b h_val_lt_m ⊢
    have h_eq_k := mainTableRowAtOrZero_get trace.program trace.mainTable ⟨k, h_lt⟩
    have h_eq_m' := mainTableRowAtOrZero_get trace.program trace.mainTable ⟨m, h_m_lt_table⟩
    have h_wrap_b : Transpiler.wrap_to_regidx
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar).rom.b_offset_imm0 = r := by
      rw [← h_eq_k]; exact h_b_ptr
    have h_wrap_c : Transpiler.wrap_to_regidx
        (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar).rom.store_offset = r := by
      rw [← h_eq_m']; exact h_so_r
    have h_b_val := congrArg Fin.val h_wrap_b
    have h_m_val := congrArg Fin.val h_wrap_c
    simp only [Transpiler.wrap_to_regidx, Fin.val_mk] at h_b_val h_m_val
    rw [Nat.mod_eq_of_lt h_val_lt_b] at h_b_val
    have h_val_lt_m' : (eval (trace.mainTable.environment
        (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar).rom.store_offset.val < 32 := h_val_lt_m
    rw [Nat.mod_eq_of_lt h_val_lt_m'] at h_m_val
    have h_goal_val : (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar).rom.b_offset_imm0.val =
      (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨m, h_m_lt_table⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar).rom.store_offset.val := by omega
    exact Fin.ext h_goal_val
  have h_last_active : IsActiveWitnessMainRow trace last := by
    exact h_sites last (List.mem_of_getLast? h_last)
  have h_last_m_active : IsActiveWitnessMainRow trace last_m := by
    exact h_sites_m last_m (List.mem_of_getLast? h_last_m)
  have h_last_eq : last = last_m :=
    bootAnchoredStep_unique trace h_last_active h_last_m_active h_boot h_boot_m h_ptr_eq
  have h_ne_path : path ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last)
  have h_ne_path_m : path_m ≠ [] := List.ne_nil_of_mem (List.mem_of_getLast? h_last_m)
  by_cases h_len : path_m.length ≤ path.length
  · have h_head_m_mem : (eval (trace.mainTable.environment trace.mainTable.table[m])
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar, Instantiation.RegSlot.c) ∈ path :=
      bootWalk_merge trace h_sites h_sites_m h_chain h_chain_m
        (h_last_eq ▸ h_last) h_last_m h_len h_head_m
    exact ⟨_, h_head_m_mem, rfl,
      (mainTableRowAtOrZero_get trace.program trace.mainTable ⟨m, h_m_lt_table⟩).symm⟩
  · have h_head_mem : (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar, Instantiation.RegSlot.b) ∈ path_m :=
      bootWalk_merge trace h_sites_m h_sites h_chain_m h_chain
        h_last_m (h_last_eq ▸ h_last) (by omega) h_head
    exfalso
    set head_k : Instantiation.RegWalkStep :=
      (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar, Instantiation.RegSlot.b)
    have h_ne_head : head_k ≠ path_m.head h_ne_path_m := by
      intro heq_head
      have h_head_m_id := List.head?_eq_some_head h_ne_path_m
      rw [h_head_m] at h_head_m_id
      have h_snd := congrArg Prod.snd (heq_head.trans (Option.some.inj h_head_m_id.symm))
      show False
      cases h_snd
    have h_ts_ge : (path_m.head h_ne_path_m).timestamp.val ≤
        head_k.timestamp.val := by
      have h_head_m_id := List.head?_eq_some_head h_ne_path_m
      rw [h_head_m] at h_head_m_id
      have h_head_m_eq := Option.some.inj h_head_m_id.symm
      have h_ms_k := mainRowAt_main_step trace.mainTable_component h_lt
      have h_cap_k := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt
      have h_ms_m := mainRowAt_main_step trace.mainTable_component h_m_lt_table
      have h_cap_m := main_index_lt_mainFixedCapacity trace.mainTable_component h_m_lt_table
      have h_k_ts : head_k.timestamp = (2 : FGL) + (↑k : FGL) * 4 := by
        show Instantiation.RegSlot.b.readTimestamp _ = _
        simp only [Instantiation.RegSlot.readTimestamp]
        have h_ms_k' : head_k.1.rom.main_step = (↑k : FGL) := by
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt] at h_ms_k
          exact h_ms_k
        rw [h_ms_k']
      have h_k_val : head_k.timestamp.val = 2 + 4 * k :=
        h_k_ts ▸ slot_timestamp_val (by norm_num : (2 : ℕ) ≤ 3) h_cap_k
      have h_m_ts : (path_m.head h_ne_path_m).timestamp = (3 : FGL) + (↑m : FGL) * 4 := by
        rw [h_head_m_eq]
        show Instantiation.RegSlot.c.readTimestamp _ = _
        simp only [Instantiation.RegSlot.readTimestamp]
        have h_ms_m' : (eval (trace.mainTable.environment trace.mainTable.table[m])
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
              trace.program).rowInputVar).rom.main_step = (↑m : FGL) := by
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_m_lt_table] at h_ms_m
          exact h_ms_m
        rw [h_ms_m']
      have h_m_val : (path_m.head h_ne_path_m).timestamp.val = 3 + 4 * m :=
        h_m_ts ▸ slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap_m
      clear h_k_ts h_m_ts h_head_m_eq h_ms_k h_ms_m h_cap_k h_cap_m h_head_m_id
      omega
    exact not_mem_chain_of_timestamp_ge trace h_ne_path_m h_sites_m h_chain_m
      h_ne_head h_ts_ge h_head_mem

/-! ## The main derivation theorem: a-column = lane_lo(ziskRegFile)

Given that the a-slot at step `k` reads register `r` (selector active, ptr = ind r),
and `RegAgree k` holds, the a-column equals the Sail register via the register file.

This theorem combines the boot walk (circuit-level value chain) with RegAgree
(register file = Sail state). The proof uses `exists_bootWalk` for the circuit
chain and `sail_xreg_eq_ziskRegFile` for the Sail bridge.

The boot walk gives either:
- boot-anchored: a_0 = 0, and ziskRegFile k r = 0 (no writes to r)
- supplier q: a_0 = cMemMessage(q).value_0, and the supplier's write value
  equals ziskRegFile k r (q is the latest writer to r)

Both cases close with the same conclusion: a_0 = lane_lo(ziskRegFile k r). -/

theorem a_column_eq_lane_lo_sail_xreg
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (h_regAgree : RegAgree ziskStep rowDecodes init k)
    (h_a_src_reg :
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_reg = 1)
    (h_a_ptr :
      Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 = r)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_entry_range : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
          = some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) →
        ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)
        ∧ ZiskFv.Airs.MemoryBus.memory_entry_packed_no_wrap
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 k =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (chainedSailStates ziskStep init k)).xreg r) := by
  rw [ZiskFv.Compliance.sail_xreg_eq_ziskRegFile ziskStep rowDecodes init k r hr h_regAgree]
  -- Goal: mainOfTable.a_0 k = lane_lo (ziskRegFile k r)
  -- Use exists_bootWalk for the full chain, then compose with register file.
  have h_lt := trace.mainTable_index ⟨k, hk⟩
  obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_boot⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem h_lt) Instantiation.RegSlot.a
      (by unfold ZiskFv.Compliance.Instantiation.RegSlot.selector
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero,
            dif_pos h_lt] at h_a_src_reg ⊢
          exact h_a_src_reg)
  -- The chain gives both the value and the ordering.
  -- bootWalk_head_value extracts the value from the chain.
  rcases bootWalk_head_value_strong trace path _ last h_head h_last h_sites h_chain h_boot with
    ⟨h0, h1, h_no_cslot⟩ | ⟨q, h_q, h_qc, h_q0, h_q1, h_max_ts⟩
  · -- Boot-anchored: a_0 = 0
    have h_a0_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).a_0 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.a_0 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_no_writes : ∀ m, m < k → ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m hm h_wr
      obtain ⟨w, h_w_mem, h_wc, _⟩ := stepWritesReg_cslot_on_bootWalk trace ziskStep rowDecodes
        h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_a_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.a) := by
        intro heq
        have := congrArg Prod.snd heq
        simp only [h_wc] at this; exact absurd this (by decide)
      exact absurd h_wc (h_no_cslot w h_w_mem (by convert h_ne))
    rw [h_a0_eq]
    have h_zero := ziskRegFile_eq_lane_lo_of_bootWalk_zero trace ziskStep rowDecodes
      k hk r hr h_no_writes
    -- h0 : regPreMessage.value_0 = 0, which is definitionally core.a_0 = 0
    convert h0.symm ▸ h_zero
  · -- Supplier q: head's a_0 = cMemMessage(q.1).value_0 via h_q0
    -- Goal: mainOfTable.a_0 k = lane_lo(ziskRegFile k r)
    -- Step 1: mainOfTable.a_0 k = aRegPreMessage(row_k).value_0 = head.regPreMessage.value_0
    -- Step 2: head.regPreMessage.value_0 = q.readMessage.value_0 (h_q0)
    -- Step 3: q.readMessage = cMemMessage q.1 (since q.2 = .c)
    -- So mainOfTable.a_0 k = cMemMessage(q.1).value_0
    -- Step 4: cMemMessage(q.1).value_0 = lane_lo(ziskRegFile k r) (the register file chain)
    have h_a0_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).a_0 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.a_0 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    -- The supplier's timestamp < head's timestamp (from chain membership)
    have h_q_ts_lt : q.timestamp.val < (3 + 4 * k : ℕ) := by
      have h_bound := timestamp_val_le_head_of_mem_chain trace
        (by rcases path with _ | ⟨_, _⟩ <;> simp_all)
        h_sites h_chain h_q
      have h_ne : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some := List.head?_eq_some_head h_ne
      rw [h_head] at h_head_some
      have h_head_id := Option.some.inj h_head_some.symm
      have h_head_ts : (path.head h_ne).timestamp =
          RegSlot.a.readTimestamp
            (mainTableRowAtOrZero trace.program trace.mainTable k) := by
        simp only [Instantiation.RegWalkStep.timestamp]
        congr 1
        · exact congrArg Prod.snd h_head_id
        · simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
          exact congrArg Prod.fst h_head_id
      have h_ms := mainRowAt_main_step trace.mainTable_component h_lt
      have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt
      have h_head_ts_val : (path.head h_ne).timestamp.val = 1 + 4 * k := by
        have : (path.head h_ne).timestamp = (1 : FGL) + (↑k : FGL) * 4 := by
          rw [h_head_ts]; simp [Instantiation.RegSlot.readTimestamp, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (1 : ℕ) ≤ 3) h_cap
      omega
    -- The supplier targets register r (from the chain's ptr propagation)
    have h_q_ptr : Transpiler.wrap_to_regidx (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr = r := by
      have h_ne' : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some' := List.head?_eq_some_head h_ne'
      rw [h_head] at h_head_some'
      have h_head_id' := Option.some.inj h_head_some'.symm
      have h_head_snd : (path.head h_ne').2 = RegSlot.a := congrArg Prod.snd h_head_id'
      -- q ≠ head (since q.2 = .c and head.2 = .a)
      have h_q_ne : q ≠ path.head h_ne' := by
        intro h_eq
        have : q.2 = (path.head h_ne').2 := congrArg Prod.snd h_eq
        rw [h_qc, h_head_snd] at this
        exact absurd this (by decide)
      -- Chain propagation gives q.readMessage.ptr = head.regPreMessage.ptr
      have h_chain_ptr := bootWalk_head_ptr trace path (path.head h_ne')
        (List.head?_eq_some_head h_ne') h_chain h_sites q h_q h_q_ne
      -- q.readMessage.ptr = cMemMessage.ptr (since q.2 = .c)
      have h_rc : (q.2.readMessage q.1).ptr =
          (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr := by rw [h_qc]; rfl
      -- head.regPreMessage.ptr = a_offset_imm0
      have h_head_ptr : ((path.head h_ne').2.regPreMessage (path.head h_ne').1).ptr =
          (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 := by
        rw [h_head_snd]
        -- Goal: (RegSlot.a.regPreMessage (path.head h_ne').1).ptr = ...
        -- regPreMessage .a row = aRegPreMessage row, .ptr = row.rom.a_offset_imm0
        simp only [Instantiation.RegSlot.regPreMessage, ZiskFv.AirsClean.Main.aRegPreMessage]
        -- Goal: (path.head h_ne').1.rom.a_offset_imm0 = (mainTableRowAtOrZero k).rom.a_offset_imm0
        congr 1; congr 1
        rw [congrArg Prod.fst h_head_id']
        -- Goal: eval (... table[↑⟨k, hk⟩] ...) ... = mainTableRowAtOrZero k
        symm; exact mainTableRowAtOrZero_get trace.program trace.mainTable ⟨k, h_lt⟩
      rw [← h_a_ptr, ← h_head_ptr, ← h_chain_ptr, h_rc]
    -- Use the helper theorem
    have h_a0_val : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).a_0 k
        = (ZiskFv.AirsClean.Main.cMemMessage q.1).value_0 := by
      rw [h_a0_eq]; convert h_q0; rw [h_qc]; rfl
    have h_no_writes_above : ∀ m, q.timestamp.val < 3 + 4 * m → m < k →
        ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m h_ts_lt hm h_wr
      obtain ⟨w, h_w_mem, h_wc, h_w_row⟩ := stepWritesReg_cslot_on_bootWalk trace ziskStep
        rowDecodes h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_a_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      -- w is on the path, w.2 = .c, w.1 = mainTableRowAtOrZero m
      -- w's timestamp = 3 + 4 * m (c-slot timestamp)
      -- By h_max_ts: w.timestamp ≤ q.timestamp
      have h_ne_head : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.a) := by
        intro heq; have := congrArg Prod.snd heq; simp only [h_wc] at this; exact absurd this (by decide)
      have h_w_ts_le := h_max_ts w h_w_mem (by convert h_ne_head) h_wc
      -- w's timestamp = 3 + 4 * m (from c-slot at row m)
      have h_m_lt_n : m < n := Nat.lt_trans hm hk
      have h_lt_m : m < trace.mainTable.table.length := by
        have := trace.mainTable_index ⟨m, h_m_lt_n⟩; omega
      have h_w_ts_val : w.timestamp.val = 3 + 4 * m := by
        have h_ms := mainRowAt_main_step trace.mainTable_component h_lt_m
        have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt_m
        have : w.timestamp = (3 : FGL) + (↑m : FGL) * 4 := by
          simp only [Instantiation.RegWalkStep.timestamp, h_wc,
            Instantiation.RegSlot.readTimestamp, h_w_row, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap
      omega
    rw [h_a0_val]
    exact cMemMessage_value_eq_lane_lo_of_bootWalk_supplier trace ziskStep rowDecodes
      k hk r hr q (h_sites q h_q) h_qc h_q_ptr h_q_ts_lt h_no_writes_above
      h_stepRegWrite_consistent h_stepRegWrite_converse h_entry_range

theorem a_column_eq_lane_hi_sail_xreg
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (h_regAgree : RegAgree ziskStep rowDecodes init k)
    (h_a_src_reg :
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_src_reg = 1)
    (h_a_ptr :
      Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 = r)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_entry_range : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
          = some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) →
        ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)
        ∧ ZiskFv.Airs.MemoryBus.memory_entry_packed_no_wrap
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 k =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (chainedSailStates ziskStep init k)).xreg r) := by
  rw [ZiskFv.Compliance.sail_xreg_eq_ziskRegFile ziskStep rowDecodes init k r hr h_regAgree]
  have h_lt := trace.mainTable_index ⟨k, hk⟩
  obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_boot⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem h_lt) Instantiation.RegSlot.a
      (by unfold ZiskFv.Compliance.Instantiation.RegSlot.selector
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero,
            dif_pos h_lt] at h_a_src_reg ⊢
          exact h_a_src_reg)
  rcases bootWalk_head_value_strong trace path _ last h_head h_last h_sites h_chain h_boot with
    ⟨h0, h1, h_no_cslot⟩ | ⟨q, h_q, h_qc, h_q0, h_q1, h_max_ts⟩
  · have h_a1_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).a_1 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.a_1 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_no_writes : ∀ m, m < k → ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m hm h_wr
      obtain ⟨w, h_w_mem, h_wc, _⟩ := stepWritesReg_cslot_on_bootWalk trace ziskStep rowDecodes
        h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_a_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.a) := by
        intro heq
        have := congrArg Prod.snd heq
        simp only [h_wc] at this; exact absurd this (by decide)
      exact absurd h_wc (h_no_cslot w h_w_mem (by convert h_ne))
    rw [h_a1_eq]
    have h_zero := ziskRegFile_eq_lane_hi_of_bootWalk_zero trace ziskStep rowDecodes
      k hk r hr h_no_writes
    convert h1.symm ▸ h_zero
  · have h_a1_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).a_1 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.a_1 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_q_ts_lt : q.timestamp.val < (3 + 4 * k : ℕ) := by
      have h_bound := timestamp_val_le_head_of_mem_chain trace
        (by rcases path with _ | ⟨_, _⟩ <;> simp_all)
        h_sites h_chain h_q
      have h_ne : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some := List.head?_eq_some_head h_ne
      rw [h_head] at h_head_some
      have h_head_id := Option.some.inj h_head_some.symm
      have h_head_ts : (path.head h_ne).timestamp =
          RegSlot.a.readTimestamp
            (mainTableRowAtOrZero trace.program trace.mainTable k) := by
        simp only [Instantiation.RegWalkStep.timestamp]
        congr 1
        · exact congrArg Prod.snd h_head_id
        · simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
          exact congrArg Prod.fst h_head_id
      have h_ms := mainRowAt_main_step trace.mainTable_component h_lt
      have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt
      have h_head_ts_val : (path.head h_ne).timestamp.val = 1 + 4 * k := by
        have : (path.head h_ne).timestamp = (1 : FGL) + (↑k : FGL) * 4 := by
          rw [h_head_ts]; simp [Instantiation.RegSlot.readTimestamp, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (1 : ℕ) ≤ 3) h_cap
      omega
    have h_q_ptr : Transpiler.wrap_to_regidx (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr = r := by
      have h_ne' : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some' := List.head?_eq_some_head h_ne'
      rw [h_head] at h_head_some'
      have h_head_id' := Option.some.inj h_head_some'.symm
      have h_head_snd : (path.head h_ne').2 = RegSlot.a := congrArg Prod.snd h_head_id'
      have h_q_ne : q ≠ path.head h_ne' := by
        intro h_eq
        have : q.2 = (path.head h_ne').2 := congrArg Prod.snd h_eq
        rw [h_qc, h_head_snd] at this
        exact absurd this (by decide)
      have h_chain_ptr := bootWalk_head_ptr trace path (path.head h_ne')
        (List.head?_eq_some_head h_ne') h_chain h_sites q h_q h_q_ne
      have h_rc : (q.2.readMessage q.1).ptr =
          (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr := by rw [h_qc]; rfl
      have h_head_ptr : ((path.head h_ne').2.regPreMessage (path.head h_ne').1).ptr =
          (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 := by
        rw [h_head_snd]
        simp only [Instantiation.RegSlot.regPreMessage, ZiskFv.AirsClean.Main.aRegPreMessage]
        congr 1; congr 1
        rw [congrArg Prod.fst h_head_id']
        symm; exact mainTableRowAtOrZero_get trace.program trace.mainTable ⟨k, h_lt⟩
      rw [← h_a_ptr, ← h_head_ptr, ← h_chain_ptr, h_rc]
    have h_a1_val : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).a_1 k
        = (ZiskFv.AirsClean.Main.cMemMessage q.1).value_1 := by
      rw [h_a1_eq]; convert h_q1; rw [h_qc]; rfl
    have h_no_writes_above : ∀ m, q.timestamp.val < 3 + 4 * m → m < k →
        ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m h_ts_lt hm h_wr
      obtain ⟨w, h_w_mem, h_wc, h_w_row⟩ := stepWritesReg_cslot_on_bootWalk trace ziskStep
        rowDecodes h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_a_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne_head : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.a) := by
        intro heq; have := congrArg Prod.snd heq; simp only [h_wc] at this; exact absurd this (by decide)
      have h_w_ts_le := h_max_ts w h_w_mem (by convert h_ne_head) h_wc
      have h_m_lt_n : m < n := Nat.lt_trans hm hk
      have h_lt_m : m < trace.mainTable.table.length := by
        have := trace.mainTable_index ⟨m, h_m_lt_n⟩; omega
      have h_w_ts_val : w.timestamp.val = 3 + 4 * m := by
        have h_ms := mainRowAt_main_step trace.mainTable_component h_lt_m
        have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt_m
        have : w.timestamp = (3 : FGL) + (↑m : FGL) * 4 := by
          simp only [Instantiation.RegWalkStep.timestamp, h_wc,
            Instantiation.RegSlot.readTimestamp, h_w_row, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap
      omega
    rw [h_a1_val]
    exact cMemMessage_value_eq_lane_hi_of_bootWalk_supplier trace ziskStep rowDecodes
      k hk r hr q (h_sites q h_q) h_qc h_q_ptr h_q_ts_lt h_no_writes_above
      h_stepRegWrite_consistent h_stepRegWrite_converse h_entry_range

theorem b_column_eq_lane_lo_sail_xreg
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (h_regAgree : RegAgree ziskStep rowDecodes init k)
    (h_b_src_reg :
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_reg = 1)
    (h_b_ptr :
      Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 = r)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_entry_range : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
          = some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) →
        ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)
        ∧ ZiskFv.Airs.MemoryBus.memory_entry_packed_no_wrap
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 k =
      ZiskFv.Trusted.lane_lo
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (chainedSailStates ziskStep init k)).xreg r) := by
  rw [ZiskFv.Compliance.sail_xreg_eq_ziskRegFile ziskStep rowDecodes init k r hr h_regAgree]
  have h_lt := trace.mainTable_index ⟨k, hk⟩
  obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_boot⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem h_lt) Instantiation.RegSlot.b
      (by unfold ZiskFv.Compliance.Instantiation.RegSlot.selector
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero,
            dif_pos h_lt] at h_b_src_reg ⊢
          exact h_b_src_reg)
  rcases bootWalk_head_value_strong trace path _ last h_head h_last h_sites h_chain h_boot with
    ⟨h0, h1, h_no_cslot⟩ | ⟨q, h_q, h_qc, h_q0, h_q1, h_max_ts⟩
  · have h_b0_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).b_0 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.b_0 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_no_writes : ∀ m, m < k → ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m hm h_wr
      obtain ⟨w, h_w_mem, h_wc, _⟩ := stepWritesReg_cslot_on_bootWalk_b trace ziskStep rowDecodes
        h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_b_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.b) := by
        intro heq
        have := congrArg Prod.snd heq
        simp only [h_wc] at this; exact absurd this (by decide)
      exact absurd h_wc (h_no_cslot w h_w_mem (by convert h_ne))
    rw [h_b0_eq]
    have h_zero := ziskRegFile_eq_lane_lo_of_bootWalk_zero trace ziskStep rowDecodes
      k hk r hr h_no_writes
    convert h0.symm ▸ h_zero
  · have h_b0_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).b_0 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.b_0 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_q_ts_lt : q.timestamp.val < (3 + 4 * k : ℕ) := by
      have h_bound := timestamp_val_le_head_of_mem_chain trace
        (by rcases path with _ | ⟨_, _⟩ <;> simp_all)
        h_sites h_chain h_q
      have h_ne : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some := List.head?_eq_some_head h_ne
      rw [h_head] at h_head_some
      have h_head_id := Option.some.inj h_head_some.symm
      have h_head_ts : (path.head h_ne).timestamp =
          RegSlot.b.readTimestamp
            (mainTableRowAtOrZero trace.program trace.mainTable k) := by
        simp only [Instantiation.RegWalkStep.timestamp]
        congr 1
        · exact congrArg Prod.snd h_head_id
        · simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
          exact congrArg Prod.fst h_head_id
      have h_ms := mainRowAt_main_step trace.mainTable_component h_lt
      have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt
      have h_head_ts_val : (path.head h_ne).timestamp.val = 2 + 4 * k := by
        have : (path.head h_ne).timestamp = (2 : FGL) + (↑k : FGL) * 4 := by
          rw [h_head_ts]; simp [Instantiation.RegSlot.readTimestamp, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (2 : ℕ) ≤ 3) h_cap
      omega
    have h_q_ptr : Transpiler.wrap_to_regidx (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr = r := by
      have h_ne' : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some' := List.head?_eq_some_head h_ne'
      rw [h_head] at h_head_some'
      have h_head_id' := Option.some.inj h_head_some'.symm
      have h_head_snd : (path.head h_ne').2 = RegSlot.b := congrArg Prod.snd h_head_id'
      have h_q_ne : q ≠ path.head h_ne' := by
        intro h_eq
        have : q.2 = (path.head h_ne').2 := congrArg Prod.snd h_eq
        rw [h_qc, h_head_snd] at this
        exact absurd this (by decide)
      have h_chain_ptr := bootWalk_head_ptr trace path (path.head h_ne')
        (List.head?_eq_some_head h_ne') h_chain h_sites q h_q h_q_ne
      have h_rc : (q.2.readMessage q.1).ptr =
          (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr := by rw [h_qc]; rfl
      have h_head_ptr : ((path.head h_ne').2.regPreMessage (path.head h_ne').1).ptr =
          (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 := by
        rw [h_head_snd]
        simp only [Instantiation.RegSlot.regPreMessage, ZiskFv.AirsClean.Main.bRegPreMessage]
        congr 1; congr 1
        rw [congrArg Prod.fst h_head_id']
        symm; exact mainTableRowAtOrZero_get trace.program trace.mainTable ⟨k, h_lt⟩
      rw [← h_b_ptr, ← h_head_ptr, ← h_chain_ptr, h_rc]
    have h_b0_val : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).b_0 k
        = (ZiskFv.AirsClean.Main.cMemMessage q.1).value_0 := by
      rw [h_b0_eq]; convert h_q0; rw [h_qc]; rfl
    have h_no_writes_above : ∀ m, q.timestamp.val < 3 + 4 * m → m < k →
        ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m h_ts_lt hm h_wr
      obtain ⟨w, h_w_mem, h_wc, h_w_row⟩ := stepWritesReg_cslot_on_bootWalk_b trace ziskStep
        rowDecodes h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_b_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne_head : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.b) := by
        intro heq; have := congrArg Prod.snd heq; simp only [h_wc] at this; exact absurd this (by decide)
      have h_w_ts_le := h_max_ts w h_w_mem (by convert h_ne_head) h_wc
      have h_m_lt_n : m < n := Nat.lt_trans hm hk
      have h_lt_m : m < trace.mainTable.table.length := by
        have := trace.mainTable_index ⟨m, h_m_lt_n⟩; omega
      have h_w_ts_val : w.timestamp.val = 3 + 4 * m := by
        have h_ms := mainRowAt_main_step trace.mainTable_component h_lt_m
        have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt_m
        have : w.timestamp = (3 : FGL) + (↑m : FGL) * 4 := by
          simp only [Instantiation.RegWalkStep.timestamp, h_wc,
            Instantiation.RegSlot.readTimestamp, h_w_row, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap
      omega
    rw [h_b0_val]
    exact cMemMessage_value_eq_lane_lo_of_bootWalk_supplier trace ziskStep rowDecodes
      k hk r hr q (h_sites q h_q) h_qc h_q_ptr h_q_ts_lt h_no_writes_above
      h_stepRegWrite_consistent h_stepRegWrite_converse h_entry_range

theorem b_column_eq_lane_hi_sail_xreg
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (h_regAgree : RegAgree ziskStep rowDecodes init k)
    (h_b_src_reg :
      (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_src_reg = 1)
    (h_b_ptr :
      Transpiler.wrap_to_regidx
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 = r)
    (h_stepRegWrite_consistent : ∀ (i : Fin n),
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1 →
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none
        ∧ stepProducerRow i (ziskStep i) (rowDecodes i) = i.val)
    (h_stepRegWrite_converse : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i)) ≠ none →
        (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.store_reg = 1)
    (h_entry_range : ∀ (i : Fin n),
        stepRegWrite (stepChannelOutput i (ziskStep i) (rowDecodes i))
          = some ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1) →
        ZiskFv.Airs.MemoryBus.memory_entry_chunks_in_range
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)
        ∧ ZiskFv.Airs.MemoryBus.memory_entry_packed_no_wrap
          ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable i.val)).toEntry 1 1)) :
    (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 k =
      ZiskFv.Trusted.lane_hi
        ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64
          (chainedSailStates ziskStep init k)).xreg r) := by
  rw [ZiskFv.Compliance.sail_xreg_eq_ziskRegFile ziskStep rowDecodes init k r hr h_regAgree]
  have h_lt := trace.mainTable_index ⟨k, hk⟩
  obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_boot⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem h_lt) Instantiation.RegSlot.b
      (by unfold ZiskFv.Compliance.Instantiation.RegSlot.selector
          simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero,
            dif_pos h_lt] at h_b_src_reg ⊢
          exact h_b_src_reg)
  rcases bootWalk_head_value_strong trace path _ last h_head h_last h_sites h_chain h_boot with
    ⟨h0, h1, h_no_cslot⟩ | ⟨q, h_q, h_qc, h_q0, h_q1, h_max_ts⟩
  · have h_b1_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).b_1 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.b_1 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_no_writes : ∀ m, m < k → ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m hm h_wr
      obtain ⟨w, h_w_mem, h_wc, _⟩ := stepWritesReg_cslot_on_bootWalk_b trace ziskStep rowDecodes
        h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_b_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.b) := by
        intro heq
        have := congrArg Prod.snd heq
        simp only [h_wc] at this; exact absurd this (by decide)
      exact absurd h_wc (h_no_cslot w h_w_mem (by convert h_ne))
    rw [h_b1_eq]
    have h_zero := ziskRegFile_eq_lane_hi_of_bootWalk_zero trace ziskStep rowDecodes
      k hk r hr h_no_writes
    convert h1.symm ▸ h_zero
  · have h_b1_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).b_1 k
        = (eval (trace.mainTable.environment
            (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            trace.programLength trace.program).rowInputVar).core.b_1 := by
      simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
    have h_q_ts_lt : q.timestamp.val < (3 + 4 * k : ℕ) := by
      have h_bound := timestamp_val_le_head_of_mem_chain trace
        (by rcases path with _ | ⟨_, _⟩ <;> simp_all)
        h_sites h_chain h_q
      have h_ne : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some := List.head?_eq_some_head h_ne
      rw [h_head] at h_head_some
      have h_head_id := Option.some.inj h_head_some.symm
      have h_head_ts : (path.head h_ne).timestamp =
          RegSlot.b.readTimestamp
            (mainTableRowAtOrZero trace.program trace.mainTable k) := by
        simp only [Instantiation.RegWalkStep.timestamp]
        congr 1
        · exact congrArg Prod.snd h_head_id
        · simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
          exact congrArg Prod.fst h_head_id
      have h_ms := mainRowAt_main_step trace.mainTable_component h_lt
      have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt
      have h_head_ts_val : (path.head h_ne).timestamp.val = 2 + 4 * k := by
        have : (path.head h_ne).timestamp = (2 : FGL) + (↑k : FGL) * 4 := by
          rw [h_head_ts]; simp [Instantiation.RegSlot.readTimestamp, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (2 : ℕ) ≤ 3) h_cap
      omega
    have h_q_ptr : Transpiler.wrap_to_regidx (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr = r := by
      have h_ne' : path ≠ [] := List.ne_nil_of_mem h_q
      have h_head_some' := List.head?_eq_some_head h_ne'
      rw [h_head] at h_head_some'
      have h_head_id' := Option.some.inj h_head_some'.symm
      have h_head_snd : (path.head h_ne').2 = RegSlot.b := congrArg Prod.snd h_head_id'
      have h_q_ne : q ≠ path.head h_ne' := by
        intro h_eq
        have : q.2 = (path.head h_ne').2 := congrArg Prod.snd h_eq
        rw [h_qc, h_head_snd] at this
        exact absurd this (by decide)
      have h_chain_ptr := bootWalk_head_ptr trace path (path.head h_ne')
        (List.head?_eq_some_head h_ne') h_chain h_sites q h_q h_q_ne
      have h_rc : (q.2.readMessage q.1).ptr =
          (ZiskFv.AirsClean.Main.cMemMessage q.1).ptr := by rw [h_qc]; rfl
      have h_head_ptr : ((path.head h_ne').2.regPreMessage (path.head h_ne').1).ptr =
          (mainTableRowAtOrZero trace.program trace.mainTable k).rom.b_offset_imm0 := by
        rw [h_head_snd]
        simp only [Instantiation.RegSlot.regPreMessage, ZiskFv.AirsClean.Main.bRegPreMessage]
        congr 1; congr 1
        rw [congrArg Prod.fst h_head_id']
        symm; exact mainTableRowAtOrZero_get trace.program trace.mainTable ⟨k, h_lt⟩
      rw [← h_b_ptr, ← h_head_ptr, ← h_chain_ptr, h_rc]
    have h_b1_val : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
          trace.program trace.mainTable).b_1 k
        = (ZiskFv.AirsClean.Main.cMemMessage q.1).value_1 := by
      rw [h_b1_eq]; convert h_q1; rw [h_qc]; rfl
    have h_no_writes_above : ∀ m, q.timestamp.val < 3 + 4 * m → m < k →
        ¬ StepWritesReg ziskStep rowDecodes m r := by
      intro m h_ts_lt hm h_wr
      obtain ⟨w, h_w_mem, h_wc, h_w_row⟩ := stepWritesReg_cslot_on_bootWalk_b trace ziskStep
        rowDecodes h_stepRegWrite_converse h_stepRegWrite_consistent hk r h_b_ptr h_lt
        h_head h_last h_sites h_chain h_boot hm h_wr
      have h_ne_head : w ≠ (eval (trace.mainTable.environment (trace.mainTable.table.get ⟨k, h_lt⟩))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar, Instantiation.RegSlot.b) := by
        intro heq; have := congrArg Prod.snd heq; simp only [h_wc] at this; exact absurd this (by decide)
      have h_w_ts_le := h_max_ts w h_w_mem (by convert h_ne_head) h_wc
      have h_m_lt_n : m < n := Nat.lt_trans hm hk
      have h_lt_m : m < trace.mainTable.table.length := by
        have := trace.mainTable_index ⟨m, h_m_lt_n⟩; omega
      have h_w_ts_val : w.timestamp.val = 3 + 4 * m := by
        have h_ms := mainRowAt_main_step trace.mainTable_component h_lt_m
        have h_cap := main_index_lt_mainFixedCapacity trace.mainTable_component h_lt_m
        have : w.timestamp = (3 : FGL) + (↑m : FGL) * 4 := by
          simp only [Instantiation.RegWalkStep.timestamp, h_wc,
            Instantiation.RegSlot.readTimestamp, h_w_row, h_ms]
        rw [this]
        exact slot_timestamp_val (by norm_num : (3 : ℕ) ≤ 3) h_cap
      omega
    rw [h_b1_val]
    exact cMemMessage_value_eq_lane_hi_of_bootWalk_supplier trace ziskStep rowDecodes
      k hk r hr q (h_sites q h_q) h_qc h_q_ptr h_q_ts_lt h_no_writes_above
      h_stepRegWrite_consistent h_stepRegWrite_converse h_entry_range

end ZiskFv.Compliance
