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

open ZiskFv.Airs.MemoryBus in
/-- The register-write entry at a step that performs a write satisfies the
    chunk-range and no-wrap constraints required by `lane_lo_entryRegValue`.

    Derivation path (per-case, not yet kernel-reduced):
    * **`store_pc = 0`** (ALU/shift/M-ext/loads): `value_0 = c_0`, `value_1 = c_1`.
      The op-bus balance (`trace.channels_balanced`) matches the Main row to a
      provider row whose `c_lo`/`c_hi` are range-checked to < 2^32 via
      `ComponentSpecFacts`.  The packed sum is
      `c_0.val + c_1.val * 2^32 < 2^32 + (2^32-1)*2^32 = 2^64 - 2^32 < GL_prime`
      when `c_1.val < 2^32 - 1`, or provable per-opcode when the result is in
      the "high-register" range.
    * **`store_pc = 1`** (JAL/JALR/AUIPC): `value_0 = pc + jmp_offset2`,
      `value_1 = 0`.  `0 < 2^32` is trivial; the PC + offset bound follows
      from `MainSequentialPcDomain` / `h_pc_offset_lt_2_32` domain bounds.
      Packed no-wrap is immediate since `value_1 = 0`. -/
private theorem cMemMessage_toEntry_range_of_stepRegWrite
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (j : ℕ) (h_j_lt_n : j < n) (_h_j_lt_table : j < trace.mainTable.table.length)
    (h_write : stepRegWrite (stepChannelOutput ⟨j, h_j_lt_n⟩
        (ziskStep ⟨j, h_j_lt_n⟩) (rowDecodes ⟨j, h_j_lt_n⟩))
      = some ((cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1)) :
    memory_entry_chunks_in_range
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1)
    ∧ memory_entry_packed_no_wrap
      ((cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable j)).toEntry 1 1) := by
  sorry -- #330-S3: op-bus balance → provider range constraints per case above

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
      ¬ StepWritesReg ziskStep rowDecodes m r) :
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
    · sorry  -- contradicts h_slot_c: the c-slot is active so stepRegWrite ≠ none
    · rcases h_j' with rfl | rfl
      · exact h_some
      · sorry  -- JALR: stepProducerRow = j (rows.finish = ⟨j, _⟩)
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
  have ⟨h_chunks, h_no_wrap⟩ := cMemMessage_toEntry_range_of_stepRegWrite trace ziskStep
    rowDecodes j h_j_lt_n h_j_lt_table h_write
  have h_lane := lane_lo_entryRegValue
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

set_option maxHeartbeats 400000 in
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
        (mainTableRowAtOrZero trace.program trace.mainTable k).rom.a_offset_imm0 = r) :
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
  rcases bootWalk_head_value trace path _ last h_head h_last h_chain h_boot with
    ⟨h0, h1⟩ | ⟨q, h_q, h_qc, h_q0, h_q1⟩
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
      sorry -- chain completeness: boot-anchored walk has no c-slot, so no writes to r
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
      sorry -- chain completeness: q is the first c-slot, so no writes after q
    rw [h_a0_val]
    exact cMemMessage_value_eq_lane_lo_of_bootWalk_supplier trace ziskStep rowDecodes
      k hk r hr q (h_sites q h_q) h_qc h_q_ptr h_q_ts_lt h_no_writes_above

end ZiskFv.Compliance
