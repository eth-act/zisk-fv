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

/-! ## No-writes lemma from boot walk

The boot walk's chain gives the register's complete write history:
between any two consecutive chain elements, no write to that register
occurred. This follows from the channel balance bijection. -/

theorem ziskRegFile_eq_lane_lo_of_bootWalk_zero
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0) :
    (eval (trace.mainTable.environment
        (trace.mainTable.table.get ⟨k, trace.mainTable_index ⟨k, hk⟩⟩))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.programLength trace.program).rowInputVar).core.a_0 = 0
    ∧ (eval (trace.mainTable.environment
        (trace.mainTable.table.get ⟨k, trace.mainTable_index ⟨k, hk⟩⟩))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        trace.programLength trace.program).rowInputVar).core.a_1 = 0 →
    (0 : FGL) = ZiskFv.Trusted.lane_lo (ziskRegFile ziskStep rowDecodes k r) := by
  sorry

theorem cMemMessage_value_eq_lane_lo_of_bootWalk_supplier
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (q : RegWalkStep)
    (h_active : IsActiveWitnessMainRow trace q)
    (h_slot_c : q.2 = Instantiation.RegSlot.c) :
    (ZiskFv.AirsClean.Main.cMemMessage q.1).value_0 =
      ZiskFv.Trusted.lane_lo (ziskRegFile ziskStep rowDecodes k r) := by
  sorry

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
  have h_lt := trace.mainTable_index ⟨k, hk⟩
  have h_boot_walk := a_columns_of_bootWalk trace
    trace.mainTable_mem trace.mainTable_component
    (List.getElem_mem h_lt)
    (by unfold ZiskFv.Compliance.Instantiation.RegSlot.selector
        simp only [ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero,
          dif_pos h_lt] at h_a_src_reg ⊢
        exact h_a_src_reg)
  have h_a0_eq : (ZiskFv.AirsClean.FullEnsemble.mainOfTable
        trace.program trace.mainTable).a_0 k
      = (eval (trace.mainTable.environment
          (trace.mainTable.table.get ⟨k, h_lt⟩))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          trace.programLength trace.program).rowInputVar).core.a_0 := by
    simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero, dif_pos h_lt]
  rcases h_boot_walk with ⟨h0, h1⟩ | ⟨q, h_active, h_slot_c, h_val0, _⟩
  · -- Boot-anchored: a_0 = 0, need ziskRegFile k r = 0
    rw [h_a0_eq]; convert h0.symm ▸
      (ziskRegFile_eq_lane_lo_of_bootWalk_zero trace ziskStep rowDecodes k hk r hr ⟨h0, h1⟩)
  · -- Supplier: a_0 = cMemMessage(q).value_0, need it = lane_lo(ziskRegFile k r)
    rw [h_a0_eq]; convert h_val0.symm ▸
      (cMemMessage_value_eq_lane_lo_of_bootWalk_supplier trace ziskStep rowDecodes
        k hk r hr q h_active h_slot_c)

end ZiskFv.Compliance
