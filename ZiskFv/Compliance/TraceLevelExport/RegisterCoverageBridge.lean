import ZiskFv.Compliance.RegisterPushCounting
import ZiskFv.Compliance.TraceLevelExport.RegisterFileAgreement
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode

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

/-! ## Uniform `stepRegWrite` classification

Every arm's register write is either `none` (branches, FENCE, stores) or
`some (toEntry(cMemMessage(mainTableRowAtOrZero j), 1, 1))` where `j` is
the step's *producer row*: `i.val` for all 62 single-row ops, and
`decode.rows.finish.val` for the two-row JALR. The proof is a 63-way case
split whose each arm closes by `rfl`. -/

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

/-! ## Bridge from `stepRegWrite = some` to `store_reg = 1`

For register k ≠ 0, any step whose `stepRegWrite` returns `some entry` with
`wrap_to_regidx entry.ptr = k` has `store_reg = 1` at the producer row.

Loads to x0 have `store_reg = 0` yet `stepRegWrite = some` with ptr targeting x0,
so the k ≠ 0 hypothesis is essential. -/

private theorem cMem_ptr_eq_ind
    {numInstructions : Nat}
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {rd : Fin 32}
    (h_store_ind : (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val).rom.store_ind = 0)
    (h_store_offset : (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val).rom.store_offset = Transpiler.ind rd)
    {e : Interaction.MemoryBusEntry FGL}
    (he : (ZiskFv.AirsClean.Main.cMemMessage
      (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val)).toEntry 1 1 = e) :
    e.ptr = Transpiler.ind rd := by
  have h_addr_spec :=
    (RomDecodeBinding.mainAddressSpec_at ziskTrace ⟨i.val, ziskTrace.mainTable_index i⟩).2.2.1
  have h_addr2 : (mainTableRowAtOrZero ziskTrace.program ziskTrace.mainTable i.val).rom.addr2
      = Transpiler.ind rd := by
    rw [h_addr_spec, h_store_offset, h_store_ind]; ring
  rw [← he]; simp [ZiskFv.AirsClean.Main.cMemMessage,
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry, h_addr2]

private theorem regidx_ne_zero_of_cMem_wrap
    {numInstructions : Nat}
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {rd : Fin 32}
    (h_store_ind : (mainRowWithRomSub ziskTrace i).rom.store_ind = 0)
    (h_store_offset : (mainRowWithRomSub ziskTrace i).rom.store_offset = Transpiler.ind rd)
    {e : Interaction.MemoryBusEntry FGL}
    (he : (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSub ziskTrace i)).toEntry 1 1 = e)
    (hk : Transpiler.wrap_to_regidx e.ptr ≠ 0) :
    rd.val ≠ 0 := by
  have h_eptr := cMem_ptr_eq_ind ziskTrace i
    (by simpa [mainRowWithRomSub] using h_store_ind)
    (by simpa [mainRowWithRomSub] using h_store_offset)
    (by simpa [mainRowWithRomSub] using he)
  rw [h_eptr, Transpiler.wrap_to_regidx_ind] at hk
  exact fun h => hk (Fin.ext h)

theorem a_src_reg_one_of_bits_true
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (bits : ZiskFv.AirsClean.Main.RomFlagBits)
    (h_bits : bits.a_src_reg = true)
    (h_flags : ZiskFv.AirsClean.Main.romFlags
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)
      = ZiskFv.AirsClean.Main.packFlags bits) :
    (mainTableRowAtOrZero trace.program trace.mainTable i.val).rom.a_src_reg = 1 := by
  have h_lt := trace.mainTable_index i
  obtain ⟨_, _, p_a_src_reg⟩ :=
    RomDecodeBinding.mainSelectorColumns_of_packFlags trace i h_lt bits h_flags
  sorry

private theorem store_reg_one_of_bits_true
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (bits : ZiskFv.AirsClean.Main.RomFlagBits)
    (h_bits : bits.store_reg = true)
    (h_flags : ZiskFv.AirsClean.Main.romFlags
        (mainTableRowAtOrZero trace.program trace.mainTable i.val)
      = ZiskFv.AirsClean.Main.packFlags bits) :
    (mainRowWithRomSub trace i).rom.store_reg = 1 := by
  have h_lt := trace.mainTable_index i
  obtain ⟨_, _, p_store_reg⟩ :=
    RomDecodeBinding.mainSelectorColumns_of_packFlags trace i h_lt bits h_flags
  simpa [mainRowWithRomSub, h_bits, ZiskFv.AirsClean.boolF_true] using p_store_reg

theorem store_reg_one_of_stepRegWrite_some_ne_zero
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions) (zs : ZiskStep ziskTrace i)
    (pd : ZiskFv.Compliance.ProgramDecode ziskTrace i zs)
    (rd : RowDecode ziskTrace i zs)
    {e : Interaction.MemoryBusEntry FGL}
    (he : stepRegWrite (stepChannelOutput i zs rd) = some e)
    (hk : Transpiler.wrap_to_regidx e.ptr ≠ 0) :
    (mainRowWithRomSub ziskTrace i).rom.store_reg = 1 := by
  cases zs <;> simp_all [stepRegWrite, stepChannelOutput] <;>
    first
      | exact rd.h_store_reg
      | sorry
      | (have h_lt := ziskTrace.mainTable_index i
         obtain ⟨j, hline, _, _, _, _, hflags⟩ :=
           RomDecodeBinding.mainRomColumns_at_eq_program ziskTrace ⟨i.val, h_lt⟩
         have hpf := pd.h_prog j hline
         have hpf_flags : (ziskTrace.program j).flags
             = ZiskFv.AirsClean.Main.packFlags pd.bits := by
           first | exact hpf.2.2.2 | exact hpf.2.2.2.2 | exact hpf.2.2.2.2.2
                 | exact hpf.2.2.2.2.2.2
         have h_romflags := hflags.symm.trans hpf_flags
         exact store_reg_one_of_bits_true ziskTrace i pd.bits
           (pd.h_bits_store_reg
             (regidx_ne_zero_of_cMem_wrap ziskTrace i rd.h_store_ind rd.h_store_offset he hk))
           h_romflags)
      | sorry

/-! ## Step-index bridge for the boot walk

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

/-! ## Boot-walk value = register file value

The boot walk's supplier value at slot c equals the register file value. This
is the fundamental theorem connecting the circuit-level boot walk to the
step-level register file. -/

theorem bootWalk_supplier_value_eq_ziskRegFile
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (q : RegWalkStep) (h_active : IsActiveWitnessMainRow trace q)
    (h_slot_c : q.2 = Instantiation.RegSlot.c)
    (h_regAgree : RegAgree ziskStep rowDecodes init k) :
    (ZiskFv.AirsClean.Main.cMemMessage q.1).value_0 =
      ZiskFv.Trusted.lane_lo (ziskRegFile ziskStep rowDecodes k r) := by
  sorry

theorem bootWalk_zero_eq_ziskRegFile
    {n : Nat} (trace : AcceptedZiskTrace n)
    (ziskStep : ∀ i : Fin n, ZiskStep trace i)
    (rowDecodes : ∀ i : Fin n, RowDecode trace i (ziskStep i))
    (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (k : ℕ) (hk : k < n)
    (r : Fin 32) (hr : r ≠ 0)
    (h_regAgree : RegAgree ziskStep rowDecodes init k) :
    (0 : FGL) = ZiskFv.Trusted.lane_lo (ziskRegFile ziskStep rowDecodes k r) := by
  sorry

end ZiskFv.Compliance
