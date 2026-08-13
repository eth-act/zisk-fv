import ZiskFv.Compliance.RegisterValueTelescope

/-!
# There is exactly one Main table in an accepted witness — #330 Phase 4 S3 groundwork

The register telescope walks backwards from a read to the write that supplied it. To turn "**a**
write the walk lands on" into "**the last** write before this step" — which is what the ZisK
register file records — the walk has to visit every earlier access to that register. That coverage
fact rests on a counting argument: at most one interaction may carry a given `mem_op = 3` read
message, so a register-pre push is answered by exactly one pull.

Two Main-component tables would break the count outright: each would emit its own copy of every
access, and a message pulled twice can be pushed twice. So the counting argument needs **table
uniqueness**, and that is what this module proves.

## Why it is provable rather than assumed

`fullRv64imSoundEnsemble` declares the Main component exactly once, and `same_circuits` pins each
witness table's component by index, so uniqueness is a fact about the ensemble rather than a
property a prover must be trusted to supply. The discriminator is `rawWidth`, measured here:

```
verifier 0, RegisterBoundary 4, MemAlignReadByte 10, MemAlignByte 16, MemAlign 30,
MemAlignRangeSlice 1, MemAlignRomSlice 6, Mem 17, RegisterStepRangeSlice 1,
SpecifiedRangesSlice 1, ArithDiv 43, ArithMul 44, BinaryExtension.shiftStaticLookup 29,
Binary.staticLookup 39, BinaryAdd 10, Main 41
```

`41` occurs once. Note the widths are *not* pairwise distinct — `MemAlignReadByte` and `BinaryAdd`
are both `10`, and three slices are `1` — so this argument works for Main and would need a
different discriminator for another table.

The alternative would have been an `AcceptedZiskTrace` field in the shape of
`mem_replay_source_covers`, which is how the mutable-Mem table's uniqueness is currently handled.
That is a caller-supplied assumption. Phase 4 exists to *remove* assumptions, so paying one to
close it would be the trade the anti-laundering rule forbids.

## Why the widths are proved one at a time

Each width needs `circuit_norm` to run over a full elaborated circuit. Asking for all sixteen inside
one `simp only` exhausts eight million heartbeats at `isDefEq`; split into separate declarations
they each go through, and the list lemma then only rewrites with numerals.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep)

/-! ## The measured raw widths -/

theorem rawWidth_main {length : ℕ} (program : Program length) :
    (Main.componentWithRomMemAndOpBus length program).rawWidth = 41 := by
  simp only [Main.componentWithRomMemAndOpBus]

theorem rawWidth_registerBoundary :
    (RegisterBoundary.component : Component FGL).rawWidth = 4 := by
  simp only [RegisterBoundary.component, GeneralFormalCircuit.size_eq, circuit_norm,
    RegisterBoundary.circuit]
  norm_num

theorem rawWidth_memAlignReadByte :
    (MemAlignReadByte.component : Component FGL).rawWidth = 10 := by
  simp only [MemAlignReadByte.component, GeneralFormalCircuit.size_eq, circuit_norm,
    MemAlignReadByte.circuit]
  norm_num

theorem rawWidth_memAlignByte :
    (MemAlignByte.component : Component FGL).rawWidth = 16 := by
  simp only [MemAlignByte.component, GeneralFormalCircuit.size_eq, circuit_norm,
    MemAlignByte.circuit]
  norm_num

theorem rawWidth_memAlign :
    (MemAlign.component : Component FGL).rawWidth = 30 := by
  simp only [MemAlign.component, GeneralFormalCircuit.size_eq, circuit_norm, MemAlign.circuit]

theorem rawWidth_memAlignRangeSlice :
    (MemAlignRangeSlice.component : Component FGL).rawWidth = 1 := by
  simp only [MemAlignRangeSlice.component, GeneralFormalCircuit.size_eq, circuit_norm,
    MemAlignRangeSlice.circuit]
  norm_num

theorem rawWidth_memAlignRomSlice :
    (MemAlignRomSlice.component : Component FGL).rawWidth = 6 := by
  simp only [MemAlignRomSlice.component, GeneralFormalCircuit.size_eq, circuit_norm,
    MemAlignRomSlice.circuit]
  norm_num

theorem rawWidth_mem :
    (Mem.componentWithDualMemBus : Component FGL).rawWidth = 17 := by
  simp only [Mem.componentWithDualMemBus]

theorem rawWidth_registerStepRangeSlice :
    (RegisterStepRangeSlice.component : Component FGL).rawWidth = 1 := by
  simp only [RegisterStepRangeSlice.component, GeneralFormalCircuit.size_eq, circuit_norm,
    RegisterStepRangeSlice.circuit]

theorem rawWidth_specifiedRangesSlice :
    (SpecifiedRangesSlice.component : Component FGL).rawWidth = 1 := by
  simp only [SpecifiedRangesSlice.component, GeneralFormalCircuit.size_eq, circuit_norm,
    SpecifiedRangesSlice.circuit]

theorem rawWidth_arithDiv :
    (ArithDiv.component : Component FGL).rawWidth = 43 := by
  simp only [ArithDiv.component, GeneralFormalCircuit.size_eq, circuit_norm, ArithDiv.circuit]
  norm_num

theorem rawWidth_arithMul :
    (ArithMul.componentComplete : Component FGL).rawWidth = 44 := by
  simp only [ArithMul.componentComplete, GeneralFormalCircuit.size_eq, circuit_norm,
    ArithMul.circuitComplete]
  norm_num

theorem rawWidth_shiftStaticLookup :
    (BinaryExtension.shiftStaticLookupComponent : Component FGL).rawWidth = 29 := by
  simp only [BinaryExtension.shiftStaticLookupComponent, GeneralFormalCircuit.size_eq, circuit_norm,
    BinaryExtension.shiftStaticLookupCircuit]
  norm_num

theorem rawWidth_binaryStaticLookup :
    (Binary.staticLookupComponent : Component FGL).rawWidth = 39 := by
  simp only [Binary.staticLookupComponent, GeneralFormalCircuit.size_eq, circuit_norm,
    Binary.staticLookupCircuit]
  norm_num

theorem rawWidth_binaryAdd :
    (BinaryAdd.component : Component FGL).rawWidth = 10 := by
  simp only [BinaryAdd.component, GeneralFormalCircuit.size_eq, circuit_norm, BinaryAdd.circuit]
  norm_num

/-! ## The ensemble's width profile, and what it pins -/

/-- **The ensemble's raw widths, in table order.** Only the numerals are rewritten here; the
    circuit-level work is in the sixteen lemmas above. -/
theorem ensemble_rawWidths {length : ℕ} (program : Program length) :
    ((fullRv64imEnsemble length program).ensemble.allTables.map (·.rawWidth))
      = [0, 4, 10, 16, 30, 1, 6, 17, 1, 1, 43, 44, 29, 39, 10, 41] := by
  simp only [fullRv64imEnsemble, fullRv64imSoundEnsemble, SoundEnsemble.toFormal,
    Ensemble.allTables, SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables,
    List.map_cons, List.map_nil, SoundEnsemble.empty, Ensemble.verifierTable,
    rawWidth_main, rawWidth_registerBoundary, rawWidth_memAlignReadByte, rawWidth_memAlignByte,
    rawWidth_memAlign, rawWidth_memAlignRangeSlice, rawWidth_memAlignRomSlice, rawWidth_mem,
    rawWidth_registerStepRangeSlice, rawWidth_specifiedRangesSlice, rawWidth_arithDiv,
    rawWidth_arithMul, rawWidth_shiftStaticLookup, rawWidth_binaryStaticLookup,
    rawWidth_binaryAdd]
  rfl

/-- A witness table carrying the Main component sits at index `15`, because that is the only place
    the ensemble's width profile shows `41`. -/
theorem main_table_index {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    {t : Table FGL} (h_mem : t ∈ witness.allTables)
    (h_component : t.component = Main.componentWithRomMemAndOpBus length program) :
    witness.allTables[15]? = some t := by
  obtain ⟨i, h_i⟩ := List.mem_iff_getElem?.mp h_mem
  have h_comp : ((fullRv64imEnsemble length program).ensemble.allTables)[i]?
      = some (Main.componentWithRomMemAndOpBus length program) := by
    rw [← witness.allTables_map_component, List.getElem?_map, h_i, Option.map_some,
      h_component]
  have h_width : ([0, 4, 10, 16, 30, 1, 6, 17, 1, 1, 43, 44, 29, 39, 10, 41] : List ℕ)[i]?
      = some 41 := by
    rw [← ensemble_rawWidths program, List.getElem?_map, h_comp, Option.map_some,
      rawWidth_main]
  have h_lt : i < 16 := by
    by_contra h_ge
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h_ge)] at h_width
    simp at h_width
  interval_cases i <;> simp_all

/-- **At most one witness table carries the Main component.**

    This is what turns the register telescope's counting argument into a real bound: with a single
    Main table, two interactions carrying the same `mem_op = 3` read message would have to be the
    same row, because equal messages force equal timestamps and a timestamp names the slot and the
    row index. -/
theorem main_table_unique {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    {t₁ t₂ : Table FGL}
    (h₁ : t₁ ∈ witness.allTables) (h₂ : t₂ ∈ witness.allTables)
    (hc₁ : t₁.component = Main.componentWithRomMemAndOpBus length program)
    (hc₂ : t₂.component = Main.componentWithRomMemAndOpBus length program) :
    t₁ = t₂ :=
  Option.some.inj
    ((main_table_index witness h₁ hc₁).symm.trans (main_table_index witness h₂ hc₂))

/-! ## Pull-uniqueness: a read timestamp names its slot and its row

An access timestamp is `offset + 4 * index` with `offset ∈ {1, 2, 3}` picking the slot and `index`
the row. Both live far below the field's wrap point, so the arithmetic is over `ℕ` and the naming
is exact. With `main_table_unique` supplying the table, a `mem_op = 3` read message therefore
determines the walk step that emitted it — which is what makes the register-pre push it answers
unique. -/

/-- Which of the three access slots a timestamp offset names. -/
private def slotOffset : RegSlot → ℕ
  | RegSlot.a => 1
  | RegSlot.b => 2
  | RegSlot.c => 3

private lemma slotOffset_le_three (s : RegSlot) : slotOffset s ≤ 3 := by
  cases s <;> decide

private lemma slotOffset_inj {s₁ s₂ : RegSlot} (h : slotOffset s₁ = slotOffset s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> simp_all [slotOffset]

/-- **`main_step` is the row's own index**, for any in-range row of any Main-component table — not
    only the executed prefix. Same indexed fixed schema `regSlot_timestamp_bound_of_mainTable` uses;
    the walk's providers may be padding rows, so the fact has to cover them. -/
theorem mainRowAt_main_step {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    {index : ℕ} (h_index : index < table.table.length) :
    (mainTableRowAtOrZero program table index).rom.main_step = (index : FGL) :=
  (mainStepIndexFixedFacts_of_component_fixedColumns
    (numInstructions := table.table.length) program table h_component
    (fun i => i.isLt)).main_step_eq_index ⟨index, h_index⟩

private lemma readTimestamp_eq_offset {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    {index : ℕ} (h_index : index < table.table.length) (s : RegSlot) :
    s.readTimestamp (mainTableRowAtOrZero program table index)
      = ((slotOffset s : ℕ) : FGL) + ((index : ℕ) : FGL) * 4 := by
  cases s <;>
    simp [RegSlot.readTimestamp, mainRowAt_main_step h_component h_index, slotOffset]

/-- **A read timestamp names one slot of one row.** The offsets `1`, `2`, `3` sit in distinct
    residues mod `4` and the row index is capped by the table's own fixed domain, so no wraparound
    can confuse two accesses. -/
theorem slot_index_eq_of_readTimestamp_eq
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    {i₁ i₂ : ℕ} (h₁ : i₁ < table.table.length) (h₂ : i₂ < table.table.length)
    {s₁ s₂ : RegSlot}
    (h : s₁.readTimestamp (mainTableRowAtOrZero program table i₁)
      = s₂.readTimestamp (mainTableRowAtOrZero program table i₂)) :
    s₁ = s₂ ∧ i₁ = i₂ := by
  rw [readTimestamp_eq_offset h_component h₁, readTimestamp_eq_offset h_component h₂] at h
  have hv := congrArg Fin.val h
  rw [slot_timestamp_val (slotOffset_le_three s₁) (main_index_lt_mainFixedCapacity h_component h₁),
    slot_timestamp_val (slotOffset_le_three s₂)
      (main_index_lt_mainFixedCapacity h_component h₂)] at hv
  have h_le₁ := slotOffset_le_three s₁
  have h_le₂ := slotOffset_le_three s₂
  exact ⟨slotOffset_inj (by omega), by omega⟩

/-- **Pull-uniqueness.** Two active register slots of the witness that carry the same `mem_op = 3`
    read message are the same slot of the same row.

    This is the counting bound the register telescope needs: a register-pre push is answered by a
    pull, and there is at most one pull to answer it, so the answering step is determined. -/
theorem readMessage_inj {n : ℕ} (trace : AcceptedZiskTrace n) {p q : RegWalkStep}
    (h_p : IsActiveWitnessMainRow trace p) (h_q : IsActiveWitnessMainRow trace q)
    (h : p.2.readMessage p.1 = q.2.readMessage q.1) :
    p = q := by
  obtain ⟨rp, sp⟩ := p
  obtain ⟨rq, sq⟩ := q
  obtain ⟨tp, h_tp, h_cp, ip, h_ip, h_rp, -⟩ := h_p
  obtain ⟨tq, h_tq, h_cq, iq, h_iq, h_rq, -⟩ := h_q
  subst h_rp
  subst h_rq
  have h_tables : tp = tq := main_table_unique trace.witness h_tp h_tq h_cp h_cq
  subst h_tables
  have h_ts : sp.readTimestamp (mainTableRowAtOrZero trace.program tp ip)
      = sq.readTimestamp (mainTableRowAtOrZero trace.program tp iq) := by
    simpa using congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h
  obtain ⟨h_slot, h_index⟩ := slot_index_eq_of_readTimestamp_eq h_cp h_ip h_iq h_ts
  subst h_slot
  subst h_index
  rfl

end ZiskFv.Compliance
