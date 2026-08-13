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

end ZiskFv.Compliance
