import ZiskFv.Compliance.RegisterWalk

/-!
# Main's three memory-bus slots never share a message

`MemBusSourceExclusivity` rules out an operand-source flag combination by showing that the
multiplicity of every interaction carrying the offending message is one fixed nonzero value. That
works at `mem_op = 4` and `mem_op = 7`, where only one shape of Main emission can occur. It fails at
`mem_op = 5`, which **two** shapes reach: a b-side current access rides at `-3` there and a
store-side current access at `-2`.

The message itself separates them, through its timestamp. Main's three accesses happen at
`1 + main_step * 4`, `2 + main_step * 4` and `3 + main_step * 4`
(`Main/Constraints.lean:363,376,389`), `main_step` is the row index, and the table's own
fixed-column schema caps that index at `mainFixedCapacity = 2^22`. So every access timestamp is
below `2^24`, no wraparound can occur, and the residue mod `4` is an invariant of the slot.
-/

namespace ZiskFv.Compliance

open Air.Flat (Table)
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.Main (MainRowWithRom componentWithRomMemAndOpBus)
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- Every row of a Main-component table carries its own index in `main_step`, and that index is
below the component's fixed-column capacity. -/
theorem exists_main_step_index_of_mem
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ∃ index : ℕ, index < ZiskFv.AirsClean.Main.mainFixedCapacity ∧
      (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.main_step
        = (index : FGL) := by
  obtain ⟨index, h_index, h_rowAt⟩ := exists_index_of_mem_mainTable h_component h_row
  refine ⟨index, main_index_lt_mainFixedCapacity h_component h_index, ?_⟩
  rw [h_rowAt]
  exact (mainStepIndexFixedFacts_of_component_fixedColumns
    (numInstructions := table.table.length) program table h_component
    (fun i => i.isLt)).main_step_eq_index ⟨index, h_index⟩

/-- An access timestamp `k + 4 * index` with `k ≤ 3` and `index < 2^22` evaluates without wrapping,
so its `val` is the integer `k + 4 * index`. -/
theorem slot_timestamp_val
    {k index : ℕ} (h_k : k ≤ 3) (h_index : index < ZiskFv.AirsClean.Main.mainFixedCapacity) :
    ((k : FGL) + (index : FGL) * 4).val = k + 4 * index := by
  have h_cap : index < 4194304 := by
    simpa [ZiskFv.AirsClean.Main.mainFixedCapacity] using h_index
  have h_prime : GL_prime = 18446744069414584321 := rfl
  have h_k_cast : ((k : ℕ) : FGL).val = k := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h_i_cast : ((index : ℕ) : FGL).val = index := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h_mul : ((index : FGL) * 4).val = index * 4 := by
    rw [Fin.val_mul, h_i_cast]
    exact Nat.mod_eq_of_lt (by omega)
  rw [Fin.val_add, h_k_cast, h_mul, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Two of Main's slots never read at the same time.** The offsets `1`, `2`, `3` sit in distinct
residues mod `4`, and no wraparound can move between them. -/
theorem slot_timestamp_ne
    {k₁ k₂ index₁ index₂ : ℕ}
    (h_k₁ : k₁ ≤ 3) (h_k₂ : k₂ ≤ 3) (h_ne : k₁ ≠ k₂)
    (h_i₁ : index₁ < ZiskFv.AirsClean.Main.mainFixedCapacity)
    (h_i₂ : index₂ < ZiskFv.AirsClean.Main.mainFixedCapacity) :
    ((k₁ : FGL) + (index₁ : FGL) * 4) ≠ ((k₂ : FGL) + (index₂ : FGL) * 4) := by
  intro h
  have h_val := congrArg Fin.val h
  rw [slot_timestamp_val h_k₁ h_i₁, slot_timestamp_val h_k₂ h_i₂] at h_val
  omega

end ZiskFv.Compliance
