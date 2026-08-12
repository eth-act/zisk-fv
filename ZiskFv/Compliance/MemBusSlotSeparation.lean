import ZiskFv.Compliance.RegisterWalk
import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusSourceExclusivity

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

open Air.Flat
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


/-- The b-side and store-side current accesses of any two Main rows carry different messages: their
timestamps are `2 + 4 * index` and `3 + 4 * index`, which never coincide. -/
theorem cMem_message_ne_bMem_message
    {length : ℕ} {program : Program length} {tblC tblB : Table FGL}
    (h_compC : tblC.component = componentWithRomMemAndOpBus length program)
    (h_compB : tblB.component = componentWithRomMemAndOpBus length program)
    {rC rB : Array FGL} (h_rC : rC ∈ tblC.table) (h_rB : rB ∈ tblB.table)
    (h : eval (tblC.environment rC)
          (ZiskFv.AirsClean.Main.cMemMessageExpr
            (componentWithRomMemAndOpBus length program).rowInputVar)
        = eval (tblB.environment rB)
          (ZiskFv.AirsClean.Main.bMemMessageExpr
            (componentWithRomMemAndOpBus length program).rowInputVar)) :
    False := by
  obtain ⟨iC, h_iC, h_msC⟩ := exists_main_step_index_of_mem h_compC h_rC
  obtain ⟨iB, h_iB, h_msB⟩ := exists_main_step_index_of_mem h_compB h_rB
  have h_ts := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h
  rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr,
    ZiskFv.AirsClean.Main.eval_bMemMessageExpr] at h_ts
  change 3 + (eval (tblC.environment rC)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.main_step * 4
    = 2 + (eval (tblB.environment rB)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.main_step * 4 at h_ts
  rw [h_msC, h_msB] at h_ts
  refine slot_timestamp_ne (k₁ := 3) (k₂ := 2) (by norm_num) (by norm_num) (by norm_num)
    h_iC h_iB ?_
  simpa using h_ts


/-- The store-side twin of `cMem_message_ne_bMem_message`. -/
theorem bMem_message_ne_cMem_message
    {length : ℕ} {program : Program length} {tblB tblC : Table FGL}
    (h_compB : tblB.component = componentWithRomMemAndOpBus length program)
    (h_compC : tblC.component = componentWithRomMemAndOpBus length program)
    {rB rC : Array FGL} (h_rB : rB ∈ tblB.table) (h_rC : rC ∈ tblC.table)
    (h : eval (tblB.environment rB)
          (ZiskFv.AirsClean.Main.bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)
        = eval (tblC.environment rC)
          (ZiskFv.AirsClean.Main.cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)) :
    False :=
  cMem_message_ne_bMem_message h_compC h_compB h_rC h_rB h.symm

/-! ## The `mem_op = 5` instances

With the slots separated, the multiplicity *is* constant once the reference slot is fixed: every
interaction carrying a b-side current's message is itself a b-side current (`-3`), and every
interaction carrying a store-side current's message is itself a store-side current (`-2`). -/

/-- Reference: a b-side current access at `mem_op = 5`. -/
theorem memBus_mult_eq_neg_three_of_msg_eq_bMem_mem_op_five
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {tblRef : Table FGL} (h_tblRef : tblRef ∈ witness.allTables)
    (h_compRef : tblRef.component = componentWithRomMemAndOpBus length program)
    {rRef : Array FGL} (h_rRef : rRef ∈ tblRef.table)
    (h_ref_op : (eval (tblRef.environment rRef)
      (ZiskFv.AirsClean.Main.bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 5)
    {j : Interaction FGL} (h_j : j ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_msg : j.msg =
      (((MemBusChannel.emitted
        (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
          + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
          + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg))
        (ZiskFv.AirsClean.Main.bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (tblRef.environment rRef)).msg) :
    j.mult = -3 :=
  memBus_mult_eq_of_msg_eq_mem_op_high h_constraints h_specs
    (by decide) (by decide) (by decide)
    (fun _ _ _ h1 h2 h3 _ => (main_aMem_mem_op_ne_five h1 h2 h3).elim)
    (fun _ _ _ h1 h2 h3 h4 _ => main_bMem_mult_of_mem_op_five h1 h2 h3 h4)
    (fun _ h_comp h_row _ _ _ _ h_full =>
      (cMem_message_ne_bMem_message h_comp h_compRef h_row h_rRef h_full).elim)
    h_ref_op h_j h_msg

/-- Reference: a store-side current access at `mem_op = 5`. -/
theorem memBus_mult_eq_neg_two_of_msg_eq_cMem_mem_op_five
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {tblRef : Table FGL} (h_tblRef : tblRef ∈ witness.allTables)
    (h_compRef : tblRef.component = componentWithRomMemAndOpBus length program)
    {rRef : Array FGL} (h_rRef : rRef ∈ tblRef.table)
    (h_ref_op : (eval (tblRef.environment rRef)
      (ZiskFv.AirsClean.Main.cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 5)
    {j : Interaction FGL} (h_j : j ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_msg : j.msg =
      (((MemBusChannel.emitted
        (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
          + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
          + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg))
        (ZiskFv.AirsClean.Main.cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (tblRef.environment rRef)).msg) :
    j.mult = -2 :=
  memBus_mult_eq_of_msg_eq_mem_op_high h_constraints h_specs
    (by decide) (by decide) (by decide)
    (fun _ _ _ h1 h2 h3 _ => (main_aMem_mem_op_ne_five h1 h2 h3).elim)
    (fun _ h_comp h_row _ _ _ _ h_full =>
      (bMem_message_ne_cMem_message h_comp h_compRef h_row h_rRef h_full).elim)
    (fun _ _ _ h1 h2 h3 h4 _ => main_cMem_mult_of_mem_op_five h1 h2 h3 h4)
    h_ref_op h_j h_msg


/-! ## Exclusivity for the remaining two slots

With `mem_op = 4`, `5` and `7` all covered, every flag combination that would put two sources on one
slot is ruled out. -/

set_option maxHeartbeats 1000000 in
/-- **A b-side register read is not also a memory or indirect read.** -/
theorem main_b_src_mem_and_ind_zero_of_b_src_reg
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (h_reg : (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 1) :
    (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem = 0
      ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind = 0 := by
  obtain ⟨-, -, b_mem, b_ind, b_reg, -⟩ :=
    main_source_flags_boolean h_component (h_constraints table h_table) h_row
  rcases zero_or_one_of_bool b_mem with h_m | h_m <;>
    rcases zero_or_one_of_bool b_ind with h_i | h_i
  · exact ⟨h_m, h_i⟩
  · exfalso
    have h_op : (eval (table.environment row)
        (ZiskFv.AirsClean.Main.bMemMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 4 := by
      rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr]
      change ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 4
      rw [h_m, h_i, h_reg]; norm_num
    exact no_balanced_message_with_constant_nonzero_mult h_balanced (m := -2) (by decide)
      (main_bMem_interaction_mem_witness h_table h_component h_row)
      (main_bMem_mult_eq_neg_two_of_mem_op_four b_mem b_ind b_reg h_op)
      (fun i h_i' h_msg _ =>
        memBus_mult_eq_neg_two_of_msg_eq_mem_op_four h_constraints h_specs h_op h_i' h_msg)
  · exfalso
    have h_op : (eval (table.environment row)
        (ZiskFv.AirsClean.Main.bMemMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 4 := by
      rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr]
      change ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 4
      rw [h_m, h_i, h_reg]; norm_num
    exact no_balanced_message_with_constant_nonzero_mult h_balanced (m := -2) (by decide)
      (main_bMem_interaction_mem_witness h_table h_component h_row)
      (main_bMem_mult_eq_neg_two_of_mem_op_four b_mem b_ind b_reg h_op)
      (fun i h_i' h_msg _ =>
        memBus_mult_eq_neg_two_of_msg_eq_mem_op_four h_constraints h_specs h_op h_i' h_msg)
  · exfalso
    have h_op : (eval (table.environment row)
        (ZiskFv.AirsClean.Main.bMemMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 5 := by
      rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr]
      change ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 5
      rw [h_m, h_i, h_reg]; norm_num
    exact no_balanced_message_with_constant_nonzero_mult h_balanced (m := -3) (by decide)
      (main_bMem_interaction_mem_witness h_table h_component h_row)
      (main_bMem_mult_of_mem_op_five b_mem b_ind b_reg h_op)
      (fun i h_i' h_msg _ =>
        memBus_mult_eq_neg_three_of_msg_eq_bMem_mem_op_five h_constraints h_specs h_table
          h_component h_row h_op h_i' h_msg)

set_option maxHeartbeats 1000000 in
/-- **A store-side register write is not also a memory or indirect store.** -/
theorem main_store_mem_and_ind_zero_of_store_reg
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (h_reg : (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 1) :
    (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem = 0
      ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind = 0 := by
  obtain ⟨-, -, -, -, -, c_mem, c_ind, c_reg⟩ :=
    main_source_flags_boolean h_component (h_constraints table h_table) h_row
  rcases zero_or_one_of_bool c_mem with h_m | h_m <;>
    rcases zero_or_one_of_bool c_ind with h_i | h_i
  · exact ⟨h_m, h_i⟩
  · exfalso
    have h_op : (eval (table.environment row)
        (ZiskFv.AirsClean.Main.cMemMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 5 := by
      rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr]
      change 2 * ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 5
      rw [h_m, h_i, h_reg]; norm_num
    exact no_balanced_message_with_constant_nonzero_mult h_balanced (m := -2) (by decide)
      (main_cMem_interaction_mem_witness h_table h_component h_row)
      (main_cMem_mult_of_mem_op_five c_mem c_ind c_reg h_op)
      (fun i h_i' h_msg _ =>
        memBus_mult_eq_neg_two_of_msg_eq_cMem_mem_op_five h_constraints h_specs h_table
          h_component h_row h_op h_i' h_msg)
  · exfalso
    have h_op : (eval (table.environment row)
        (ZiskFv.AirsClean.Main.cMemMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 5 := by
      rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr]
      change 2 * ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 5
      rw [h_m, h_i, h_reg]; norm_num
    exact no_balanced_message_with_constant_nonzero_mult h_balanced (m := -2) (by decide)
      (main_cMem_interaction_mem_witness h_table h_component h_row)
      (main_cMem_mult_of_mem_op_five c_mem c_ind c_reg h_op)
      (fun i h_i' h_msg _ =>
        memBus_mult_eq_neg_two_of_msg_eq_cMem_mem_op_five h_constraints h_specs h_table
          h_component h_row h_op h_i' h_msg)
  · exact absurd (main_not_store_mem_and_store_ind_and_store_reg h_balanced h_constraints h_specs
      h_table h_component h_row h_m h_i h_reg) (by simp)

end ZiskFv.Compliance
