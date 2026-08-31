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
    {tblRef : Table FGL} (_h_tblRef : tblRef ∈ witness.allTables)
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
    {tblRef : Table FGL} (_h_tblRef : tblRef ∈ witness.allTables)
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


/-! ## Every register access is a pull

The payoff of exclusivity, stated uniformly over the three slots: a row whose slot selector is set
emits that slot's current access at multiplicity exactly `-1` and opcode exactly `3`. That is what
Clean's `exists_push_of_pull` consumes, so the register walk can step from such a row rather than
stopping at it. -/

open ZiskFv.Compliance.Instantiation (RegSlot)

set_option maxHeartbeats 1000000 in
/-- **A register access is a `-1` pull at `mem_op = 3`, on every slot.** -/
theorem regSlot_mem_pull_of_selector
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar) = 1) :
    (((MemBusChannel.emitted
      (s.memMult (componentWithRomMemAndOpBus length program).rowInputVar)
      (s.memMessageExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row)).mult = -1
    ∧ (eval (table.environment row)
        (s.memMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 3 := by
  cases s
  · exact main_aMem_pull_of_a_src_reg h_balanced h_constraints h_specs h_table h_component h_row
      h_sel
  · have h_sel' : (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 1 := h_sel
    obtain ⟨h_m, h_i⟩ := main_b_src_mem_and_ind_zero_of_b_src_reg h_balanced h_constraints h_specs
      h_table h_component h_row h_sel'
    obtain ⟨-, -, e_b_mem, e_b_ind, e_b_reg, -⟩ :=
      main_rom_eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar
    constructor
    · rw [RegSlot.memMult, memBus_emitted_eval_mult]
      have h_eval :
          Expression.eval (table.environment row)
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg))
          = -((eval (table.environment row)
                (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
              + (eval (table.environment row)
                (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind
              + (eval (table.environment row)
                (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg) := by
        simp only [Expression.eval, e_b_mem, e_b_ind, e_b_reg]; ring
      rw [h_eval, h_m, h_i, h_sel']; norm_num
    · rw [RegSlot.memMessageExpr, ZiskFv.AirsClean.Main.eval_bMemMessageExpr]
      change ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 3
      rw [h_m, h_i, h_sel']; norm_num
  · have h_sel' : (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 1 := h_sel
    obtain ⟨h_m, h_i⟩ := main_store_mem_and_ind_zero_of_store_reg h_balanced h_constraints h_specs
      h_table h_component h_row h_sel'
    obtain ⟨-, -, -, -, -, e_c_mem, e_c_ind, e_c_reg⟩ :=
      main_rom_eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar
    constructor
    · rw [RegSlot.memMult, memBus_emitted_eval_mult]
      have h_eval :
          Expression.eval (table.environment row)
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg))
          = -((eval (table.environment row)
                (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem
              + (eval (table.environment row)
                (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind
              + (eval (table.environment row)
                (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg) := by
        simp only [Expression.eval, e_c_mem, e_c_ind, e_c_reg]; ring
      rw [h_eval, h_m, h_i, h_sel']; norm_num
    · rw [RegSlot.memMessageExpr, ZiskFv.AirsClean.Main.eval_cMemMessageExpr]
      change 2 * ((eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem
        + (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind)
        + 3 * (eval (table.environment row)
          (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 3
      rw [h_m, h_i, h_sel']; norm_num


/-! ## One step of the walk, between witness sites -/

open ZiskFv.Compliance.Instantiation (RegSupplies RegWalkStep readTimestamp_lt_of_regSupplies)

/-- A slot's current access really is one of its table's memory-bus interactions. -/
theorem regSlot_mem_interaction_mem_table
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot) :
    (((MemBusChannel.emitted
      (s.memMult (componentWithRomMemAndOpBus length program).rowInputVar)
      (s.memMessageExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row))
      ∈ table.interactionsWith MemBusChannel.toRaw := by
  rw [Table.interactionsWith]
  refine List.mem_flatMap.mpr ⟨row, h_row, ?_⟩
  rw [Operations.interactionValuesWith_eq_map, h_component,
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_memBus]
  cases s <;> simp [RegSlot.memMult, RegSlot.memMessageExpr]

/-- The no-wrap bound for a row given by membership rather than index. -/
theorem regSlot_timestamp_bound_of_mem
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot) :
    (s.readTimestamp (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar)).val < 2 ^ 40 := by
  obtain ⟨index, h_index, h_rowAt⟩ := exists_index_of_mem_mainTable h_component h_row
  rw [h_rowAt]
  exact regSlot_timestamp_bound_of_mainTable h_component h_index s

/-- A walk step whose own register read is answered by the `RegisterBoundary`.

    `ActiveMainRegisterBoundaryProviderRowMatchSpec` ignores its trailing `multiplicity` and `as`
    arguments — both are `_`-bound in its definition — so this predicate passes `0` for each and is
    independent of them. Carrying them here would be two parameters that mean nothing. -/
def BoundarySuppliedAt {n : Nat} (trace : AcceptedZiskTrace n) (p : RegWalkStep) : Prop :=
  ∃ table ∈ trace.witness.allTables,
    ∃ _h_comp : table.component =
        componentWithRomMemAndOpBus trace.programLength trace.program,
      ∃ row ∈ table.table,
        p.1 = eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
        ∧ p.2.selector p.1 = 1
        ∧ ActiveMainRegisterBoundaryProviderRowMatchSpec trace.program trace.witness table row
            (((MemBusChannel.emitted
              (p.2.memMult
                (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
              (p.2.memMessageExpr
                (componentWithRomMemAndOpBus trace.programLength
                  trace.program).rowInputVar)).toRaw).eval (table.environment row))
            (p.2.memMessageExpr
              (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
            0 0

/-- **One step of the register walk, between witness sites.**

    A row whose slot selector is set has its register read supplied either by the
    `RegisterBoundary`, or by another witness site that **supplies** it and whose own read happens
    strictly later. Every input is discharged: the `-1` pull shape from source exclusivity, the
    branch split from `channels_balanced`, the descent from the bus-102 slice, and the no-wrap bound
    from the Main table's fixed-column capacity.

    The supply link is part of the conclusion, not just the timestamp inequality, so iterating this
    step builds a chain rather than an unrelated sequence of sites. -/
theorem site_step
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1) :
    BoundarySuppliedAt trace
        (eval (table.environment row)
          (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)
      ∨ ∃ q : RegWalkStep, IsActiveWitnessMainRow trace q
          ∧ RegWalkStep.SuppliedBy
              (eval (table.environment row)
                (componentWithRomMemAndOpBus trace.programLength
                  trace.program).rowInputVar, s) q
          ∧ (s.readTimestamp (eval (table.environment row)
              (componentWithRomMemAndOpBus trace.programLength
                trace.program).rowInputVar)).val < q.timestamp.val := by
  obtain ⟨h_pull, h_op⟩ := regSlot_mem_pull_of_selector trace.channels_balanced
    trace.constraints_hold trace.spec_holds h_table h_component h_row s h_sel
  rcases registerRead_counterpart_of_witnessTable trace h_table h_row
      (regSlot_mem_interaction_mem_table h_component h_row s) rfl h_pull h_op
      (multiplicity := 0) (as := 0) with h_boundary | ⟨q, h_q, h_ts⟩
  · exact Or.inl ⟨table, h_table, h_component, row, h_row, rfl, h_sel, h_boundary⟩
  · have h_supplies :
        RegSupplies s q.2 (eval (table.environment row)
          (componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar) q.1 := by
      show q.2.prevStep q.1 = s.readTimestamp _
      rw [h_ts, RegSlot.eval_memMessageExpr_timestamp]
    exact Or.inr ⟨q, h_q, h_supplies,
      readTimestamp_lt_of_regSupplies h_supplies
        (regSlot_descent_of_witnessMainRow trace h_q)
        (regSlot_timestamp_bound_of_mem h_component h_row s)⟩


/-! ## Termination: the walk ends at the `RegisterBoundary`

Each supply step strictly increases the read timestamp, and every read timestamp is below `2^40`.
So following the counterparts cannot go on forever: after finitely many steps the counterpart is no
longer another Main row, and the only remaining memory-bus provider at `mem_op = 3` is the
`RegisterBoundary`.

The result records the **path**, not just the fact that some boundary-supplied site exists. A bare
existential would not say that *this* site's read is the one traced back to the boundary, and
transporting a register value along the telescope needs the intermediate steps. -/

set_option maxHeartbeats 1000000 in
/-- **The walk terminates, and here is the walk.** From any witness site, following supply
    counterparts produces a finite chain that starts at that site and ends at a site whose read is
    supplied by the `RegisterBoundary`. Every step of the chain is itself a witness site.

    The measure is `2 ^ 40 - readTimestamp`, which strictly decreases at every step because each
    step moves strictly later in time, and which is well-founded because every read timestamp is
    below `2 ^ 40` — from the Main table's own fixed-column capacity, not from a premise about
    segment length. -/
theorem exists_boundaryWalk_of_fuel
    {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (fuel : ℕ) {table : Table FGL}, table ∈ trace.witness.allTables →
      ∀ (_h_component : table.component =
          componentWithRomMemAndOpBus trace.programLength trace.program),
        ∀ {row : Array FGL}, row ∈ table.table → ∀ (s : RegSlot),
          s.selector (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1 →
          2 ^ 40 - (s.readTimestamp (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength
              trace.program).rowInputVar)).val ≤ fuel →
          ∃ path : List RegWalkStep, ∃ last : RegWalkStep,
            path.head? = some
                (eval (table.environment row)
                  (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)
              ∧ path.getLast? = some last
              ∧ (∀ q ∈ path, IsActiveWitnessMainRow trace q)
              ∧ List.IsChain RegWalkStep.SuppliedBy path
              ∧ BoundarySuppliedAt trace last := by
  intro fuel
  induction fuel with
  | zero =>
      intro table h_table h_component row h_row s h_sel h_fuel
      exact absurd (regSlot_timestamp_bound_of_mem h_component h_row s) (by omega)
  | succ fuel ih =>
      intro table h_table h_component row h_row s h_sel h_fuel
      have h_start := isActiveWitnessMainRow_of_mem trace h_table h_component h_row s h_sel
      rcases site_step trace h_table h_component h_row s h_sel with
        h_boundary | ⟨q, h_q, h_sup, h_lt⟩
      · refine ⟨[(eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)],
          _, rfl, rfl, ?_, List.isChain_singleton _, h_boundary⟩
        intro p hp
        rw [List.mem_singleton] at hp
        exact hp ▸ h_start
      · obtain ⟨tbl, h_tbl, h_comp, index, h_index, h_rowAt, h_active⟩ := h_q
        have h_get : q.1 = eval (tbl.environment (tbl.table.get ⟨index, h_index⟩))
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar := by
          rw [h_rowAt]
          exact mainTableRowAtOrZero_get trace.program tbl ⟨index, h_index⟩
        obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_bd⟩ :=
          ih h_tbl h_comp (List.get_mem tbl.table ⟨index, h_index⟩) q.2
            (by rw [← h_get]; exact h_active)
            (by
              have h_bound := regSlot_timestamp_bound_of_mem h_comp
                (List.get_mem tbl.table ⟨index, h_index⟩) q.2
              rw [← h_get] at h_bound ⊢
              have : q.timestamp.val = (q.2.readTimestamp q.1).val := rfl
              omega)
        have h_q_eq : (eval (tbl.environment (tbl.table.get ⟨index, h_index⟩))
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, q.2)
              = q := by
          rw [← h_get]; rfl
        rw [h_q_eq] at h_head
        match path, h_head with
        | a :: rest, h_head =>
            have h_a : a = q := by simpa using h_head
            subst h_a
            refine ⟨(eval (table.environment row)
                (componentWithRomMemAndOpBus trace.programLength
                  trace.program).rowInputVar, s) :: a :: rest,
              last, rfl, by simpa using h_last, ?_, ?_, h_bd⟩
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact h_start
              · exact h_sites p hp
            · exact List.isChain_cons_cons.mpr ⟨h_sup, h_chain⟩

/-- **Termination, with the measure supplied.** Every witness site starts a chain that ends at the
    boundary. -/
theorem exists_boundaryWalk
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1) :
    ∃ path : List RegWalkStep, ∃ last : RegWalkStep,
      path.head? = some
          (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)
        ∧ path.getLast? = some last
        ∧ (∀ q ∈ path, IsActiveWitnessMainRow trace q)
        ∧ List.IsChain RegWalkStep.SuppliedBy path
        ∧ BoundarySuppliedAt trace last :=
  exists_boundaryWalk_of_fuel trace (2 ^ 40) h_table h_component h_row s h_sel (by omega)

/-- The bare existence statement: *some* witness site is boundary-supplied. This is the weak
    corollary of `exists_boundaryWalk`; prefer the path version, which says that the site you
    started from is the one traced back. -/
theorem exists_boundarySuppliedSite
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1) :
    ∃ p : RegWalkStep, BoundarySuppliedAt trace p := by
  obtain ⟨_, last, _, _, _, _, h_bd⟩ :=
    exists_boundaryWalk trace h_table h_component h_row s h_sel
  exact ⟨last, h_bd⟩

/-- The chain `exists_boundaryWalk` builds is a genuine walk: its read timestamps do not repeat, so
    it never revisits a site's read. This is `regSupplies_chain_timestamps_nodup_of_witnessRows`
    applied to the path, and it is what makes "the walk reaches the boundary" a statement about a
    finite acyclic path rather than about an arbitrary sequence. -/
theorem boundaryWalk_timestamps_nodup
    {n : Nat} (trace : AcceptedZiskTrace n) (path : List RegWalkStep)
    (h_sites : ∀ q ∈ path, IsActiveWitnessMainRow trace q)
    (h_chain : List.IsChain RegWalkStep.SuppliedBy path) :
    (path.map RegWalkStep.timestamp).Nodup :=
  regSupplies_chain_timestamps_nodup_of_witnessRows trace path h_sites h_chain

end ZiskFv.Compliance
