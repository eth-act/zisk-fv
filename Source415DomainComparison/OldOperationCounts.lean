import Source415DomainComparison.BalancedCounts
import Source415DomainComparison.MainCapacity
import Source415DomainComparison.OldChannelStreams
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification

/-! Actual old-model row-count cancellation. Every Binary/Extension/Add row
pushes once, every Arith row pushes once and optionally pulls once, and Main
pulls at most once. Existing old OpBus balance counts positions below the field
characteristic, including zero interactions. Cancelling the Arith row count
therefore bounds Binary+Extension rows by the already source-fixed Main domain.
No new accepted-trace bound, provider fullness promise, or source oracle occurs.
-/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel OpBusMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

variable {p : Nat} {program : Program p}

private def positive (interactions : List (Interaction FGL)) : Nat :=
  interactions.countP (fun interaction => decide (interaction.mult = 1))

private def negative (interactions : List (Interaction FGL)) : Nat :=
  interactions.countP (fun interaction => decide (interaction.mult = -1))

private def signed (interactions : List (Interaction FGL)) : Prop :=
  ∀ interaction ∈ interactions,
    interaction.mult = 0 ∨ interaction.mult = 1 ∨ interaction.mult = -1

private theorem signed_append (left right : List (Interaction FGL))
    (hl : signed left) (hr : signed right) : signed (left ++ right) := by
  intro interaction member
  rcases List.mem_append.mp member with member | member
  · exact hl interaction member
  · exact hr interaction member

private theorem positive_append (left right : List (Interaction FGL)) :
    positive (left ++ right) = positive left + positive right := List.countP_append

private theorem negative_append (left right : List (Interaction FGL)) :
    negative (left ++ right) = negative left + negative right := List.countP_append

private theorem flatMap_profiles {α : Type} (rows : List α)
    (emit : α → List (Interaction FGL)) (pushes pulls : Nat)
    (row_profile : ∀ row ∈ rows, signed (emit row) ∧
      positive (emit row) = pushes ∧ negative (emit row) ≤ pulls) :
    signed (rows.flatMap emit) ∧
      positive (rows.flatMap emit) = pushes * rows.length ∧
      negative (rows.flatMap emit) ≤ pulls * rows.length := by
  induction rows with
  | nil => simp [signed, positive, negative]
  | cons row tail ih =>
      have head := row_profile row List.mem_cons_self
      have rest := ih (fun item hi => row_profile item (List.mem_cons_of_mem _ hi))
      refine ⟨?_, ?_, ?_⟩
      · intro interaction hi
        rw [List.flatMap_cons, List.mem_append] at hi
        rcases hi with hi | hi
        · exact head.1 interaction hi
        · exact rest.1 interaction hi
      · rw [List.flatMap_cons, positive_append, head.2.1, rest.2.1, List.length_cons]
        simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      · rw [List.flatMap_cons, negative_append, List.length_cons, Nat.mul_add, Nat.mul_one]
        simpa only [Nat.add_comm] using Nat.add_le_add head.2.2 rest.2.2

private theorem one_push_profile (interaction : Interaction FGL)
    (mult : interaction.mult = 1) :
    signed [interaction] ∧ positive [interaction] = 1 ∧ negative [interaction] ≤ 0 := by
  have hdistinct : (1 : FGL) ≠ -1 := by decide
  simp [signed, positive, negative, mult, hdistinct]

private theorem one_nonpositive_profile (interaction : Interaction FGL)
    (mult : interaction.mult = 0 ∨ interaction.mult = -1) :
    signed [interaction] ∧ positive [interaction] = 0 ∧ negative [interaction] ≤ 1 := by
  have hdistinct : (-1 : FGL) ≠ 1 := by decide
  rcases mult with mult | mult <;> simp [signed, positive, negative, mult, hdistinct]

private theorem primary_optional_pull_profile (primary secondary : Interaction FGL)
    (push : primary.mult = 1) (pull : secondary.mult = 0 ∨ secondary.mult = -1) :
    signed [primary, secondary] ∧ positive [primary, secondary] = 1 ∧
      negative [primary, secondary] ≤ 1 := by
  have hdistinct : (1 : FGL) ≠ -1 := by decide
  have hdistinct' : (-1 : FGL) ≠ 1 := by decide
  rcases pull with pull | pull <;>
    simp [signed, positive, negative, push, pull, hdistinct, hdistinct']

private theorem unit_table_profile (table : Table FGL)
    (message : OpBusMessage (Expression FGL))
    (operations : table.component.operations.interactionsWith OpBusChannel.toRaw =
      [(OpBusChannel.pushed message).toRaw]) :
    signed (table.interactionsWith OpBusChannel.toRaw) ∧
      positive (table.interactionsWith OpBusChannel.toRaw) = table.table.length ∧
      negative (table.interactionsWith OpBusChannel.toRaw) ≤ 0 := by
  have profile := flatMap_profiles table.table
    (fun row => table.component.operations.interactionValuesWith
      OpBusChannel.toRaw (table.environment row)) 1 0 (by
      intro row _
      dsimp only
      rw [Operations.interactionValuesWith_eq_map, operations, List.map_cons, List.map_nil]
      exact one_push_profile _ rfl)
  simpa only [Table.interactionsWith, Nat.one_mul, Nat.zero_mul] using profile

private theorem old_prefix_silent (old : OldWitness p program) (index : Fin 15)
    (before : index.val < 10) :
    (oldTable old index).interactionsWith OpBusChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  intro member
  have named := List.mem_map_of_mem (f := fun channel : RawChannel FGL => channel.name) member
  have absent : OpBusChannel.toRaw.name ∉
      (oldTable old index).component.circuit.channels.map (·.name) := by
    rw [oldTable_component]
    fin_cases index <;> norm_num at before
    · change OpBusChannel.toRaw.name ∉ RegisterBoundary.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ MemAlignReadByte.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ MemAlignByte.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ MemAlign.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ MemAlignRangeSlice.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ MemAlignRomSlice.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ Mem.componentWithDualMemBus.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ RegisterStepRangeSlice.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ SpecifiedRangesSlice.component.circuit.channels.map (·.name)
      decide
    · change OpBusChannel.toRaw.name ∉ ArithDiv.component.circuit.channels.map (·.name)
      decide
  exact absent named

private theorem old_verifier_silent (old : OldWitness p program) :
    old.verifierTable.interactionsWith OpBusChannel.toRaw = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  change OpBusChannel.toRaw ∉ ([] : List (RawChannel FGL))
  simp

/-- The exact old operation stream; zero-valued Main/remainder emissions stay. -/
theorem old_operation_stream (old : OldWitness p program) :
    old.interactionsWith OpBusChannel.toRaw =
      (oldTable old 10).interactionsWith OpBusChannel.toRaw ++
      (oldTable old 11).interactionsWith OpBusChannel.toRaw ++
      (oldTable old 12).interactionsWith OpBusChannel.toRaw ++
      (oldTable old 13).interactionsWith OpBusChannel.toRaw ++
      (oldTable old 14).interactionsWith OpBusChannel.toRaw := by
  change (old.verifierTable :: old.tables).flatMap
    (fun table => table.interactionsWith OpBusChannel.toRaw) = _
  rw [old_tables_eq]
  simp only [commonTables, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
    old_verifier_silent old, old_prefix_silent old 0 (by decide),
    old_prefix_silent old 1 (by decide), old_prefix_silent old 2 (by decide),
    old_prefix_silent old 3 (by decide), old_prefix_silent old 4 (by decide),
    old_prefix_silent old 5 (by decide), old_prefix_silent old 6 (by decide),
    old_prefix_silent old 7 (by decide), old_prefix_silent old 8 (by decide),
    old_prefix_silent old 9 (by decide), List.nil_append, List.append_nil, List.append_assoc]

private theorem old_binary_profile (old : OldWitness p program) :
    signed ((oldTable old 12).interactionsWith OpBusChannel.toRaw) ∧
      positive ((oldTable old 12).interactionsWith OpBusChannel.toRaw) =
        (oldTable old 12).table.length ∧
      negative ((oldTable old 12).interactionsWith OpBusChannel.toRaw) ≤ 0 := by
  apply unit_table_profile _ (Binary.opBusMessageExpr Binary.staticLookupComponent.rowInputVar)
  rw [old_binary_component]
  exact Binary.staticLookupComponent_interactionsWith_opBus

private theorem old_extension_profile (old : OldWitness p program) :
    signed ((oldTable old 11).interactionsWith OpBusChannel.toRaw) ∧
      positive ((oldTable old 11).interactionsWith OpBusChannel.toRaw) =
        (oldTable old 11).table.length ∧
      negative ((oldTable old 11).interactionsWith OpBusChannel.toRaw) ≤ 0 := by
  apply unit_table_profile _
    (BinaryExtension.opBusMessageExpr BinaryExtension.shiftStaticLookupComponent.rowInputVar)
  rw [old_extension_component]
  exact BinaryExtension.shiftStaticLookupComponent_interactionsWith_opBus

private theorem old_add_profile (old : OldWitness p program) :
    signed ((oldTable old 13).interactionsWith OpBusChannel.toRaw) ∧
      positive ((oldTable old 13).interactionsWith OpBusChannel.toRaw) =
        (oldTable old 13).table.length ∧
      negative ((oldTable old 13).interactionsWith OpBusChannel.toRaw) ≤ 0 := by
  apply unit_table_profile _ (BinaryAdd.opBusMessageExpr BinaryAdd.component.rowInputVar)
  rw [oldTable_component]
  exact BinaryAdd.component_interactionsWith_opBus

private theorem old_arith_profile (old : OldWitness p program)
    (constraints : old.Constraints) (balance : old.BalancedChannels) :
    signed ((oldTable old 10).interactionsWith OpBusChannel.toRaw) ∧
      positive ((oldTable old 10).interactionsWith OpBusChannel.toRaw) =
        (oldTable old 10).table.length ∧
      negative ((oldTable old 10).interactionsWith OpBusChannel.toRaw) ≤
        (oldTable old 10).table.length := by
  have component : (oldTable old 10).component = ArithMul.componentComplete :=
    oldTable_component old 10
  have specs := Legacy45.witness_spec_of_constraints old constraints balance
  have profile := flatMap_profiles (oldTable old 10).table
    (fun row => (oldTable old 10).component.operations.interactionValuesWith
      OpBusChannel.toRaw ((oldTable old 10).environment row)) 1 1 (by
      intro row hrow
      have spec := specs _ (oldTable_mem old 10) row hrow
      rw [component, ArithMul.componentComplete_spec] at spec
      have eval_row : eval ((oldTable old 10).environment row)
          ArithMul.componentComplete.rowInputVar =
        ArithMul.componentComplete.rowInput ((oldTable old 10).environment row) := by
        simpa only [Component.rowInput, Component.rowInputVar] using
          (eval_varFromOffset_valueFromOffset ArithMul.componentComplete.Input 0
            ((oldTable old 10).environment row))
      have div_block : ArithMul.SharedDivBlockSpec
          (eval ((oldTable old 10).environment row) ArithMul.componentComplete.rowInputVar) := by
        rw [eval_row]
        exact spec.2
      have div_bool := div_block.1.2.2.2.2.2.2.1
      have zero_bool := div_block.1.2.2.2.2.1
      have div : (eval ((oldTable old 10).environment row)
          ArithMul.componentComplete.rowInputVar).flags.div = 0 ∨
        (eval ((oldTable old 10).environment row)
          ArithMul.componentComplete.rowInputVar).flags.div = 1 := by
        rcases mul_eq_zero.mp div_bool with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h).symm
      have div_zero : (eval ((oldTable old 10).environment row)
          ArithMul.componentComplete.rowInputVar).flags.div_by_zero = 0 ∨
        (eval ((oldTable old 10).environment row)
          ArithMul.componentComplete.rowInputVar).flags.div_by_zero = 1 := by
        rcases mul_eq_zero.mp zero_bool with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h).symm
      have secondary :
          (((OpBusChannel.emitted
            (-(ArithMul.componentComplete.rowInputVar.flags.div *
              (1 - ArithMul.componentComplete.rowInputVar.flags.div_by_zero)))
            (ArithMul.remainderBoundOpBusMessageExpr
              ArithMul.componentComplete.rowInputVar)).toRaw).eval
            ((oldTable old 10).environment row)).mult = 0 ∨
          (((OpBusChannel.emitted
            (-(ArithMul.componentComplete.rowInputVar.flags.div *
              (1 - ArithMul.componentComplete.rowInputVar.flags.div_by_zero)))
            (ArithMul.remainderBoundOpBusMessageExpr
              ArithMul.componentComplete.rowInputVar)).toRaw).eval
            ((oldTable old 10).environment row)).mult = -1 := by
        rw [ArithMul.eval_remainderBoundInteraction_mult]
        rcases div with div | div <;> rcases div_zero with div_zero | div_zero <;>
          simp [div, div_zero]
      dsimp only
      rw [Operations.interactionValuesWith_eq_map, component,
        ArithMul.componentComplete_interactionsWith_opBus, List.map_cons, List.map_cons,
        List.map_nil]
      exact primary_optional_pull_profile _ _ rfl secondary)
  simpa only [Table.interactionsWith, Nat.one_mul] using profile

private theorem old_main_profile (old : OldWitness p program)
    (constraints : old.Constraints) :
    signed ((oldTable old 14).interactionsWith OpBusChannel.toRaw) ∧
      positive ((oldTable old 14).interactionsWith OpBusChannel.toRaw) = 0 ∧
      negative ((oldTable old 14).interactionsWith OpBusChannel.toRaw) ≤
        (oldTable old 14).table.length := by
  have component : (oldTable old 14).component =
      Main.componentWithRomMemAndOpBus p program := oldTable_component old 14
  have operations : (oldTable old 14).component.operations.interactionsWith
      OpBusChannel.toRaw =
      [(OpBusChannel.emitted
        (-(Main.componentWithRomMemAndOpBus p program).rowInputVar.core.is_external_op)
        (Main.opBusMessageExpr
          (Main.componentWithRomMemAndOpBus p program).rowInputVar.core)).toRaw] := by
    rw [component]
    exact Main.componentWithRomMemAndOpBus_interactionsWith_opBus p program
  have profile := flatMap_profiles (oldTable old 14).table
    (fun row => (oldTable old 14).component.operations.interactionValuesWith
      OpBusChannel.toRaw ((oldTable old 14).environment row)) 0 1 (by
      intro row hrow
      let interaction := ((OpBusChannel.emitted
        (-(Main.componentWithRomMemAndOpBus p program).rowInputVar.core.is_external_op)
        (Main.opBusMessageExpr
          (Main.componentWithRomMemAndOpBus p program).rowInputVar.core)).toRaw).eval
            ((oldTable old 14).environment row)
      have member : interaction ∈ (oldTable old 14).interactionsWith OpBusChannel.toRaw := by
        apply List.mem_flatMap.mpr
        refine ⟨row, hrow, ?_⟩
        rw [Operations.interactionValuesWith_eq_map, operations]
        exact List.mem_cons_self
      have nonpositive := (main_table_opBus_mult_neg_one_or_zero_of_constraints
        (constraints _ (oldTable_mem old 14)) component member).symm
      dsimp only
      rw [Operations.interactionValuesWith_eq_map, operations, List.map_cons, List.map_nil]
      exact one_nonpositive_profile interaction nonpositive)
  simpa only [Table.interactionsWith, Nat.zero_mul, Nat.one_mul] using profile

/-- Both families together fit the actual old Main domain. Arith's optional
remainder pull is cancelled against its own unconditional primary push. -/
theorem old_binary_extension_rows_le_main (old : OldWitness p program)
    (constraints : old.Constraints) (balance : old.BalancedChannels) :
    (oldTable old 12).table.length + (oldTable old 11).table.length ≤
      (oldTable old 14).table.length := by
  have arith := old_arith_profile old constraints balance
  have extension := old_extension_profile old
  have binary := old_binary_profile old
  have add := old_add_profile old
  have main := old_main_profile old constraints
  have op_balance : BalancedInteractions (old.interactionsWith OpBusChannel.toRaw) := by
    apply balance OpBusChannel.toRaw
    rw [old_finished_channels]
    simp [oldFinishedChannels]
  have tri : signed (old.interactionsWith OpBusChannel.toRaw) := by
    rw [old_operation_stream]
    exact signed_append _ _
      (signed_append _ _ (signed_append _ _ (signed_append _ _ arith.1 extension.1)
        binary.1) add.1) main.1
  have counts := balanced_positional_counts op_balance tri
  change positive (old.interactionsWith OpBusChannel.toRaw) =
    negative (old.interactionsWith OpBusChannel.toRaw) at counts
  have ext_zero := Nat.eq_zero_of_le_zero extension.2.2
  have binary_zero := Nat.eq_zero_of_le_zero binary.2.2
  have add_zero := Nat.eq_zero_of_le_zero add.2.2
  rw [old_operation_stream] at counts
  simp only [positive_append, negative_append, arith.2.1, extension.2.1,
    binary.2.1, add.2.1, main.2.1, ext_zero, binary_zero, add_zero] at counts
  have arith_bound := arith.2.2
  have main_bound := main.2.2
  omega

/-- Exact zero-inclusive length bound for a real full Binary source completion
with all eight requests per old Binary row; derived from old acceptance only. -/
theorem old_binary_request_count_bound (old : OldWitness p program)
    (constraints : old.Constraints) (balance : old.BalancedChannels) :
    BinaryTable.tableSize + 8 * (oldTable old 12).table.length < ringChar FGL := by
  have rows := old_binary_extension_rows_le_main old constraints balance
  have capacity := old_main_capacity old
  have binary_bound : (oldTable old 12).table.length ≤ Main.mainFixedCapacity := by omega
  rw [ringChar.eq FGL GL_prime]
  exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 8 binary_bound) _)
    binary_source_main_capacity_no_overflow

/-- Same source-derived count bound for the actual full Extension source rows. -/
theorem old_extension_request_count_bound (old : OldWitness p program)
    (constraints : old.Constraints) (balance : old.BalancedChannels) :
    BinaryExtensionTable.tableSize + 8 * (oldTable old 11).table.length < ringChar FGL := by
  have rows := old_binary_extension_rows_le_main old constraints balance
  have capacity := old_main_capacity old
  have extension_bound : (oldTable old 11).table.length ≤ Main.mainFixedCapacity := by omega
  rw [ringChar.eq FGL GL_prime]
  exact lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left 8 extension_bound) _)
    extension_source_main_capacity_no_overflow

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
