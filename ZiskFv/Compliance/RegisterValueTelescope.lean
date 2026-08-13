import ZiskFv.Compliance.RegisterBoundaryAnchor

/-!
# The backward walk: carrying a register value back to `bootMessage`

#342 established the **forward** walk. From a register read, `exists_push_of_pull` finds the
register-pre push that answers it, and that push belongs to a row whose own access is strictly
later; iterating reaches the `RegisterBoundary` reload.

Ordering is not agreement. #330 Phase 4 needs the **value**, and for that the walk has to run the
other way: from a row's register-pre push, find the *pull* it answers. That pull is an earlier read,
or `bootMessage`'s literal `(timestamp 0, value 0)`. Following it back and carrying the message
equality at each step is what turns "the operand column holds some value" into "the operand column
holds the value the register was last written with".

Clean gives `exists_push_of_pull` but no converse. `balanceOf` is symmetric in the sign, so the
converse is the same argument at `mult = 1`, and
`no_balanced_message_with_constant_nonzero_mult` already packages the arithmetic.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.Main (componentWithRomMemAndOpBus)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep)

/-- **The converse of `exists_push_of_pull`, on the memory bus.**

    A push must be answered too: an interaction riding at `+1` forces another interaction with the
    same message whose multiplicity is neither `0` nor `1`. Clean states only the pull direction;
    `balanceOf` is sign-symmetric, so this is the same count argument at `m = 1`. -/
theorem exists_pull_of_push_memBus
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    {a : Interaction FGL} (h_a : a ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_push : a.mult = 1) :
    ∃ b ∈ witness.interactionsWith MemBusChannel.toRaw,
      b.msg = a.msg ∧ b.mult ≠ 0 ∧ b.mult ≠ 1 := by
  by_contra! h_none
  exact no_balanced_message_with_constant_nonzero_mult h_balanced (m := 1) one_ne_zero h_a h_push
    (fun i h_i h_msg h_ne => h_none i h_i h_msg h_ne)


/-! ## What answers a register-pre push

At `mem_op = 3` the memory bus carries six shapes: Main's three current accesses (pulls), Main's
three register-pre pushes, and the `RegisterBoundary` boot pull and reload push. A counterpart with
`mult ∉ {0, 1}` can only be one of the two pulls.

The `mult ≠ 0` clause is not decoration. A register-pre push on an **inactive** slot rides at
multiplicity `0` — it is a phantom emission that carries a message but contributes nothing to the
balance — and idle slots are everywhere in the witnesses. `mult ≠ 0` is what stops such a phantom
from answering a read, exactly as `mult ≠ -1` stopped the boot pull in the forward direction. -/

/-- Main's register-pre push rides at its own selector, which booleanity pins to `0` or `1`. -/
theorem main_regPre_mult_zero_or_one
    {length : ℕ} {program : Program length}
    {table : Table FGL} {row : Array FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    (h_constraints : table.Constraints) (h_row : row ∈ table.table) (s : RegSlot) :
    (((MemBusChannel.emitted (s.selectorExpr (componentWithRomMemAndOpBus length program).rowInputVar) (s.regPreMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row)).mult = 0
    ∨ (((MemBusChannel.emitted (s.selectorExpr (componentWithRomMemAndOpBus length program).rowInputVar) (s.regPreMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row)).mult = 1 := by
  obtain ⟨b_a_mem, b_a_reg, b_b_mem, b_b_ind, b_b_reg, b_c_mem, b_c_ind, b_c_reg⟩ :=
    main_source_flags_boolean h_component h_constraints h_row
  obtain ⟨e_a_mem, e_a_reg, e_b_mem, e_b_ind, e_b_reg, e_c_mem, e_c_ind, e_c_reg⟩ :=
    main_rom_eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar
  rw [memBus_emitted_eval_mult]
  cases s
  · rw [RegSlot.selectorExpr, e_a_reg]; exact zero_or_one_of_bool b_a_reg
  · rw [RegSlot.selectorExpr, e_b_reg]; exact zero_or_one_of_bool b_b_reg
  · rw [RegSlot.selectorExpr, e_c_reg]; exact zero_or_one_of_bool b_c_reg

end ZiskFv.Compliance
