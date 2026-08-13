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

end ZiskFv.Compliance
