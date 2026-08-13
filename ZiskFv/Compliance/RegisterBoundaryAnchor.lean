import ZiskFv.Compliance.MemBusSlotSeparation

/-!
# The register walk lands on the reload, and the reload timestamp is a real read

`exists_boundaryWalk` says a register chain ends at the `RegisterBoundary`. That component emits two
messages, so "ends at the boundary" leaves a question: **which** one?

It is the **reload**, and nothing new is needed to see it. `RegisterBoundary` emits its boot pull at
multiplicity `-1` and its reload push at `+1` (`RegisterBoundary.lean:126-128`), while
`ActiveMainRegisterBoundaryProviderRowMatchSpec` — the shape `exists_push_of_pull` hands back —
carries `mult ≠ -1`. The boot pull is excluded by construction.

The consequence is worth stating on its own: the reload's free `reloadTimestamp` column **equals a
real Main read timestamp**, which is `k + 4 * main_step` for `k ∈ {1, 2, 3}` and therefore never `0`.
So that boundary row cannot self-pair — its boot pull cannot be answered by its own reload push.

**This is per register, not global.** A register that is never read keeps a boundary row whose
reload sits at timestamp `0` and *does* self-pair; `boundaryRowIdle`
(`RegisterMemBusBalance.lean:298`) is exactly that, and `AddFaithfulPaddedWitness` puts thirty of
them in an accepted witness beside a real read on `x1`. Those rows carry no information and nothing
depends on them. The claim here is about the boundary row that answers a read.

## On #348

That issue was opened on the belief that `main.pil:447` is what rules the self-pairing out. **In the
first segment it does not**, which is the case the model is in.

`447` range-checks `last_segment_reg_mem_step - last_reg_mem_step - 1` against
`MAX_RANGE = 2^24 - 1`, and `main_step_to_special_mem_step(step) = 1 + 4 * step + 3`, so
`last_segment_reg_mem_step = 4 * (main_segment + 1) * N` (`main.pil:439`). At `main_segment = 0` and
`N = mainFixedCapacity = 2^22` that is `2^24`, so `reloadTimestamp = 0` makes the checked expression
`2^24 - 1` — equal to `MAX_RANGE` exactly, admitted with **zero margin** rather than comfortably
inside.

At `main_segment ≥ 1` the expression at `reloadTimestamp = 0` is at least `2^25 - 1`, which is
outside `MAX_RANGE`, so `447` *does* exclude `0` in every later segment. The Lean model is
single-segment, so the conclusion above holds where it is used — but the PIL-level statement is
segment-dependent and must not be quoted unqualified.

The exclusion comes from the multiplicity ledger instead — the same place operand-source exclusivity
came from. `447` is still a real unmodelled constraint, and it still buys something (an upper bound
on the reload timestamp, which the backward walk to `bootMessage` will want), but it is not the
anchor.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.Main (componentWithRomMemAndOpBus)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep)

/-- The boot pull rides at `-1`. This is the whole reason it cannot be a counterpart. -/
theorem registerBoundary_boot_eval_mult (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.RegisterBoundary.RegisterBoundaryRow FGL) :
    (((MemBusChannel.emitted (-1)
      (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr row)).toRaw).eval env).mult = -1 := by
  rw [memBus_emitted_eval_mult]
  simp [Expression.eval]

/-- **The walk lands on the reload, never on the boot pull**, and balance equates the reload's
    timestamp with the read's.

    `RegisterBoundary` emits exactly two messages; the counterpart shape carries `mult ≠ -1`, which
    is precisely the boot pull's multiplicity. So the surviving branch is the reload push. -/
theorem boundarySuppliedAt_reload_message
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          ZiskFv.AirsClean.RegisterBoundary.reloadMessage
              (eval (boundaryTable.environment boundaryRow)
                ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)
            = p.2.readMessage p.1 := by
  obtain ⟨table, h_table, h_comp, row, h_row, h_p1, h_sel, h_spec⟩ := h
  obtain ⟨pi, h_pw, h_msg, h_nonpull, h_nonzero, bt, h_bt, h_pi, h_bc⟩ := h_spec
  refine ⟨bt, h_bt, h_bc, ?_⟩
  rcases exists_registerBoundary_mem_row_eval_of_interaction_mem h_bc h_pi with
    ⟨br, h_br, h_eval⟩ | ⟨br, h_br, h_eval⟩
  · exact absurd (by rw [h_eval]; exact registerBoundary_boot_eval_mult _ _) h_nonpull
  · refine ⟨br, h_br, ?_⟩
    have h_raw :
        (((MemBusChannel.emitted 1
          (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
          (bt.environment br)).msg
        = (((MemBusChannel.emitted
            (p.2.memMult
              (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
            (p.2.memMessageExpr
              (componentWithRomMemAndOpBus trace.programLength
                trace.program).rowInputVar)).toRaw).eval (table.environment row)).msg := by
      rw [← h_eval]; exact h_msg
    have h_full := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_reloadMessageExpr,
      RegSlot.eval_memMessageExpr] at h_full
    rw [h_p1]
    exact h_full

/-- The reload's timestamp is the read's timestamp — the projection the walk uses. -/
theorem boundarySuppliedAt_reload_timestamp
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          (eval (boundaryTable.environment boundaryRow)
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadTimestamp
            = p.2.readTimestamp p.1 := by
  obtain ⟨bt, h_bt, h_bc, br, h_br, h_msg⟩ := boundarySuppliedAt_reload_message trace h
  refine ⟨bt, h_bt, h_bc, br, h_br, ?_⟩
  have h := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_msg
  rw [RegSlot.readMessage_timestamp] at h
  exact h

/-- **The reload carries the read's values.** Ordering is not agreement, and this is the half that
    is about agreement: balance equates the whole message, so the boundary row's `reloadValue`
    columns are the values the register read returned. #330 Phase 4's value telescope consumes this;
    it is one projection away from the message equality and should not be re-derived there. -/
theorem boundarySuppliedAt_reload_values
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          (eval (boundaryTable.environment boundaryRow)
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadValue_0
              = (p.2.readMessage p.1).value_0
            ∧ (eval (boundaryTable.environment boundaryRow)
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadValue_1
              = (p.2.readMessage p.1).value_1 := by
  obtain ⟨bt, h_bt, h_bc, br, h_br, h_msg⟩ := boundarySuppliedAt_reload_message trace h
  exact ⟨bt, h_bt, h_bc, br, h_br,
    congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_msg,
    congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_msg⟩

/-- Every Main register read happens at a **positive** timestamp: the slot offsets are `1`, `2`, `3`
and `main_step` is the row index, so the read timestamp is `k + 4 * index` with `k ≥ 1`, below
`2 ^ 24` and never `0`. -/
theorem readTimestamp_val_pos
    {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot) :
    0 < (s.readTimestamp (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar)).val := by
  obtain ⟨index, h_index, h_ms⟩ := exists_main_step_index_of_mem h_component h_row
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ 3 → 0 < ((k : FGL) + (index : FGL) * 4).val := by
    intro k hk1 hk3
    rw [slot_timestamp_val hk3 h_index]
    omega
  cases s
  · simpa [RegSlot.readTimestamp, h_ms] using key 1 (by norm_num) (by norm_num)
  · simpa [RegSlot.readTimestamp, h_ms] using key 2 (by norm_num) (by norm_num)
  · simpa [RegSlot.readTimestamp, h_ms] using key 3 (by norm_num) (by norm_num)

/-- **The boundary cannot self-pair.** Its reload timestamp equals a real Main read timestamp, and
    every such timestamp is positive, so the reload push can never answer the boot pull's
    `timestamp = 0` message.

    This is what issue #348 wanted, and it needs no new constraint: it follows from the counterpart's
    `mult ≠ -1` plus the fixed-column schema that puts `main_step` at the row index. -/
theorem boundary_reload_ne_boot
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          (eval (boundaryTable.environment boundaryRow)
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadTimestamp ≠ 0 := by
  obtain ⟨bt, h_bt, h_bc, br, h_br, h_ts⟩ := boundarySuppliedAt_reload_timestamp trace h
  obtain ⟨table, h_table, h_comp, row, h_row, h_p1, h_sel, -⟩ := h
  refine ⟨bt, h_bt, h_bc, br, h_br, ?_⟩
  rw [h_ts, h_p1]
  intro h_zero
  have h_pos := readTimestamp_val_pos h_comp h_row p.2
  rw [h_zero] at h_pos
  simp at h_pos

end ZiskFv.Compliance
