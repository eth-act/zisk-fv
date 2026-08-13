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
So the boundary cannot self-pair — its boot pull cannot be answered by its own reload push —
whenever any register read occurs.

## On #348

That issue was opened on the belief that `main.pil:447` is what rules the self-pairing out. It is
not. `447` range-checks `last_segment_reg_mem_step - last_reg_mem_step - 1`, and
`main_step_to_special_mem_step(step) = 1 + 4 * step + 3` makes `last_segment_reg_mem_step = 4 * N`
for a segment of `N` rows. With `N = mainFixedCapacity = 2^22` that is `2^24`, so at
`reloadTimestamp = 0` the checked expression is `2^24 - 1`, which is *inside* `rangeTable24`. `447`
admits `0`.

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
theorem boundarySuppliedAt_reload_timestamp
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h : BoundarySuppliedAt trace p) :
    ∃ boundaryTable ∈ trace.witness.allTables,
      ∃ _h_comp : boundaryTable.component = ZiskFv.AirsClean.RegisterBoundary.component,
        ∃ boundaryRow ∈ boundaryTable.table,
          (eval (boundaryTable.environment boundaryRow)
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar).reloadTimestamp
            = p.2.readTimestamp p.1 := by
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
    have h_ts := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_full
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_reloadMessageExpr,
      RegSlot.eval_memMessageExpr_timestamp] at h_ts
    rw [h_p1]
    exact h_ts


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
  obtain ⟨table, h_table, h_comp, row, h_row, h_p1, h_sel, h_spec⟩ := h
  obtain ⟨bt, h_bt, h_bc, br, h_br, h_ts⟩ :=
    boundarySuppliedAt_reload_timestamp trace
      ⟨table, h_table, h_comp, row, h_row, h_p1, h_sel, h_spec⟩
  refine ⟨bt, h_bt, h_bc, br, h_br, ?_⟩
  rw [h_ts, h_p1]
  intro h_zero
  have h_pos := readTimestamp_val_pos h_comp h_row p.2
  rw [h_zero] at h_pos
  simp at h_pos

end ZiskFv.Compliance
