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


/-- **What answers a register-pre push.** Every memory-bus interaction of the witness that carries a
`mem_op = 3` message at a multiplicity outside `{0, 1}` is either a Main *current* access or the
`RegisterBoundary` boot pull.

The exclusions, in the order the case split meets them: ten components emit nothing on this bus;
`MemAlignReadByte`, `MemAlignByte`, `MemAlign` and `Mem` carry `mem_op ∈ {1, 2}`; the boundary reload
rides at `+1`; and Main's three register-pre pushes ride at their own selector, which is `0` or `1`.
That last one is why `mult ≠ 0` matters as much as `mult ≠ 1`. -/
theorem memBus_mem_op_three_counterpart
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {refEnv : Environment FGL} {refMult : Expression FGL}
    {refMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_ref_op : (eval refEnv refMsg).mem_op = 3)
    {j : Interaction FGL} (h_j : j ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_msg : j.msg = (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg)
    (h_ne0 : j.mult ≠ 0) (h_ne1 : j.mult ≠ 1) :
    (∃ tbl ∈ witness.allTables,
        ∃ _h : tbl.component = componentWithRomMemAndOpBus length program,
          ∃ r ∈ tbl.table, ∃ t : RegSlot,
            j = ((MemBusChannel.emitted (t.memMult (componentWithRomMemAndOpBus length program).rowInputVar) (t.memMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
              (tbl.environment r))
      ∨ (∃ btbl ∈ witness.allTables,
          ∃ _h : btbl.component = ZiskFv.AirsClean.RegisterBoundary.component,
            ∃ br ∈ btbl.table,
              j = ((MemBusChannel.emitted (-1)
                (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
                  ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
                (btbl.environment br)) := by
  rw [EnsembleWitness.mem_interactionsWith] at h_j
  obtain ⟨table, h_table, h_mem_table⟩ := h_j
  have h_component_mem :
      table.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  have h_op_of_emitted :
      ∀ {env : Environment FGL} {mm : Expression FGL}
        {msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)},
        j = ((MemBusChannel.emitted mm msg).toRaw).eval env →
          (eval env msg).mem_op = 3 := by
    intro env mm msg h_eval
    have h_raw :
        (((MemBusChannel.emitted mm msg).toRaw).eval env).msg =
          (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg := by
      rw [← h_eval]; exact h_msg
    rw [memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw), h_ref_op]
  have h_op_of_pushed :
      ∀ {env : Environment FGL}
        {msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)},
        j = ((MemBusChannel.pushed msg).toRaw).eval env →
          (eval env msg).mem_op = 3 := by
    intro env msg h_eval
    have h_raw :
        (((MemBusChannel.pushed msg).toRaw).eval env).msg =
          (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg := by
      rw [← h_eval]; exact h_msg
    rw [memBusMessage_mem_op_eq_of_eval_pushed_provider_msg_eq (h_msg := h_raw), h_ref_op]
  have h_op_of_pulled :
      ∀ {env : Environment FGL}
        {msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)},
        j = ((MemBusChannel.pulled msg).toRaw).eval env →
          (eval env msg).mem_op = 3 := by
    intro env msg h_eval
    have h_raw :
        (((MemBusChannel.pulled msg).toRaw).eval env).msg =
          (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg := by
      rw [← h_eval]; exact h_msg
    rw [memBusMessage_mem_op_eq_of_eval_pulled_provider_msg_eq (h_msg := h_raw), h_ref_op]
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_regBoundary | h_marb | h_mab | h_memAlign | h_memAlignRange | h_memAlignRom |
    h_mem | h_ranges | h_regRange | h_arithDiv | h_arithMul | h_binExt | h_binary | h_binaryAdd |
    h_main
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith MemBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_memBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  -- RegisterBoundary: boot survives, reload rides at `+1`.
  · rcases exists_registerBoundary_mem_row_eval_of_interaction_mem h_regBoundary h_mem_table with
      ⟨br, h_br, h_eval⟩ | ⟨br, h_br, h_eval⟩
    · exact Or.inr ⟨table, h_table, h_regBoundary, br, h_br, h_eval⟩
    · exact absurd (by rw [h_eval, memBus_emitted_eval_mult]; simp [Expression.eval]) h_ne1
  -- MemAlignReadByte carries `1`.
  · exfalso
    rcases exists_memBus_row_eval_of_pair_interactionsWith
        (by simpa [h_marb] using
          ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus)
        h_mem_table with ⟨r, h_r, h_eval⟩ | ⟨r, h_r, h_eval⟩
    · have h_op := h_op_of_pulled h_eval
      rw [memBusMessage_eval_mem_op] at h_op
      have h_lit : (1 : FGL) = 3 := by
        simpa [ZiskFv.AirsClean.MemAlignReadByte.memReadMessageExpr, Expression.eval] using h_op
      exact absurd h_lit (by decide)
    · have h_op := h_op_of_pushed h_eval
      rw [ZiskFv.AirsClean.MemAlignReadByte.eval_memBusMessageExpr] at h_op
      have h_lit : (1 : FGL) = 3 := by
        simpa [ZiskFv.AirsClean.MemAlignReadByte.memBusMessage] using h_op
      exact absurd h_lit (by decide)
  -- MemAlignByte carries `1` or `1 + is_write`.
  · exfalso
    have h_rowSpec := h_specs table h_table
    rcases exists_memBus_row_eval_of_pair_interactionsWith
        (by simpa [h_mab] using
          ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus)
        h_mem_table with ⟨r, h_r, h_eval⟩ | ⟨r, h_r, h_eval⟩
    · have h_op := h_op_of_pulled h_eval
      rw [memBusMessage_eval_mem_op] at h_op
      have h_lit : (1 : FGL) = 3 := by
        simpa [ZiskFv.AirsClean.MemAlignByte.memReadMessageExpr, Expression.eval] using h_op
      exact absurd h_lit (by decide)
    · have h_spec := h_rowSpec r h_r
      rw [h_mab, ZiskFv.AirsClean.MemAlignByte.component_spec,
        component_rowInput_eq_eval_rowInputVar] at h_spec
      have h_isw := h_spec.2.2.2.2.2.2.2
      have h_op := h_op_of_pushed h_eval
      rw [ZiskFv.AirsClean.MemAlignByte.eval_memBusMessageExpr] at h_op
      change 1 + (eval (table.environment r)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar).is_write = 3 at h_op
      rcases zero_or_one_of_val_lt_two (by simpa using h_isw) with h0 | h1
      · rw [h0] at h_op; exact absurd (by rw [← h_op]; ring : (1 : FGL) = 3) (by decide)
      · rw [h1] at h_op; exact absurd (by rw [← h_op]; norm_num : (2 : FGL) = 3) (by decide)
  -- MemAlign carries `wr + 1`.
  · exfalso
    have h_rowSpec := h_specs table h_table
    obtain ⟨r, h_r, h_eval⟩ :=
      exists_memBus_row_eval_of_singleton_interactionsWith
        (by simpa [h_memAlign] using
          ZiskFv.AirsClean.MemAlign.component_interactionsWith_memBus)
        h_mem_table
    have h_spec := h_rowSpec r h_r
    rw [h_memAlign, ZiskFv.AirsClean.MemAlign.component_spec,
      component_rowInput_eq_eval_rowInputVar] at h_spec
    have h_wr := h_spec.1
    have h_op := h_op_of_emitted h_eval
    rw [ZiskFv.AirsClean.MemAlign.eval_memBusMessageExpr] at h_op
    change (eval (table.environment r)
      ZiskFv.AirsClean.MemAlign.component.rowInputVar).wr + 1 = 3 at h_op
    rcases zero_or_one_of_bool h_wr with h0 | h1
    · rw [h0] at h_op; exact absurd (by rw [← h_op]; ring : (1 : FGL) = 3) (by decide)
    · rw [h1] at h_op; exact absurd (by rw [← h_op]; norm_num : (2 : FGL) = 3) (by decide)
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      memAlignRangeSlice_table_interactionsWith_memBus_nil h_memAlignRange
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      memAlignRomSlice_table_interactionsWith_memBus_nil h_memAlignRom
    simp [h_nil] at h_mem_table
  -- Mem carries `wr + 1` and `1`.
  · exfalso
    have h_rowSpec := h_specs table h_table
    rcases exists_memBus_row_eval_of_pair_interactionsWith
        (by simpa [h_mem] using
          ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus)
        h_mem_table with ⟨r, h_r, h_eval⟩ | ⟨r, h_r, h_eval⟩
    · have h_spec := h_rowSpec r h_r
      rw [h_mem] at h_spec
      have h_rowSpec' := ZiskFv.AirsClean.Mem.spec_of_componentWithDualMemBus_spec _ h_spec
      rw [component_rowInput_eq_eval_rowInputVar] at h_rowSpec'
      have h_wr := h_rowSpec'.2.2.2.2.1
      have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] at h_op
      change (eval (table.environment r)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr + 1 = 3 at h_op
      rcases zero_or_one_of_bool h_wr with h0 | h1
      · rw [h0] at h_op; exact absurd (by rw [← h_op]; ring : (1 : FGL) = 3) (by decide)
      · rw [h1] at h_op; exact absurd (by rw [← h_op]; norm_num : (2 : FGL) = 3) (by decide)
    · have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr] at h_op
      have h_lit : (1 : FGL) = 3 := by
        simpa [ZiskFv.AirsClean.Mem.memBusDualMessage] using h_op
      exact absurd h_lit (by decide)
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      specifiedRangesSlice_table_interactionsWith_memBus_nil h_ranges
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      registerStepRangeSlice_table_interactionsWith_memBus_nil h_regRange
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      arithDiv_table_interactionsWith_memBus_nil h_arithDiv
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      arithMul_table_interactionsWith_memBus_nil h_arithMul
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      staticBinaryExtension_table_interactionsWith_memBus_nil h_binExt
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      staticBinary_table_interactionsWith_memBus_nil h_binary
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      binaryAdd_table_interactionsWith_memBus_nil h_binaryAdd
    simp [h_nil] at h_mem_table
  -- Main: the three register-pre pushes ride at their selector, in `{0, 1}`; the three current
  -- accesses survive.
  · obtain ⟨r, h_r, h_branch⟩ := exists_main_mem_row_eval_of_interaction_mem h_main h_mem_table
    have h_regPre : ∀ t : RegSlot,
        j = ((MemBusChannel.emitted (t.selectorExpr (componentWithRomMemAndOpBus length program).rowInputVar)
          (t.regPreMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval (table.environment r) → False := by
      intro t h_eval
      rcases main_regPre_mult_zero_or_one h_main (h_constraints table h_table) h_r t with h0 | h1
      · exact h_ne0 (by rw [h_eval]; exact h0)
      · exact h_ne1 (by rw [h_eval]; exact h1)
    rcases h_branch with h_eval | h_eval | h_eval | h_eval | h_eval | h_eval
    · exact absurd (h_regPre RegSlot.a h_eval) not_false
    · exact Or.inl ⟨table, h_table, h_main, r, h_r, RegSlot.a, h_eval⟩
    · exact absurd (h_regPre RegSlot.b h_eval) not_false
    · exact Or.inl ⟨table, h_table, h_main, r, h_r, RegSlot.b, h_eval⟩
    · exact absurd (h_regPre RegSlot.c h_eval) not_false
    · exact Or.inl ⟨table, h_table, h_main, r, h_r, RegSlot.c, h_eval⟩


/-! ## The backward step

A register-pre push is answered by an earlier read or by `bootMessage`. When it is a read, that
read's own slot is active — `mem_op = 3` forces it — so the walk can take its register-pre push in
turn, and the timestamp strictly **decreases** because the bus-102 descent puts a row's predecessor
below its own access. -/

/-- A current access at `mem_op = 3` has its register selector set. For the a side that is
`a_src_mem + 3 * a_src_reg = 3` with both flags boolean, which forces `a_src_reg = 1`. -/
theorem regSlot_selector_of_mem_op_three
    {length : ℕ} {program : Program length} {table : Table FGL} {row : Array FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    (h_constraints : table.Constraints) (h_row : row ∈ table.table) (s : RegSlot)
    (h_op : (eval (table.environment row) (s.memMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 3) :
    s.selector (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar) = 1 := by
  obtain ⟨b_a_mem, b_a_reg, b_b_mem, b_b_ind, b_b_reg, b_c_mem, b_c_ind, b_c_reg⟩ :=
    main_source_flags_boolean h_component h_constraints h_row
  cases s
  · rw [RegSlot.memMessageExpr, ZiskFv.AirsClean.Main.eval_aMemMessageExpr] at h_op
    change (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem
      + 3 * (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg = 3 at h_op
    show (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg = 1
    rcases zero_or_one_of_bool b_a_reg with h2 | h2
    · exfalso
      rcases zero_or_one_of_bool b_a_mem with h1 | h1 <;>
        rw [h1, h2] at h_op <;> exact absurd h_op (by decide)
    · exact h2
  · rw [RegSlot.memMessageExpr, ZiskFv.AirsClean.Main.eval_bMemMessageExpr] at h_op
    change ((eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
      + (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind)
      + 3 * (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 3 at h_op
    show (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg = 1
    rcases zero_or_one_of_bool b_b_reg with h3 | h3
    · exfalso
      rcases zero_or_one_of_bool b_b_mem with h1 | h1 <;>
        rcases zero_or_one_of_bool b_b_ind with h2 | h2 <;>
          rw [h1, h2, h3] at h_op <;> exact absurd h_op (by decide)
    · exact h3
  · rw [RegSlot.memMessageExpr, ZiskFv.AirsClean.Main.eval_cMemMessageExpr] at h_op
    change 2 * ((eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem
      + (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind)
      + 3 * (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 3 at h_op
    show (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg = 1
    rcases zero_or_one_of_bool b_c_reg with h3 | h3
    · exfalso
      rcases zero_or_one_of_bool b_c_mem with h1 | h1 <;>
        rcases zero_or_one_of_bool b_c_ind with h2 | h2 <;>
          rw [h1, h2, h3] at h_op <;> exact absurd h_op (by decide)
    · exact h3

end ZiskFv.Compliance
