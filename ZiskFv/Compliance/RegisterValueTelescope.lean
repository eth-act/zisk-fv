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


/-- A slot's register-pre push really is one of the witness's memory-bus interactions. -/
theorem regSlot_regPre_interaction_mem_witness
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot) :
    (((MemBusChannel.emitted (s.selectorExpr (componentWithRomMemAndOpBus length program).rowInputVar) (s.regPreMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row)) ∈ witness.interactionsWith MemBusChannel.toRaw := by
  rw [EnsembleWitness.mem_interactionsWith]
  refine ⟨table, h_table, ?_⟩
  rw [Table.interactionsWith]
  refine List.mem_flatMap.mpr ⟨row, h_row, ?_⟩
  rw [Operations.interactionValuesWith_eq_map, h_component,
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_memBus]
  cases s <;> simp [RegSlot.selectorExpr, RegSlot.regPreMessageExpr]

/-- An active slot's register-pre push rides at `+1`. -/
theorem regSlot_regPre_mult_one
    {length : ℕ} {program : Program length}
    {table : Table FGL} {row : Array FGL}
    (s : RegSlot) (h_sel : s.selector (eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar) = 1) :
    (((MemBusChannel.emitted (s.selectorExpr (componentWithRomMemAndOpBus length program).rowInputVar) (s.regPreMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row)).mult = 1 := by
  obtain ⟨-, e_a_reg, -, -, e_b_reg, -, -, e_c_reg⟩ :=
    main_rom_eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar
  rw [memBus_emitted_eval_mult]
  cases s
  · rw [RegSlot.selectorExpr, e_a_reg]; exact h_sel
  · rw [RegSlot.selectorExpr, e_b_reg]; exact h_sel
  · rw [RegSlot.selectorExpr, e_c_reg]; exact h_sel

/-- **One backward step.** An active slot's register-pre push is answered either by
    `bootMessage` — which pins that slot's predecessor timestamp *and its operand values* to `0` —
    or by an earlier register read, whose own slot is active and whose read timestamp is the
    predecessor timestamp, hence **strictly below** this row's own access.

    The strict decrease is the bus-102 descent, so the measure that terminates the backward walk is
    the read timestamp itself. -/
theorem backward_step
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1) :
    (∃ btbl ∈ trace.witness.allTables,
        ∃ _h : btbl.component = ZiskFv.AirsClean.RegisterBoundary.component,
          ∃ br ∈ btbl.table,
            s.regPreMessage (eval (table.environment row)
                (componentWithRomMemAndOpBus trace.programLength
                  trace.program).rowInputVar)
              = ZiskFv.AirsClean.RegisterBoundary.bootMessage
                (eval (btbl.environment br)
                  ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar))
      ∨ (∃ tbl ∈ trace.witness.allTables,
          ∃ _h : tbl.component =
              componentWithRomMemAndOpBus trace.programLength trace.program,
            ∃ r ∈ tbl.table, ∃ t : RegSlot,
              t.selector (eval (tbl.environment r)
                  (componentWithRomMemAndOpBus trace.programLength
                    trace.program).rowInputVar) = 1
              ∧ t.readMessage (eval (tbl.environment r)
                  (componentWithRomMemAndOpBus trace.programLength
                    trace.program).rowInputVar)
                = s.regPreMessage (eval (table.environment row)
                  (componentWithRomMemAndOpBus trace.programLength
                    trace.program).rowInputVar)) := by
  have h_mem := regSlot_regPre_interaction_mem_witness h_table h_component h_row s
  have h_mult := regSlot_regPre_mult_one (table := table) (row := row) s h_sel
  obtain ⟨b, h_b, h_bmsg, h_b0, h_b1⟩ :=
    exists_pull_of_push_memBus trace.channels_balanced h_mem h_mult
  have h_ref_op : (eval (table.environment row) (s.regPreMessageExpr
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).mem_op = 3 :=
    RegSlot.eval_regPreMessageExpr_mem_op s _ _
  rcases memBus_mem_op_three_counterpart trace.constraints_hold trace.spec_holds h_ref_op h_b
      h_bmsg h_b0 h_b1 with
    ⟨tbl, h_tbl, h_comp, r, h_r, t, h_eval⟩ | ⟨btbl, h_btbl, h_bcomp, br, h_br, h_eval⟩
  · refine Or.inr ⟨tbl, h_tbl, h_comp, r, h_r, t, ?_, ?_⟩
    · refine regSlot_selector_of_mem_op_three h_comp (trace.constraints_hold tbl h_tbl) h_r t ?_
      have h_raw :
          (((MemBusChannel.emitted (t.memMult
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
            (t.memMessageExpr
              (componentWithRomMemAndOpBus trace.programLength
                trace.program).rowInputVar)).toRaw).eval (tbl.environment r)).msg
          = (((MemBusChannel.emitted (s.selectorExpr
              (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
              (s.regPreMessageExpr
                (componentWithRomMemAndOpBus trace.programLength
                  trace.program).rowInputVar)).toRaw).eval (table.environment row)).msg := by
        rw [← h_eval]; exact h_bmsg
      rw [memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)]
      exact h_ref_op
    · have h_raw :
          (((MemBusChannel.emitted (t.memMult
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
            (t.memMessageExpr
              (componentWithRomMemAndOpBus trace.programLength
                trace.program).rowInputVar)).toRaw).eval (tbl.environment r)).msg
          = (((MemBusChannel.emitted (s.selectorExpr
              (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
              (s.regPreMessageExpr
                (componentWithRomMemAndOpBus trace.programLength
                  trace.program).rowInputVar)).toRaw).eval (table.environment row)).msg := by
        rw [← h_eval]; exact h_bmsg
      have h_full := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
      rwa [RegSlot.eval_memMessageExpr, RegSlot.eval_regPreMessageExpr] at h_full
  · refine Or.inl ⟨btbl, h_btbl, h_bcomp, br, h_br, ?_⟩
    have h_raw :
        (((MemBusChannel.emitted (-1)
          (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
          (btbl.environment br)).msg
        = (((MemBusChannel.emitted (s.selectorExpr
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
            (s.regPreMessageExpr
              (componentWithRomMemAndOpBus trace.programLength
                trace.program).rowInputVar)).toRaw).eval (table.environment row)).msg := by
      rw [← h_eval]; exact h_bmsg
    have h_full := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_bootMessageExpr,
      RegSlot.eval_regPreMessageExpr] at h_full
    exact h_full.symm


/-- **The backward step strictly decreases the read timestamp.**

    The predecessor column is a free witness column, so nothing bounds it *a priori* — the bound
    arrives with the step. Once the answering read is identified, its own timestamp is `k + 4 * index`
    and so below `2 ^ 40`, and the bus-102 descent then puts it strictly below this row's access.
    That is the measure the backward walk terminates on. -/
theorem backward_step_lt
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1)
    {tbl : Table FGL} (h_tbl : tbl ∈ trace.witness.allTables)
    (h_comp : tbl.component = componentWithRomMemAndOpBus trace.programLength trace.program)
    {r : Array FGL} (h_r : r ∈ tbl.table) (t : RegSlot)
    (h_eq : t.readMessage (eval (tbl.environment r) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
      = s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)) :
    (t.readTimestamp (eval (tbl.environment r) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val
      < (s.readTimestamp (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val := by
  have h_ts : t.readTimestamp (eval (tbl.environment r) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
      = s.prevStep (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) := by
    have := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_eq
    rwa [RegSlot.readMessage_timestamp, RegSlot.regPreMessage_timestamp] at this
  have h_bound : (s.prevStep (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val < 2 ^ 40 := by
    rw [← h_ts]
    exact regSlot_timestamp_bound_of_mem h_comp h_r t
  have h_descent :
      ZiskFv.AirsClean.RangeTables.rangeTable24.Spec
        (s.distance (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)) :=
    ZiskFv.Compliance.Instantiation.rangeTable24_spec_distance_of_active trace.channels_balanced trace.spec_holds
      trace.constraints_hold h_table h_row rfl h_component s h_sel
  rw [h_ts]
  exact ZiskFv.AirsClean.FullEnsemble.prev_val_lt_of_registerStepSpec h_descent h_bound

/-- **The boot branch pins the operand values to zero.** A register-pre message's value lanes are
    the row's *own* operand values, and `bootMessage` carries `(0, 0)`. So a slot whose predecessor
    access is the boot pull reads a register that still holds `0` — the anchor the value telescope
    descends to. -/
theorem regPre_values_zero_of_boot
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} {row : Array FGL} (s : RegSlot)
    {btbl : Table FGL} {br : Array FGL}
    (h_eq : s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
      = ZiskFv.AirsClean.RegisterBoundary.bootMessage
        (eval (btbl.environment br)
          ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)) :
    (s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).value_0 = 0
      ∧ (s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).value_1 = 0
      ∧ s.prevStep (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_eq
  · exact congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_eq
  · have := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_eq
    rwa [RegSlot.regPreMessage_timestamp] at this


/-! ## The backward walk reaches `bootMessage`

Each step moves to an earlier read, and read timestamps are natural numbers, so the descent cannot
continue forever. The measure is the read timestamp itself — decreasing, unlike the forward walk's
`2 ^ 40 - readTimestamp`. -/

/-- A slot of a witness row whose predecessor access is the boot pull, so whose operand values are
    the register's untouched `0`. -/
def BootAnchoredAt {n : Nat} (trace : AcceptedZiskTrace n)
    (table : Table FGL) (row : Array FGL) (s : RegSlot) : Prop :=
  ∃ btbl ∈ trace.witness.allTables,
    ∃ _h : btbl.component = ZiskFv.AirsClean.RegisterBoundary.component,
      ∃ br ∈ btbl.table,
        s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)
          = ZiskFv.AirsClean.RegisterBoundary.bootMessage
            (eval (btbl.environment br)
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)

set_option maxHeartbeats 1000000 in
/-- **The backward walk terminates at `bootMessage`.** From any active slot of any witness Main row,
    following register-pre pushes back reaches a slot anchored at the boot pull.

    The measure is the read timestamp, which `backward_step_lt` strictly decreases at every step. -/
theorem exists_bootAnchored_of_fuel
    {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (fuel : ℕ) {table : Table FGL}, table ∈ trace.witness.allTables →
      ∀ (h_component : table.component =
          componentWithRomMemAndOpBus trace.programLength trace.program),
        ∀ {row : Array FGL}, row ∈ table.table → ∀ (s : RegSlot),
          s.selector (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1 →
          (s.readTimestamp (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val ≤ fuel →
          ∃ tbl ∈ trace.witness.allTables,
            ∃ _h : tbl.component =
                componentWithRomMemAndOpBus trace.programLength trace.program,
              ∃ r ∈ tbl.table, ∃ t : RegSlot,
                t.selector (eval (tbl.environment r) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1
                ∧ BootAnchoredAt trace tbl r t := by
  intro fuel
  induction fuel with
  | zero =>
      intro table h_table h_component row h_row s h_sel h_fuel
      exact absurd (readTimestamp_val_pos h_component h_row s) (by omega)
  | succ fuel ih =>
      intro table h_table h_component row h_row s h_sel h_fuel
      rcases backward_step trace h_table h_component h_row s h_sel with
        h_boot | ⟨tbl, h_tbl, h_comp, r, h_r, t, h_tsel, h_eq⟩
      · exact ⟨table, h_table, h_component, row, h_row, s, h_sel, h_boot⟩
      · refine ih h_tbl h_comp h_r t h_tsel ?_
        have h_lt := backward_step_lt trace h_table h_component h_row s h_sel h_tbl h_comp h_r t h_eq
        omega

/-- **Termination, with the measure supplied.** Every active register slot of the witness traces
    back to a slot anchored at `bootMessage`.

    **This is the WEAK corollary — prefer `exists_bootWalk`.** The `tbl / r / t` bound here are
    fresh: the statement says a boot-anchored slot *exists*, not that the slot you started from is
    the one traced back, and it carries no value. It stands in the same relation to
    `exists_bootWalk` as `exists_boundarySuppliedSite` does to `exists_boundaryWalk`. -/
theorem exists_bootAnchored
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table) (s : RegSlot)
    (h_sel : s.selector (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1) :
    ∃ tbl ∈ trace.witness.allTables,
      ∃ _h : tbl.component =
          componentWithRomMemAndOpBus trace.programLength trace.program,
        ∃ r ∈ tbl.table, ∃ t : RegSlot,
          t.selector (eval (tbl.environment r) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1
          ∧ BootAnchoredAt trace tbl r t :=
  exists_bootAnchored_of_fuel trace
    (s.readTimestamp (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val
    h_table h_component h_row s h_sel (by omega)

/-- **The anchor, as a predicate on a walk step.** Same content as `BootAnchoredAt`, phrased on the
    evaluated `RegWalkStep` so a path can end in it. -/
def BootAnchoredStep {n : Nat} (trace : AcceptedZiskTrace n) (p : RegWalkStep) : Prop :=
  ∃ btbl ∈ trace.witness.allTables,
    ∃ _h : btbl.component = ZiskFv.AirsClean.RegisterBoundary.component,
      ∃ br ∈ btbl.table,
        p.2.regPreMessage p.1
          = ZiskFv.AirsClean.RegisterBoundary.bootMessage
            (eval (btbl.environment br)
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)

theorem bootAnchoredStep_iff {n : Nat} (trace : AcceptedZiskTrace n)
    (table : Table FGL) (row : Array FGL) (s : RegSlot) :
    BootAnchoredAt trace table row s
      ↔ BootAnchoredStep trace
          (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s) :=
  Iff.rfl

/-- **One backward link, as a relation on walk steps.** `p.AnswersRegPre q` says `q`'s read message
    *is* `p`'s register-pre message.

    This is the relation that carries the **value**: both sides are full `MemBusMessage`s, so the
    equality pins the operand lanes as well as the timestamp. Along an a- or b-side chain the value
    is therefore constant — correct, since reads do not write — and the store side is where it
    steps, because `cRegPreMessage` carries `store_reg_prev_value` while `cMemMessage` carries the
    new one. -/
def RegWalkStep.AnswersRegPre (p q : RegWalkStep) : Prop :=
  q.2.readMessage q.1 = p.2.regPreMessage p.1

/-- **The backward walk, recording its path.** From any active slot of any witness Main row,
    following register-pre pushes back produces a finite path whose head is *that* slot, whose
    every element is an active witness row, whose consecutive steps are linked by
    `AnswersRegPre`, and whose last step is anchored at `bootMessage`.

    This is the backward analogue of `exists_boundaryWalk`, and it exists for the same reason #349
    added the path there: `exists_bootAnchored` produces a boot-anchored slot *somewhere*, with no
    stated relation to the slot the walk started from, which is not enough to carry a value.

    The measure is the read timestamp, which `backward_step_lt` strictly decreases. -/
theorem exists_bootWalk_of_fuel
    {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (fuel : ℕ) {table : Table FGL}, table ∈ trace.witness.allTables →
      ∀ (h_component : table.component =
          componentWithRomMemAndOpBus trace.programLength trace.program),
        ∀ {row : Array FGL}, row ∈ table.table → ∀ (s : RegSlot),
          s.selector (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1 →
          (s.readTimestamp (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val
              ≤ fuel →
          ∃ path : List RegWalkStep, ∃ last : RegWalkStep,
            path.head? = some
                (eval (table.environment row)
                  (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)
              ∧ path.getLast? = some last
              ∧ (∀ q ∈ path, IsActiveWitnessMainRow trace q)
              ∧ List.IsChain RegWalkStep.AnswersRegPre path
              ∧ BootAnchoredStep trace last := by
  intro fuel
  induction fuel with
  | zero =>
      intro table h_table h_component row h_row s h_sel _h_fuel
      exact absurd (readTimestamp_val_pos h_component h_row s) (by omega)
  | succ fuel ih =>
      intro table h_table h_component row h_row s h_sel h_fuel
      have h_start := isActiveWitnessMainRow_of_mem trace h_table h_component h_row s h_sel
      rcases backward_step trace h_table h_component h_row s h_sel with
        h_boot | ⟨tbl, h_tbl, h_comp, r, h_r, t, h_tsel, h_eq⟩
      · exact ⟨[(eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)],
          _, rfl, rfl,
          (by intro p hp; rw [List.mem_singleton] at hp; exact hp ▸ h_start),
          List.isChain_singleton _, h_boot⟩
      · have h_lt := backward_step_lt trace h_table h_component h_row s h_sel h_tbl h_comp h_r t h_eq
        obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_bd⟩ :=
          ih h_tbl h_comp h_r t h_tsel (by omega)
        match path, h_head with
        | a :: rest, h_head =>
            have h_a : a = (eval (tbl.environment r)
                (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, t) := by
              simpa using h_head
            refine ⟨(eval (table.environment row)
                (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar, s)
                  :: a :: rest,
              last, rfl, by simpa using h_last, ?_, ?_, h_bd⟩
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact h_start
              · exact h_sites p hp
            · refine List.isChain_cons_cons.mpr ⟨?_, h_chain⟩
              show a.2.readMessage a.1 = _
              rw [h_a]
              exact h_eq

/-- **The backward walk, with the measure supplied.** Every active register slot of the witness
    starts a path that ends anchored at `bootMessage`. -/
theorem exists_bootWalk
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
        ∧ List.IsChain RegWalkStep.AnswersRegPre path
        ∧ BootAnchoredStep trace last :=
  exists_bootWalk_of_fuel trace
    (s.readTimestamp (eval (table.environment row)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).val
    h_table h_component h_row s h_sel (by omega)

/-! ## S1 — the anchor pins the operand COLUMN, not just the message

`aRegPreMessage.value_0` is *definitionally* `row.core.a_0` (`AirsClean/Main/Bridge.lean:200`), and
likewise for `a_1` / the b-slot. So a boot-anchored slot does not merely carry a zero in its message:
the Main row's operand column itself is `0`. That is the first statement in this development that
constrains a column an `Inputs_<op>` field talks about, which is why the Phase 4 slice starts here.

The c-slot is deliberately absent. `cRegPreMessage.value_0` is `store_reg_prev_value_0`, a *different*
column from `cMemMessage`'s write value — that asymmetry is exactly where a write happens, and it is
why the chain's value steps at c-links and is constant at a- and b-links. -/

/-- **A boot-anchored a-slot reads a register that still holds `0`, in the `a_0` / `a_1` columns.** -/
theorem a_columns_zero_of_bootAnchoredStep
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h_slot : p.2 = RegSlot.a) (h : BootAnchoredStep trace p) :
    p.1.core.a_0 = 0 ∧ p.1.core.a_1 = 0 := by
  obtain ⟨row, slot⟩ := p
  subst h_slot
  obtain ⟨btbl, _h_btbl, _h_bcomp, br, _h_br, h_eq⟩ := h
  exact ⟨congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_eq,
    congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_eq⟩

/-- **A boot-anchored b-slot reads a register that still holds `0`, in the `b_0` / `b_1` columns.** -/
theorem b_columns_zero_of_bootAnchoredStep
    {n : Nat} (trace : AcceptedZiskTrace n) {p : RegWalkStep}
    (h_slot : p.2 = RegSlot.b) (h : BootAnchoredStep trace p) :
    p.1.core.b_0 = 0 ∧ p.1.core.b_1 = 0 := by
  obtain ⟨row, slot⟩ := p
  subst h_slot
  obtain ⟨btbl, _h_btbl, _h_bcomp, br, _h_br, h_eq⟩ := h
  exact ⟨congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_eq,
    congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_eq⟩

/-- **The anchor, unpacked.** A boot-anchored slot's operand values are `0` and its predecessor
    timestamp is `0`: the register is untouched. -/
theorem bootAnchored_values_zero
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} {row : Array FGL} {s : RegSlot}
    (h : BootAnchoredAt trace table row s) :
    (s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).value_0 = 0
      ∧ (s.regPreMessage (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).value_1 = 0
      ∧ s.prevStep (eval (table.environment row) (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 0 := by
  obtain ⟨btbl, h_btbl, h_bcomp, br, h_br, h_eq⟩ := h
  exact regPre_values_zero_of_boot trace s h_eq

/-! ## S1 — the value the walk carries

A link `p.AnswersRegPre q` is a full `MemBusMessage` equality, so it pins `p`'s pushed value to
`q`'s read value. What happens to that value next is decided by `q`'s slot, and the two cases are
genuinely different:

* an a- or b-slot **reads**. `aMemMessage` and `aRegPreMessage` carry the *same* operand columns
  (`Main/Bridge.lean:165,195`), so what `q` pulls is what `q` pushes and the value passes straight
  through to the next link.
* a c-slot **writes**. `cMemMessage.value_0` is the store value, while `cRegPreMessage.value_0` is
  `store_reg_prev_value_0` (`Main/Bridge.lean:184,213`) — two different columns. The carried value
  stops there, holding exactly what that row wrote.

So the head of a boot-anchored walk holds either `0`, when no c-link occurs on the path and the
register is still untouched, or the value written at the walk's first c-link. That disjunction is
the ZisK half of the a-slot low-lane input field: it says the operand column holds the register's
current contents, expressed as "the last write, or the boot value". -/

/-- **Reading does not change the register.** A read slot's two messages carry the same operand
    lanes. Deliberately false for `.c`: that asymmetry is where a write happens. -/
theorem readMessage_value_eq_regPre_of_ne_c {s : RegSlot} (h_ne : s ≠ RegSlot.c)
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    (s.readMessage row).value_0 = (s.regPreMessage row).value_0
      ∧ (s.readMessage row).value_1 = (s.regPreMessage row).value_1 := by
  cases s
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl h_ne

/-- **The value at the head of a boot-anchored walk.** Either the register was never written and
    the head's pushed value is `0`, or the path contains a c-slot — a write — and the head's pushed
    value is exactly what that row's write message carried.

    The induction is over the path: each non-`c` link passes the value through unchanged, the first
    `c` link stops it, and a path that reaches the anchor without one lands on `bootMessage`'s
    literal zero. -/
theorem bootWalk_head_value {n : Nat} (trace : AcceptedZiskTrace n) :
    ∀ (path : List RegWalkStep) (p last : RegWalkStep),
      path.head? = some p → path.getLast? = some last →
      List.IsChain RegWalkStep.AnswersRegPre path →
      BootAnchoredStep trace last →
      ((p.2.regPreMessage p.1).value_0 = 0 ∧ (p.2.regPreMessage p.1).value_1 = 0)
        ∨ ∃ q ∈ path, q.2 = RegSlot.c
            ∧ (p.2.regPreMessage p.1).value_0 = (q.2.readMessage q.1).value_0
            ∧ (p.2.regPreMessage p.1).value_1 = (q.2.readMessage q.1).value_1 := by
  intro path
  induction path with
  | nil => intro p last h_head; simp at h_head
  | cons a rest ih =>
      intro p last h_head h_last h_chain h_boot
      have h_p : a = p := by simpa using h_head
      subst h_p
      match rest with
      | [] =>
          have h_last' : a = last := by simpa using h_last
          subst h_last'
          obtain ⟨btbl, _h_btbl, _h_bcomp, br, _h_br, h_eq⟩ := h_boot
          exact Or.inl ⟨congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_eq,
            congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_eq⟩
      | b :: rest' =>
          obtain ⟨h_link, h_chain'⟩ := List.isChain_cons_cons.mp h_chain
          have h_link' : b.2.readMessage b.1 = a.2.regPreMessage a.1 := h_link
          by_cases h_c : b.2 = RegSlot.c
          · exact Or.inr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, h_c,
              (congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_link').symm,
              (congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_link').symm⟩
          · obtain ⟨h_v0, h_v1⟩ := readMessage_value_eq_regPre_of_ne_c h_c b.1
            have h_a0 : (a.2.regPreMessage a.1).value_0 = (b.2.regPreMessage b.1).value_0 := by
              rw [← h_v0, ← congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_0 h_link']
            have h_a1 : (a.2.regPreMessage a.1).value_1 = (b.2.regPreMessage b.1).value_1 := by
              rw [← h_v1, ← congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.value_1 h_link']
            rcases ih b last rfl (by simpa using h_last) h_chain' h_boot with
              ⟨h0, h1⟩ | ⟨q, h_q, h_qc, h_q0, h_q1⟩
            · exact Or.inl ⟨h_a0.trans h0, h_a1.trans h1⟩
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ h_q, h_qc,
                h_a0.trans h_q0, h_a1.trans h_q1⟩

/-- **S1, on the a-slot's columns.** From any active a-slot of any witness Main row, the operand
    columns `a_0` / `a_1` hold either `0` or the value written by an active c-slot of a witness Main
    row — the write the walk lands on.

    Both alternatives name real witness rows, which is what makes this usable: the c-branch's `q` is
    an `IsActiveWitnessMainRow`, so a later step can apply the step soundness of *that* row. -/
theorem a_columns_of_bootWalk {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      componentWithRomMemAndOpBus trace.programLength trace.program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (h_sel : RegSlot.a.selector (eval (table.environment row)
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1) :
    (eval (table.environment row)
        (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar).core.a_0 = 0
      ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar).core.a_1 = 0
    ∨ ∃ q : RegWalkStep, IsActiveWitnessMainRow trace q ∧ q.2 = RegSlot.c
        ∧ (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar).core.a_0
          = (ZiskFv.AirsClean.Main.cMemMessage q.1).value_0
        ∧ (eval (table.environment row)
            (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar).core.a_1
          = (ZiskFv.AirsClean.Main.cMemMessage q.1).value_1 := by
  obtain ⟨path, last, h_head, h_last, h_sites, h_chain, h_boot⟩ :=
    exists_bootWalk trace h_table h_component h_row RegSlot.a h_sel
  rcases bootWalk_head_value trace path _ last h_head h_last h_chain h_boot with
    ⟨h0, h1⟩ | ⟨q, h_q, h_qc, h_q0, h_q1⟩
  · exact Or.inl ⟨h0, h1⟩
  · rw [h_qc] at h_q0 h_q1
    exact Or.inr ⟨q, h_sites q h_q, h_qc, h_q0, h_q1⟩

end ZiskFv.Compliance
