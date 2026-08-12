import ZiskFv.AirsClean.FullEnsemble.Balance.RegisterChainBridges

/-!
# Main's operand-source flags are exclusive, and balance is what proves it

Main's a-side operand is either a memory read (`a_src_mem`) or a register read (`a_src_reg`). The
component asserts only that each flag is **boolean** (`Main/Constraints.lean:252,259`); nothing in it
says they cannot both be set. Yet the register walk in `ZiskFv/Compliance/RegisterWalk.lean` needs
exactly that: it can only follow a supply step to a row whose own access is a `mem_op = 3` **pull**,
and Clean's `exists_push_of_pull` fires only at multiplicity exactly `-1`, i.e. at
`a_src_mem + a_src_reg = 1`.

This module proves the exclusivity from `BalancedChannels` alone.

The argument is a multiplicity count, not a decode fact:

* `Air.Flat.BalancedInteractions` is **message-exact** — `∀ msg, balanceOf interactions msg = 0`,
  summing multiplicities over interactions carrying that exact message array. It is not a
  challenge-mixed sum, so a single message can be reasoned about on its own.
* A row with both a-side flags set emits its a-side current access with
  `mem_op = a_src_mem + 3 * a_src_reg = 4`.
* **No memory-bus emission in the ensemble carries `mem_op = 4` at a non-negative multiplicity.**
  Main's three register-pre pushes are the only positive ones and they carry the literal `3`; the
  Mem, MemAlign, MemAlignByte and MemAlignReadByte messages carry `1` or `wr + 1` with `wr` boolean;
  `RegisterBoundary` carries the literal `3`. Main's three *current* accesses are all pulls
  (`Main/Constraints.lean:436,441,446`), and at `mem_op = 4` booleanity pins each to `-2`.
* So the balance at that message is `-2 * count` with `count ≥ 1` and `count < GL_prime`, which
  cannot vanish.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.Main (MainRowWithRom componentWithRomMemAndOpBus)

/-! ## Reading a raw memory-bus interaction -/

/-- The multiplicity of an emitted memory-bus interaction is its multiplicity expression,
    evaluated. -/
theorem memBus_emitted_eval_mult
    (env : Environment FGL) (mult : Expression FGL)
    (msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)) :
    (((MemBusChannel.emitted mult msg).toRaw).eval env).mult = Expression.eval env mult :=
  rfl

/-- A boolean column is `0` or `1`. -/
private lemma zero_or_one_of_bool {col : FGL} (h : col * (1 - col) = 0) : col = 0 ∨ col = 1 := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ?_
    have : col - 1 = 0 := by
      have hneg := congrArg Neg.neg h1
      simpa [sub_eq_add_neg] using hneg
    linear_combination this

/-- A field element whose `val` is below `2` is `0` or `1`. -/
private lemma zero_or_one_of_val_lt_two {x : FGL} (h : x.val < 2) : x = 0 ∨ x = 1 := by
  interval_cases h_val : x.val
  · exact Or.inl (by apply Fin.ext; simp [h_val])
  · exact Or.inr (by apply Fin.ext; simp [h_val])

/-- Push `Expression.eval` through a Main row variable's ROM projections. -/
private lemma main_rom_eval
    (env : Environment FGL) (row : Var MainRowWithRom FGL) :
    Expression.eval env row.rom.a_src_mem = (eval env row).rom.a_src_mem
  ∧ Expression.eval env row.rom.a_src_reg = (eval env row).rom.a_src_reg
  ∧ Expression.eval env row.rom.b_src_mem = (eval env row).rom.b_src_mem
  ∧ Expression.eval env row.rom.b_src_ind = (eval env row).rom.b_src_ind
  ∧ Expression.eval env row.rom.b_src_reg = (eval env row).rom.b_src_reg
  ∧ Expression.eval env row.rom.store_mem = (eval env row).rom.store_mem
  ∧ Expression.eval env row.rom.store_ind = (eval env row).rom.store_ind
  ∧ Expression.eval env row.rom.store_reg = (eval env row).rom.store_reg := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field, Expression.eval]

/-! ## Main's three current accesses, at `mem_op = 4`

Each is a pull whose multiplicity is the negated selector sum, and at `mem_op = 4` booleanity leaves
exactly one assignment of the selectors — one that pins the multiplicity to `-2`. -/

/-- The a-side current access rides at `-2` when its `mem_op` is `4`. -/
theorem main_aMem_mult_eq_neg_two_of_mem_op_four
    {env : Environment FGL} {row : Var MainRowWithRom FGL}
    (h_mem : (eval env row).rom.a_src_mem * (1 - (eval env row).rom.a_src_mem) = 0)
    (h_reg : (eval env row).rom.a_src_reg * (1 - (eval env row).rom.a_src_reg) = 0)
    (h_op : (eval env (ZiskFv.AirsClean.Main.aMemMessageExpr row)).mem_op = 4) :
    (((MemBusChannel.emitted (-(row.rom.a_src_mem + row.rom.a_src_reg))
      (ZiskFv.AirsClean.Main.aMemMessageExpr row)).toRaw).eval env).mult = -2 := by
  rw [ZiskFv.AirsClean.Main.eval_aMemMessageExpr] at h_op
  change (eval env row).rom.a_src_mem + 3 * (eval env row).rom.a_src_reg = 4 at h_op
  obtain ⟨h_a_mem, h_a_reg, -⟩ := main_rom_eval env row
  rw [memBus_emitted_eval_mult]
  have h_eval : Expression.eval env (-(row.rom.a_src_mem + row.rom.a_src_reg))
      = -((eval env row).rom.a_src_mem + (eval env row).rom.a_src_reg) := by
    simp only [Expression.eval, h_a_mem, h_a_reg]; ring
  rw [h_eval]
  rcases zero_or_one_of_bool h_mem with h1 | h1 <;>
    rcases zero_or_one_of_bool h_reg with h2 | h2 <;>
      rw [h1, h2] at h_op ⊢ <;> norm_num at h_op ⊢
  · exact absurd h_op (by decide)
  · exact absurd h_op (by decide)
  · exact absurd h_op (by decide)

/-- The b-side current access rides at `-2` when its `mem_op` is `4`. -/
theorem main_bMem_mult_eq_neg_two_of_mem_op_four
    {env : Environment FGL} {row : Var MainRowWithRom FGL}
    (h_mem : (eval env row).rom.b_src_mem * (1 - (eval env row).rom.b_src_mem) = 0)
    (h_ind : (eval env row).rom.b_src_ind * (1 - (eval env row).rom.b_src_ind) = 0)
    (h_reg : (eval env row).rom.b_src_reg * (1 - (eval env row).rom.b_src_reg) = 0)
    (h_op : (eval env (ZiskFv.AirsClean.Main.bMemMessageExpr row)).mem_op = 4) :
    (((MemBusChannel.emitted
      (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
      (ZiskFv.AirsClean.Main.bMemMessageExpr row)).toRaw).eval env).mult = -2 := by
  rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] at h_op
  change ((eval env row).rom.b_src_mem + (eval env row).rom.b_src_ind)
    + 3 * (eval env row).rom.b_src_reg = 4 at h_op
  obtain ⟨-, -, h_b_mem, h_b_ind, h_b_reg, -⟩ := main_rom_eval env row
  rw [memBus_emitted_eval_mult]
  have h_eval :
      Expression.eval env (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
      = -((eval env row).rom.b_src_mem + (eval env row).rom.b_src_ind
          + (eval env row).rom.b_src_reg) := by
    simp only [Expression.eval, h_b_mem, h_b_ind, h_b_reg]; ring
  rw [h_eval]
  rcases zero_or_one_of_bool h_mem with h1 | h1 <;>
    rcases zero_or_one_of_bool h_ind with h2 | h2 <;>
      rcases zero_or_one_of_bool h_reg with h3 | h3 <;>
        rw [h1, h2, h3] at h_op ⊢ <;> norm_num at h_op ⊢ <;>
          first
            | rfl
            | exact absurd h_op (by decide)

/-- The store-side current access rides at `-2` when its `mem_op` is `4`. -/
theorem main_cMem_mult_eq_neg_two_of_mem_op_four
    {env : Environment FGL} {row : Var MainRowWithRom FGL}
    (h_mem : (eval env row).rom.store_mem * (1 - (eval env row).rom.store_mem) = 0)
    (h_ind : (eval env row).rom.store_ind * (1 - (eval env row).rom.store_ind) = 0)
    (h_reg : (eval env row).rom.store_reg * (1 - (eval env row).rom.store_reg) = 0)
    (h_op : (eval env (ZiskFv.AirsClean.Main.cMemMessageExpr row)).mem_op = 4) :
    (((MemBusChannel.emitted
      (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
      (ZiskFv.AirsClean.Main.cMemMessageExpr row)).toRaw).eval env).mult = -2 := by
  rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr] at h_op
  change 2 * ((eval env row).rom.store_mem + (eval env row).rom.store_ind)
    + 3 * (eval env row).rom.store_reg = 4 at h_op
  obtain ⟨-, -, -, -, -, h_c_mem, h_c_ind, h_c_reg⟩ := main_rom_eval env row
  rw [memBus_emitted_eval_mult]
  have h_eval :
      Expression.eval env (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
      = -((eval env row).rom.store_mem + (eval env row).rom.store_ind
          + (eval env row).rom.store_reg) := by
    simp only [Expression.eval, h_c_mem, h_c_ind, h_c_reg]; ring
  rw [h_eval]
  rcases zero_or_one_of_bool h_mem with h1 | h1 <;>
    rcases zero_or_one_of_bool h_ind with h2 | h2 <;>
      rcases zero_or_one_of_bool h_reg with h3 | h3 <;>
        rw [h1, h2, h3] at h_op ⊢ <;> norm_num at h_op ⊢ <;>
          first
            | rfl
            | exact absurd h_op (by decide)


/-- Projecting `mem_op` commutes with evaluating a memory-bus message. -/
theorem memBusMessage_eval_mem_op
    (env : Environment FGL)
    (msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)) :
    (eval env msg).mem_op = Expression.eval env msg.mem_op := by
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field]

/-- `mem_op` projection for a *pulled* memory-bus interaction, the `MemAlignByte` /
`MemAlignReadByte` read shape. Mirrors the `pushed` and `emitted` variants in
`MemBusRowBridges`. -/
theorem memBusMessage_mem_op_eq_of_eval_pulled_provider_msg_eq
    {mainMsg providerMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {mainMult : Expression FGL}
    {mainEnv providerEnv : Environment FGL}
    (h_msg :
      (((MemBusChannel.pulled providerMsg).toRaw).eval providerEnv).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval mainEnv).msg) :
    (eval providerEnv providerMsg).mem_op = (eval mainEnv mainMsg).mem_op := by
  have h_vec :
      Vector.map (Expression.eval providerEnv) (toElements providerMsg) =
        Vector.map (Expression.eval mainEnv) (toElements mainMsg) := by
    apply Vector.toArray_injective
    simpa [ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_eval : eval providerEnv providerMsg = eval mainEnv mainMsg := by
    have h_from := congrArg
      (fun xs => (fromElements xs :
        ZiskFv.Channels.MemoryBus.MemBusMessage FGL)) h_vec
    simpa [ProvableType.fromElements_eval_toElements] using h_from
  exact congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.mem_op h_eval

/-- Main's eight operand-source flags are boolean at any row satisfying the component's
constraints. -/
theorem main_source_flags_boolean
    {length : ℕ} {program : Program length}
    {table : Table FGL} {row : Array FGL}
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    (h_constraints : table.Constraints) (h_row : row ∈ table.table) :
    (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_mem) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_ind) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.b_src_reg) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_mem) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_ind) = 0
  ∧ (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg
      * (1 - (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.store_reg) = 0 := by
  have h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold
        (table.environment row) := by
    have := h_constraints row h_row
    rwa [h_component] at this
  obtain ⟨-, -, -, -, h_a_mem, -, -, h_b_mem, h_c_mem, h_c_ind, h_b_ind, h_a_reg, h_b_reg,
    h_c_reg⟩ :=
    ZiskFv.AirsClean.Main.romBoolSpec_of_componentWithRomMemAndOpBus_constraints
      length program (table.environment row) h_holds
  obtain ⟨e_a_mem, e_a_reg, e_b_mem, e_b_ind, e_b_reg, e_c_mem, e_c_ind, e_c_reg⟩ :=
    main_rom_eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Expression.eval, sub_eq_add_neg, e_a_mem] using h_a_mem
  · simpa [Expression.eval, sub_eq_add_neg, e_a_reg] using h_a_reg
  · simpa [Expression.eval, sub_eq_add_neg, e_b_mem] using h_b_mem
  · simpa [Expression.eval, sub_eq_add_neg, e_b_ind] using h_b_ind
  · simpa [Expression.eval, sub_eq_add_neg, e_b_reg] using h_b_reg
  · simpa [Expression.eval, sub_eq_add_neg, e_c_mem] using h_c_mem
  · simpa [Expression.eval, sub_eq_add_neg, e_c_ind] using h_c_ind
  · simpa [Expression.eval, sub_eq_add_neg, e_c_reg] using h_c_reg

/-! ## No other emission in the ensemble reaches `mem_op = 4`

Main's three register-pre pushes carry the literal `3`; `RegisterBoundary`'s boot and reload carry
the literal `3`; `MemAlignReadByte` carries `1`; `MemAlign`, `MemAlignByte` and `Mem` carry `wr + 1`
or `1 + is_write` for a flag their own `Spec` pins to `{0, 1}`. Each case below reads the provider's
`mem_op` off the shared message and contradicts `4`. -/

/-- Every memory-bus interaction of the witness carrying the same message as a reference emission
whose `mem_op` is `4` rides at multiplicity `-2`.

This is the whole content of the exclusivity argument. The reference is a Main a-side current access
on a row that sets both `a_src_mem` and `a_src_reg`; the conclusion says nothing else in the
ensemble can offset it. -/
theorem memBus_mult_eq_of_msg_eq_mem_op_high
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {k m : FGL} (h_k1 : k ≠ 1) (h_k2 : k ≠ 2) (h_k3 : k ≠ 3)
    (h_slot_a : ∀ {env : Environment FGL} {row : Var MainRowWithRom FGL},
      (eval env row).rom.a_src_mem * (1 - (eval env row).rom.a_src_mem) = 0 →
      (eval env row).rom.a_src_reg * (1 - (eval env row).rom.a_src_reg) = 0 →
      (eval env (ZiskFv.AirsClean.Main.aMemMessageExpr row)).mem_op = k →
      (((MemBusChannel.emitted (-(row.rom.a_src_mem + row.rom.a_src_reg))
        (ZiskFv.AirsClean.Main.aMemMessageExpr row)).toRaw).eval env).mult = m)
    (h_slot_b : ∀ {env : Environment FGL} {row : Var MainRowWithRom FGL},
      (eval env row).rom.b_src_mem * (1 - (eval env row).rom.b_src_mem) = 0 →
      (eval env row).rom.b_src_ind * (1 - (eval env row).rom.b_src_ind) = 0 →
      (eval env row).rom.b_src_reg * (1 - (eval env row).rom.b_src_reg) = 0 →
      (eval env (ZiskFv.AirsClean.Main.bMemMessageExpr row)).mem_op = k →
      (((MemBusChannel.emitted
        (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
        (ZiskFv.AirsClean.Main.bMemMessageExpr row)).toRaw).eval env).mult = m)
    (h_slot_c : ∀ {env : Environment FGL} {row : Var MainRowWithRom FGL},
      (eval env row).rom.store_mem * (1 - (eval env row).rom.store_mem) = 0 →
      (eval env row).rom.store_ind * (1 - (eval env row).rom.store_ind) = 0 →
      (eval env row).rom.store_reg * (1 - (eval env row).rom.store_reg) = 0 →
      (eval env (ZiskFv.AirsClean.Main.cMemMessageExpr row)).mem_op = k →
      (((MemBusChannel.emitted
        (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
        (ZiskFv.AirsClean.Main.cMemMessageExpr row)).toRaw).eval env).mult = m)
    {refEnv : Environment FGL} {refMult : Expression FGL}
    {refMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_ref_op : (eval refEnv refMsg).mem_op = k)
    {j : Interaction FGL} (h_j : j ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_msg : j.msg = (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg) :
    j.mult = m := by
  rw [EnsembleWitness.mem_interactionsWith] at h_j
  obtain ⟨table, h_table, h_mem_table⟩ := h_j
  have h_component_mem :
      table.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  -- Every emission of the row this interaction comes from carries its own `mem_op`; matching the
  -- reference message forces that value to be `4`.
  have h_op_of_emitted :
      ∀ {env : Environment FGL} {m : Expression FGL}
        {msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)},
        j = ((MemBusChannel.emitted m msg).toRaw).eval env →
          (eval env msg).mem_op = k := by
    intro env m msg h_eval
    have h_raw :
        (((MemBusChannel.emitted m msg).toRaw).eval env).msg =
          (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg := by
      rw [← h_eval]; exact h_msg
    have := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [this, h_ref_op]
  have h_op_of_pushed :
      ∀ {env : Environment FGL}
        {msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)},
        j = ((MemBusChannel.pushed msg).toRaw).eval env →
          (eval env msg).mem_op = k := by
    intro env msg h_eval
    have h_raw :
        (((MemBusChannel.pushed msg).toRaw).eval env).msg =
          (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg := by
      rw [← h_eval]; exact h_msg
    have := memBusMessage_mem_op_eq_of_eval_pushed_provider_msg_eq (h_msg := h_raw)
    rw [this, h_ref_op]
  have h_op_of_pulled :
      ∀ {env : Environment FGL}
        {msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)},
        j = ((MemBusChannel.pulled msg).toRaw).eval env →
          (eval env msg).mem_op = k := by
    intro env msg h_eval
    have h_raw :
        (((MemBusChannel.pulled msg).toRaw).eval env).msg =
          (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg := by
      rw [← h_eval]; exact h_msg
    have := memBusMessage_mem_op_eq_of_eval_pulled_provider_msg_eq (h_msg := h_raw)
    rw [this, h_ref_op]
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_regBoundary | h_marb | h_mab | h_memAlign | h_memAlignRange | h_memAlignRom |
    h_mem | h_ranges | h_regRange | h_arithDiv | h_arithMul | h_binExt | h_binary | h_binaryAdd |
    h_main
  -- Components with no memory-bus interactions at all.
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith MemBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_memBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  -- RegisterBoundary: both emissions carry the literal `3`.
  · exfalso
    rcases exists_registerBoundary_mem_row_eval_of_interaction_mem h_regBoundary h_mem_table with
      ⟨row, _h_row, h_eval⟩ | ⟨row, _h_row, h_eval⟩
    · have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.RegisterBoundary.eval_bootMessageExpr] at h_op
      have h_lit : (3 : FGL) = k := by
        simpa [ZiskFv.AirsClean.RegisterBoundary.bootMessage] using h_op
      exact h_k3 h_lit.symm
    · have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.RegisterBoundary.eval_reloadMessageExpr] at h_op
      have h_lit : (3 : FGL) = k := by
        simpa [ZiskFv.AirsClean.RegisterBoundary.reloadMessage] using h_op
      exact h_k3 h_lit.symm
  -- MemAlignReadByte: both emissions carry the literal `1`.
  · exfalso
    rcases exists_memBus_row_eval_of_pair_interactionsWith
        (by simpa [h_marb] using
          ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus)
        h_mem_table with
      ⟨row, _h_row, h_eval⟩ | ⟨row, _h_row, h_eval⟩
    · have h_op := h_op_of_pulled h_eval
      rw [memBusMessage_eval_mem_op] at h_op
      have h_lit : (1 : FGL) = k := by
        simpa [ZiskFv.AirsClean.MemAlignReadByte.memReadMessageExpr, Expression.eval] using h_op
      exact h_k1 h_lit.symm
    · have h_op := h_op_of_pushed h_eval
      rw [ZiskFv.AirsClean.MemAlignReadByte.eval_memBusMessageExpr] at h_op
      have h_lit : (1 : FGL) = k := by
        simpa [ZiskFv.AirsClean.MemAlignReadByte.memBusMessage] using h_op
      exact h_k1 h_lit.symm
  -- MemAlignByte: the read carries `1`, the write-back `1 + is_write` for a bounded `is_write`.
  · exfalso
    have h_rowSpec := h_specs table h_table
    rcases exists_memBus_row_eval_of_pair_interactionsWith
        (by simpa [h_mab] using
          ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus)
        h_mem_table with
      ⟨row, h_row, h_eval⟩ | ⟨row, h_row, h_eval⟩
    · have h_op := h_op_of_pulled h_eval
      rw [memBusMessage_eval_mem_op] at h_op
      have h_lit : (1 : FGL) = k := by
        simpa [ZiskFv.AirsClean.MemAlignByte.memReadMessageExpr, Expression.eval] using h_op
      exact h_k1 h_lit.symm
    · have h_spec := h_rowSpec row h_row
      rw [h_mab, ZiskFv.AirsClean.MemAlignByte.component_spec,
        component_rowInput_eq_eval_rowInputVar] at h_spec
      have h_isw := h_spec.2.2.2.2.2.2.2
      have h_op := h_op_of_pushed h_eval
      rw [ZiskFv.AirsClean.MemAlignByte.eval_memBusMessageExpr] at h_op
      change 1 + (eval (table.environment row)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar).is_write = k at h_op
      rcases zero_or_one_of_val_lt_two (by simpa using h_isw) with h0 | h1
      · rw [h0] at h_op
        have h_lit : (1 : FGL) = k := by rw [← h_op]; ring
        exact h_k1 h_lit.symm
      · rw [h1] at h_op
        have h_lit : (2 : FGL) = k := by rw [← h_op]; norm_num
        exact h_k2 h_lit.symm
  -- MemAlign: `mem_op = wr + 1` with `wr` boolean.
  · exfalso
    have h_rowSpec := h_specs table h_table
    obtain ⟨row, h_row, h_eval⟩ :=
      exists_memBus_row_eval_of_singleton_interactionsWith
        (by simpa [h_memAlign] using
          ZiskFv.AirsClean.MemAlign.component_interactionsWith_memBus)
        h_mem_table
    have h_spec := h_rowSpec row h_row
    rw [h_memAlign, ZiskFv.AirsClean.MemAlign.component_spec,
      component_rowInput_eq_eval_rowInputVar] at h_spec
    have h_wr := h_spec.1
    have h_op := h_op_of_emitted h_eval
    rw [ZiskFv.AirsClean.MemAlign.eval_memBusMessageExpr] at h_op
    change (eval (table.environment row)
      ZiskFv.AirsClean.MemAlign.component.rowInputVar).wr + 1 = k at h_op
    rcases zero_or_one_of_bool h_wr with h0 | h1
    · rw [h0] at h_op
      have h_lit : (1 : FGL) = k := by rw [← h_op]; ring
      exact h_k1 h_lit.symm
    · rw [h1] at h_op
      have h_lit : (2 : FGL) = k := by rw [← h_op]; norm_num
      exact h_k2 h_lit.symm
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      memAlignRangeSlice_table_interactionsWith_memBus_nil h_memAlignRange
    simp [h_nil] at h_mem_table
  · exfalso
    have h_nil : table.interactionsWith MemBusChannel.toRaw = [] :=
      memAlignRomSlice_table_interactionsWith_memBus_nil h_memAlignRom
    simp [h_nil] at h_mem_table
  -- Mem: the primary emission is `wr + 1` with `wr` boolean, the dual emission is the literal `1`.
  · exfalso
    have h_rowSpec := h_specs table h_table
    rcases exists_memBus_row_eval_of_pair_interactionsWith
        (by simpa [h_mem] using
          ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus)
        h_mem_table with
      ⟨row, h_row, h_eval⟩ | ⟨row, h_row, h_eval⟩
    · have h_spec := h_rowSpec row h_row
      rw [h_mem] at h_spec
      have h_rowSpec' := ZiskFv.AirsClean.Mem.spec_of_componentWithDualMemBus_spec _ h_spec
      rw [component_rowInput_eq_eval_rowInputVar] at h_rowSpec'
      have h_wr := h_rowSpec'.2.2.2.2.1
      have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] at h_op
      change (eval (table.environment row)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr + 1 = k at h_op
      rcases zero_or_one_of_bool h_wr with h0 | h1
      · rw [h0] at h_op
        have h_lit : (1 : FGL) = k := by rw [← h_op]; ring
        exact h_k1 h_lit.symm
      · rw [h1] at h_op
        have h_lit : (2 : FGL) = k := by rw [← h_op]; norm_num
        exact h_k2 h_lit.symm
    · have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr] at h_op
      have h_lit : (1 : FGL) = k := by
        simpa [ZiskFv.AirsClean.Mem.memBusDualMessage] using h_op
      exact h_k1 h_lit.symm
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
  -- Main: the three register-pre pushes carry `3`; the three current accesses are pulls that
  -- booleanity pins to `-2` once their `mem_op` is `4`.
  · obtain ⟨row, h_row, h_branch⟩ :=
      exists_main_mem_row_eval_of_interaction_mem h_main h_mem_table
    obtain ⟨b_a_mem, b_a_reg, b_b_mem, b_b_ind, b_b_reg, b_c_mem, b_c_ind, b_c_reg⟩ :=
      main_source_flags_boolean h_main (h_constraints table h_table) h_row
    rcases h_branch with h_eval | h_eval | h_eval | h_eval | h_eval | h_eval
    · exfalso
      have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Main.eval_aRegPreMessageExpr] at h_op
      have h_lit : (3 : FGL) = k := by
        simpa [ZiskFv.AirsClean.Main.aRegPreMessage] using h_op
      exact h_k3 h_lit.symm
    · rw [h_eval]
      exact h_slot_a b_a_mem b_a_reg (h_op_of_emitted h_eval)
    · exfalso
      have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Main.eval_bRegPreMessageExpr] at h_op
      have h_lit : (3 : FGL) = k := by
        simpa [ZiskFv.AirsClean.Main.bRegPreMessage] using h_op
      exact h_k3 h_lit.symm
    · rw [h_eval]
      exact h_slot_b b_b_mem b_b_ind b_b_reg (h_op_of_emitted h_eval)
    · exfalso
      have h_op := h_op_of_emitted h_eval
      rw [ZiskFv.AirsClean.Main.eval_cRegPreMessageExpr] at h_op
      have h_lit : (3 : FGL) = k := by
        simpa [ZiskFv.AirsClean.Main.cRegPreMessage] using h_op
      exact h_k3 h_lit.symm
    · rw [h_eval]
      exact h_slot_c b_c_mem b_c_ind b_c_reg (h_op_of_emitted h_eval)


/-- The `mem_op = 4` instance: all three Main current accesses ride at `-2` there. -/
theorem memBus_mult_eq_neg_two_of_msg_eq_mem_op_four
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {refEnv : Environment FGL} {refMult : Expression FGL}
    {refMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_ref_op : (eval refEnv refMsg).mem_op = 4)
    {j : Interaction FGL} (h_j : j ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_msg : j.msg = (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg) :
    j.mult = -2 :=
  memBus_mult_eq_of_msg_eq_mem_op_high h_constraints h_specs
    (by decide) (by decide) (by decide)
    (fun h1 h2 h3 => main_aMem_mult_eq_neg_two_of_mem_op_four h1 h2 h3)
    (fun h1 h2 h3 h4 => main_bMem_mult_eq_neg_two_of_mem_op_four h1 h2 h3 h4)
    (fun h1 h2 h3 h4 => main_cMem_mult_eq_neg_two_of_mem_op_four h1 h2 h3 h4)
    h_ref_op h_j h_msg

/-! ## The exclusivity, from balance -/

/-- A natural number below the modulus that casts to `0` in the field is `0`. This is what turns
`-2 * count = 0` into `count = 0`. -/
private lemma natCast_eq_zero_of_lt_prime {c : ℕ} (h_lt : c < GL_prime) (h : (c : FGL) = 0) :
    c = 0 := by
  have h_dvd : GL_prime ∣ c := (ZMod.natCast_eq_zero_iff c GL_prime).mp h
  exact Nat.eq_zero_of_dvd_of_lt h_dvd h_lt


/-- **A message whose every interaction rides at one nonzero multiplicity cannot balance.**

    The balance at that message is `m * count`; `count` is at least one because the witnessing
    interaction is itself counted, and below the modulus because the whole interaction list is. With
    `m` invertible that product cannot vanish. -/
theorem no_balanced_message_with_constant_nonzero_mult
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    {m : FGL} (h_m : m ≠ 0)
    {I : Interaction FGL} (h_I : I ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_I_mult : I.mult = m)
    (h_all : ∀ i ∈ witness.interactionsWith MemBusChannel.toRaw,
      i.msg = I.msg → i.mult ≠ 0 → i.mult = m) :
    False := by
  have h_balance := memBus_balanced_of_witness witness h_balanced
  have h_zero := h_balance.2 I.msg
  rw [balanceOf_eq_of_mult_or_zero h_all] at h_zero
  set count : ℕ :=
    (witness.interactionsWith MemBusChannel.toRaw).countP
      (fun i => i.msg = I.msg && i.mult ≠ 0) with h_count
  have h_count_pos : 0 < count := by
    rw [h_count, List.countP_pos_iff]
    exact ⟨I, h_I, by simp [h_I_mult, h_m]⟩
  have h_count_lt : count < ringChar FGL ∨ ringChar FGL = 0 := by
    rcases count_lt_ringChar_of_balancedInteractions (msg := I.msg) h_balance with h | h
    · exact Or.inl (lt_of_le_of_lt (List.countP_and_left_le _ _ _) h)
    · exact Or.inr h
  have h_cast : ((count : ℕ) : FGL) = 0 := by
    rcases mul_eq_zero.mp h_zero with h | h
    · exact absurd h h_m
    · exact h
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime] at h_count_lt
  have h_count_zero : count = 0 := by
    rcases h_count_lt with h_lt | h_char
    · exact natCast_eq_zero_of_lt_prime h_lt h_cast
    · exact absurd h_char (by decide)
  omega




/-- A Main row's a-side current access really is one of the witness's memory-bus interactions. -/
theorem main_aMem_interaction_mem_witness
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table) :
    (((MemBusChannel.emitted
      (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
        + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
      (ZiskFv.AirsClean.Main.aMemMessageExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row))
      ∈ witness.interactionsWith MemBusChannel.toRaw := by
  rw [EnsembleWitness.mem_interactionsWith]
  refine ⟨table, h_table, ?_⟩
  rw [Table.interactionsWith]
  refine List.mem_flatMap.mpr ⟨row, h_row, ?_⟩
  rw [Operations.interactionValuesWith_eq_map, h_component,
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_memBus]
  simp

set_option maxHeartbeats 1000000 in
/-- **Main's a-side operand sources are exclusive, and `BalancedChannels` is what proves it.**

    A row setting both `a_src_mem` and `a_src_reg` emits its a-side current access at
    `mem_op = 4` and multiplicity `-2`. By `memBus_mult_eq_neg_two_of_msg_eq_mem_op_four`, every
    interaction of the witness carrying that same message also rides at `-2`, so the balance at that
    message is `-2 * count` with `count ≥ 1`. Since `count` is below the field characteristic and
    `2` is invertible, that cannot vanish.

    No decode fact and no ROM binding is used: the flags are pinned by the multiplicity ledger
    alone. -/
theorem main_not_a_src_mem_and_a_src_reg
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (h_src_mem : (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem = 1)
    (h_src_reg : (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg = 1) :
    False := by
  set env := table.environment row with h_env
  set rowVar := (componentWithRomMemAndOpBus length program).rowInputVar with h_rowVar
  set refMult : Expression FGL := -(rowVar.rom.a_src_mem + rowVar.rom.a_src_reg) with h_refMult
  set refMsg := ZiskFv.AirsClean.Main.aMemMessageExpr rowVar with h_refMsg
  set I := (((MemBusChannel.emitted refMult refMsg).toRaw).eval env) with h_I
  -- the reference message sits at `mem_op = 4`
  have h_ref_op : (eval env refMsg).mem_op = 4 := by
    rw [h_refMsg, ZiskFv.AirsClean.Main.eval_aMemMessageExpr]
    change (eval env rowVar).rom.a_src_mem + 3 * (eval env rowVar).rom.a_src_reg = 4
    rw [h_src_mem, h_src_reg]
    norm_num
  have h_I_mem : I ∈ witness.interactionsWith MemBusChannel.toRaw :=
    main_aMem_interaction_mem_witness h_table h_component h_row
  have h_I_mult : I.mult = -2 :=
    main_aMem_mult_eq_neg_two_of_mem_op_four
      (by rw [h_src_mem]; ring) (by rw [h_src_reg]; ring) h_ref_op
  -- every interaction on that message rides at `-2`
  have h_all :
      ∀ i ∈ witness.interactionsWith MemBusChannel.toRaw,
        i.msg = I.msg → i.mult ≠ 0 → i.mult = -2 := by
    intro i h_i h_msg _
    exact memBus_mult_eq_neg_two_of_msg_eq_mem_op_four h_constraints h_specs h_ref_op h_i h_msg
  have h_balance := memBus_balanced_of_witness witness h_balanced
  have h_zero := h_balance.2 I.msg
  rw [balanceOf_eq_of_mult_or_zero h_all] at h_zero
  set count : ℕ :=
    (witness.interactionsWith MemBusChannel.toRaw).countP
      (fun i => i.msg = I.msg && i.mult ≠ 0) with h_count
  -- the reference interaction itself is counted
  have h_count_pos : 0 < count := by
    rw [h_count, List.countP_pos_iff]
    exact ⟨I, h_I_mem, by simp [h_I_mult]⟩
  -- and the count is below the characteristic
  have h_count_lt : count < ringChar FGL ∨ ringChar FGL = 0 := by
    rcases count_lt_ringChar_of_balancedInteractions (msg := I.msg) h_balance with h | h
    · exact Or.inl (lt_of_le_of_lt (List.countP_and_left_le _ _ _) h)
    · exact Or.inr h
  -- `-2 * count = 0` with `2` invertible forces `count = 0`
  have h_cast : ((count : ℕ) : FGL) = 0 := by
    have h2 : (-2 : FGL) ≠ 0 := by decide
    rcases mul_eq_zero.mp h_zero with h | h
    · exact absurd h h2
    · exact h
  rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime] at h_count_lt
  have h_count_zero : count = 0 := by
    rcases h_count_lt with h_lt | h_char
    · exact natCast_eq_zero_of_lt_prime h_lt h_cast
    · exact absurd h_char (by decide)
  omega


/-- **A register-reading row does not also read memory on the a side.** Immediate from
    `main_not_a_src_mem_and_a_src_reg` plus booleanity. -/
theorem main_a_src_mem_eq_zero_of_a_src_reg
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (h_src_reg : (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg = 1) :
    (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem = 0 := by
  obtain ⟨b_a_mem, -⟩ := main_source_flags_boolean h_component (h_constraints table h_table) h_row
  rcases zero_or_one_of_bool b_a_mem with h | h
  · exact h
  · exact absurd (main_not_a_src_mem_and_a_src_reg h_balanced h_constraints h_specs h_table
      h_component h_row h h_src_reg) (by simp)

/-- **The a-side access of a register-reading row is a genuine `-1` pull at `mem_op = 3`.**

    This is the shape Clean's `exists_push_of_pull` consumes, so it is what lets the register walk
    take another step from a supplying row rather than stopping there. Both halves come from
    exclusivity: the multiplicity is `-(0 + 1)` and the opcode is `0 + 3 * 1`. -/
theorem main_aMem_pull_of_a_src_reg
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels)
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = componentWithRomMemAndOpBus length program)
    {row : Array FGL} (h_row : row ∈ table.table)
    (h_src_reg : (eval (table.environment row)
      (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg = 1) :
    (((MemBusChannel.emitted
      (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
        + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
      (ZiskFv.AirsClean.Main.aMemMessageExpr
        (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
      (table.environment row)).mult = -1
    ∧ (eval (table.environment row)
        (ZiskFv.AirsClean.Main.aMemMessageExpr
          (componentWithRomMemAndOpBus length program).rowInputVar)).mem_op = 3 := by
  have h_src_mem := main_a_src_mem_eq_zero_of_a_src_reg h_balanced h_constraints h_specs
    h_table h_component h_row h_src_reg
  obtain ⟨e_a_mem, e_a_reg, -⟩ :=
    main_rom_eval (table.environment row) (componentWithRomMemAndOpBus length program).rowInputVar
  constructor
  · rw [memBus_emitted_eval_mult]
    have h_eval :
        Expression.eval (table.environment row)
          (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
            + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
        = -((eval (table.environment row)
              (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem
            + (eval (table.environment row)
              (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg) := by
      simp only [Expression.eval, e_a_mem, e_a_reg]; ring
    rw [h_eval, h_src_mem, h_src_reg]
    norm_num
  · rw [ZiskFv.AirsClean.Main.eval_aMemMessageExpr]
    change (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_mem
      + 3 * (eval (table.environment row)
        (componentWithRomMemAndOpBus length program).rowInputVar).rom.a_src_reg = 3
    rw [h_src_mem, h_src_reg]
    norm_num


/-! ## `mem_op = 7`: only the store-side current access can reach it

`a_src_mem + 3 * a_src_reg` tops out at `4` and `(b_src_mem + b_src_ind) + 3 * b_src_reg` at `5`, so
at `7` the a- and b-side hypotheses are vacuous. The store side reaches `7` only at
`store_mem = store_ind = 1, store_reg = 1`, where its multiplicity is `-3`. -/

theorem main_aMem_mult_of_mem_op_seven
    {env : Environment FGL} {row : Var MainRowWithRom FGL}
    (h_mem : (eval env row).rom.a_src_mem * (1 - (eval env row).rom.a_src_mem) = 0)
    (h_reg : (eval env row).rom.a_src_reg * (1 - (eval env row).rom.a_src_reg) = 0)
    (h_op : (eval env (ZiskFv.AirsClean.Main.aMemMessageExpr row)).mem_op = 7) :
    (((MemBusChannel.emitted (-(row.rom.a_src_mem + row.rom.a_src_reg))
      (ZiskFv.AirsClean.Main.aMemMessageExpr row)).toRaw).eval env).mult = -3 := by
  exfalso
  rw [ZiskFv.AirsClean.Main.eval_aMemMessageExpr] at h_op
  change (eval env row).rom.a_src_mem + 3 * (eval env row).rom.a_src_reg = 7 at h_op
  rcases zero_or_one_of_bool h_mem with h1 | h1 <;>
    rcases zero_or_one_of_bool h_reg with h2 | h2 <;>
      rw [h1, h2] at h_op <;> norm_num at h_op <;> exact absurd h_op (by decide)

theorem main_bMem_mult_of_mem_op_seven
    {env : Environment FGL} {row : Var MainRowWithRom FGL}
    (h_mem : (eval env row).rom.b_src_mem * (1 - (eval env row).rom.b_src_mem) = 0)
    (h_ind : (eval env row).rom.b_src_ind * (1 - (eval env row).rom.b_src_ind) = 0)
    (h_reg : (eval env row).rom.b_src_reg * (1 - (eval env row).rom.b_src_reg) = 0)
    (h_op : (eval env (ZiskFv.AirsClean.Main.bMemMessageExpr row)).mem_op = 7) :
    (((MemBusChannel.emitted
      (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
      (ZiskFv.AirsClean.Main.bMemMessageExpr row)).toRaw).eval env).mult = -3 := by
  exfalso
  rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] at h_op
  change ((eval env row).rom.b_src_mem + (eval env row).rom.b_src_ind)
    + 3 * (eval env row).rom.b_src_reg = 7 at h_op
  rcases zero_or_one_of_bool h_mem with h1 | h1 <;>
    rcases zero_or_one_of_bool h_ind with h2 | h2 <;>
      rcases zero_or_one_of_bool h_reg with h3 | h3 <;>
        rw [h1, h2, h3] at h_op <;> norm_num at h_op <;> exact absurd h_op (by decide)

theorem main_cMem_mult_of_mem_op_seven
    {env : Environment FGL} {row : Var MainRowWithRom FGL}
    (h_mem : (eval env row).rom.store_mem * (1 - (eval env row).rom.store_mem) = 0)
    (h_ind : (eval env row).rom.store_ind * (1 - (eval env row).rom.store_ind) = 0)
    (h_reg : (eval env row).rom.store_reg * (1 - (eval env row).rom.store_reg) = 0)
    (h_op : (eval env (ZiskFv.AirsClean.Main.cMemMessageExpr row)).mem_op = 7) :
    (((MemBusChannel.emitted
      (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
      (ZiskFv.AirsClean.Main.cMemMessageExpr row)).toRaw).eval env).mult = -3 := by
  rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr] at h_op
  change 2 * ((eval env row).rom.store_mem + (eval env row).rom.store_ind)
    + 3 * (eval env row).rom.store_reg = 7 at h_op
  obtain ⟨-, -, -, -, -, h_c_mem, h_c_ind, h_c_reg⟩ := main_rom_eval env row
  rw [memBus_emitted_eval_mult]
  have h_eval :
      Expression.eval env (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
      = -((eval env row).rom.store_mem + (eval env row).rom.store_ind
          + (eval env row).rom.store_reg) := by
    simp only [Expression.eval, h_c_mem, h_c_ind, h_c_reg]; ring
  rw [h_eval]
  rcases zero_or_one_of_bool h_mem with h1 | h1 <;>
    rcases zero_or_one_of_bool h_ind with h2 | h2 <;>
      rcases zero_or_one_of_bool h_reg with h3 | h3 <;>
        rw [h1, h2, h3] at h_op ⊢ <;> norm_num at h_op ⊢ <;>
          first
            | rfl
            | exact absurd h_op (by decide)

/-- The `mem_op = 7` instance of the classification. -/
theorem memBus_mult_eq_neg_three_of_msg_eq_mem_op_seven
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints) (h_specs : witness.Spec)
    {refEnv : Environment FGL} {refMult : Expression FGL}
    {refMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_ref_op : (eval refEnv refMsg).mem_op = 7)
    {j : Interaction FGL} (h_j : j ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_msg : j.msg = (((MemBusChannel.emitted refMult refMsg).toRaw).eval refEnv).msg) :
    j.mult = -3 :=
  memBus_mult_eq_of_msg_eq_mem_op_high h_constraints h_specs
    (by decide) (by decide) (by decide)
    (fun h1 h2 h3 => main_aMem_mult_of_mem_op_seven h1 h2 h3)
    (fun h1 h2 h3 h4 => main_bMem_mult_of_mem_op_seven h1 h2 h3 h4)
    (fun h1 h2 h3 h4 => main_cMem_mult_of_mem_op_seven h1 h2 h3 h4)
    h_ref_op h_j h_msg

end ZiskFv.AirsClean.FullEnsemble
