import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem

/-!
# ROM-driven decode binding (issue #159, BLOCK 1 pilot)

This module turns the *assumed* `Decode_add` decode columns
(`mainOfTable … .op i = OP_ADD`, `… .jmp_offset1 i = 4`, …, which today are
caller hypotheses on the `Decode_add` structure) into facts **derived** from
the committed program `trace.program`, via the circuit's Main↔ROM lookup.

This is the #61 "decode-driven" direction: instead of trusting that the
witness row's `op` column happens to be `OP_ADD`, we read the operation off the
*committed program's* instruction at the row's committed `pc`, using the
in-circuit ROM lookup soundness.

## The reused Clean lookup idiom

A Clean `StaticTable` lookup's soundness IS `table.Spec` of the looked-up
entry (`build/clean-lean/Clean/Circuit/Lookup.lean:140-147`,
`StaticTable.toTable` with `Soundness _ := table.Spec` and
`imply_soundness := contains_iff.mp`). For ZisK's ROM,
`romStaticTable.Spec msg := ∃ i, msg = program i` (membership;
`ZiskFv/AirsClean/ZiskInstructionRom.lean:56-67`). The already-proven
`ZiskFv.AirsClean.Main.romSpec_of_componentWithRomMemAndOpBus_constraints`
(`ZiskFv/AirsClean/Main/Circuit.lean:733`) projects, from
`(componentWithRomMemAndOpBus length program).operations.ConstraintsHold env`,
exactly `(romStaticTable length program).Spec (eval env (romMessageExpr …))`,
i.e. the row's evaluated 11-field ROM message equals SOME program entry. We
reuse that lemma wholesale; we do not re-derive lookup soundness.

## R1 — positional binding

The membership witness `j` has `(program j).line = mainOfTable.pc i` (the row's
committed `pc`): the row at trace index `i` binds to the program entry at
`pc(i)`, *not* necessarily `program i` (branches make `pc(i) ≠ i`). Uniqueness
of `j` — that it is THE entry at `pc(i)` — needs program-line distinctness,
which is NOT derivable from the existing accepted-trace facts (`Program` is an
abstract `Fin n → ZiskRomMessage`). We therefore do not assume uniqueness here:
the program-level decode premise of `Decode_add_of_program` is quantified over
*all* program entries at the row's committed line, so the existential witness
`j` discharges it directly. A positional/unique alternative would add a clean
`Function.Injective (fun i => (program i).line)` premise.

## Trust note

No axioms. The binding is derived purely from `trace.constraints_hold` (the
in-circuit ROM lookup) plus the membership-based `Table.Constraints` projection.
-/

/-! ## Component-level ROM-flag booleanity for the unified Main component

The repo already proves `is_external_op` booleanity at the unified-component
level (`is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints`) and
the 14 remaining flag booleans at the `componentWithRomAndMemBus` level
(`romBoolSpec_of_componentWithRomAndMemBus_constraints`). The two helpers below
fill the one missing variant — the 14 flag booleans at the
`componentWithRomMemAndOpBus` level — by delegating to the existing
`mainWithRomAndMemBus` row-level lemma exactly as
`romSpec_of_mainWithRomMemAndOpBus_constraints` does for the ROM lookup. -/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- Row-level 14-flag booleanity for the OpBus-extended Main circuit, by
    delegating to the `mainWithRomAndMemBus` variant (the added op-bus emission
    contributes no constraint). -/
theorem romBoolSpec_of_mainWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomMemAndOpBus length program row).operations offset)) :
    env (row.core.m32 * (1 - row.core.m32)) = 0
  ∧ env (row.core.set_pc * (1 - row.core.set_pc)) = 0
  ∧ env (row.core.store_pc * (1 - row.core.store_pc)) = 0
  ∧ env (row.rom.a_src_imm * (1 - row.rom.a_src_imm)) = 0
  ∧ env (row.rom.a_src_mem * (1 - row.rom.a_src_mem)) = 0
  ∧ env (row.rom.is_precompiled * (1 - row.rom.is_precompiled)) = 0
  ∧ env (row.rom.b_src_imm * (1 - row.rom.b_src_imm)) = 0
  ∧ env (row.rom.b_src_mem * (1 - row.rom.b_src_mem)) = 0
  ∧ env (row.rom.store_mem * (1 - row.rom.store_mem)) = 0
  ∧ env (row.rom.store_ind * (1 - row.rom.store_ind)) = 0
  ∧ env (row.rom.b_src_ind * (1 - row.rom.b_src_ind)) = 0
  ∧ env (row.rom.a_src_reg * (1 - row.rom.a_src_reg)) = 0
  ∧ env (row.rom.b_src_reg * (1 - row.rom.b_src_reg)) = 0
  ∧ env (row.rom.store_reg * (1 - row.rom.store_reg)) = 0 :=
  romBoolSpec_of_mainWithRomAndMemBus_constraints length program row offset env
    (by simpa only [mainWithRomMemAndOpBus] using h_holds)

/-- Component-level 14-flag booleanity for the unified Main component. -/
theorem romBoolSpec_of_componentWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold env) :
    env ((componentWithRomMemAndOpBus length program).rowInputVar.core.m32
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.core.m32)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.core.set_pc
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.core.set_pc)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.core.store_pc
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.core.store_pc)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_imm
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_imm)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.is_precompiled
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.is_precompiled)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_imm
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_imm)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg)) = 0
  ∧ env ((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg)) = 0 := by
  have h_row :
      (componentWithRomMemAndOpBus length program).rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff
      (component := componentWithRomMemAndOpBus length program) env).mp h_holds
  exact romBoolSpec_of_mainWithRomMemAndOpBus_constraints
    length program
    (componentWithRomMemAndOpBus length program).rowInputVar
    (componentWithRomMemAndOpBus length program).rowOffset env (by
      simpa only [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
        Component.rowOperations] using h_row)

end ZiskFv.AirsClean.Main

namespace ZiskFv.Compliance.RomDecodeBinding

open ZiskFv.Compliance
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainTableRowAtOrZero)
open ZiskFv.AirsClean.Main (componentWithRomMemAndOpBus romMessage romMessageExpr)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

/-- **Per-row Main constraints projection.**

The accepted trace's `constraints_hold : witness.Constraints` is
membership-based (`∀ table ∈ allTables, ∀ row ∈ table.table, …ConstraintsHold`).
This projects it to the unified Main component's `operations.ConstraintsHold`
at any in-range Main-table row, with the component already rewritten to
`componentWithRomMemAndOpBus` via `mainTable_component`. This is the hook that
feeds `romSpec_of_componentWithRomMemAndOpBus_constraints`. -/
theorem mainOperationsConstraintsHold_at
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    (componentWithRomMemAndOpBus numInstructions trace.program).operations.ConstraintsHold
      (trace.mainTable.environment (trace.mainTable.table.get idx)) := by
  have h_tableConstraints : trace.mainTable.Constraints :=
    trace.constraints_hold trace.mainTable trace.mainTable_mem
  have h_mem : trace.mainTable.table.get idx ∈ trace.mainTable.table :=
    List.mem_iff_get.mpr ⟨idx, rfl⟩
  have h_row := h_tableConstraints (trace.mainTable.table.get idx) h_mem
  rw [trace.mainTable_component] at h_row
  exact h_row

/-- **The reusable binding lemma (deliverable 1).**

For every in-range Main-table row `idx`, the row's evaluated 11-field ROM
message equals SOME committed program entry `j`. Concretely: the named-column
projection of the row (`mainTableRowAtOrZero …`), packed back into a
`ZiskRomMessage` by `romMessage`, equals `trace.program j`.

This is the foundation that ties EVERY Main row's decode columns to the
committed program, derived from `trace.constraints_hold` alone, via the
in-circuit ROM lookup. It is opcode-agnostic and reused by every per-op
`Decode_<op>_of_program`. -/
theorem mainRomMessage_at_eq_program
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    ∃ j : Fin trace.numInstructions,
      romMessage (mainTableRowAtOrZero trace.program trace.mainTable idx.val)
        = trace.program j := by
  have h_holds := mainOperationsConstraintsHold_at trace idx
  have h_spec :=
    ZiskFv.AirsClean.Main.romSpec_of_componentWithRomMemAndOpBus_constraints
      numInstructions trace.program
      (trace.mainTable.environment (trace.mainTable.table.get idx)) h_holds
  simp only [ZiskFv.AirsClean.ZiskInstructionRom.romStaticTable] at h_spec
  obtain ⟨j, hj⟩ := h_spec
  refine ⟨j, ?_⟩
  rw [← hj, ZiskFv.AirsClean.Main.eval_romMessageExpr,
    ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get]

/-- **Column-level form of the binding lemma.**

Projects the directly-columned ROM-message slots out of
`mainRomMessage_at_eq_program`, phrased against the `mainOfTable` named columns
and the bound program entry's fields. The `line = pc` conjunct is the R1
positional binding. The final conjunct records that the row's packed flags
equal the entry's `flags` (the flag pins are unpacked separately). -/
theorem mainDecodeColumns_at_eq_program
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    ∃ j : Fin trace.numInstructions,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc idx.val
    ∧ (trace.program j).op = (mainOfTable trace.program trace.mainTable).op idx.val
    ∧ (trace.program j).jmp_offset1
        = (mainOfTable trace.program trace.mainTable).jmp_offset1 idx.val
    ∧ (trace.program j).jmp_offset2
        = (mainOfTable trace.program trace.mainTable).jmp_offset2 idx.val
    ∧ (trace.program j).flags
        = ZiskFv.AirsClean.Main.romFlags
            (mainTableRowAtOrZero trace.program trace.mainTable idx.val) := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace idx
  refine ⟨j, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [← hj, romMessage,
      ZiskFv.AirsClean.FullEnsemble.mainOfTable_pc,
      ZiskFv.AirsClean.FullEnsemble.mainOfTable_op,
      ZiskFv.AirsClean.FullEnsemble.mainOfTable_jmp_offset1,
      ZiskFv.AirsClean.FullEnsemble.mainOfTable_jmp_offset2]

/-! ## Flag unpacking

The four ADD flag pins (`is_external_op = 1`, `m32 = 0`, `store_pc = 0`,
`set_pc = 0`) are not dedicated ROM-message slots: they are packed, with eleven
other booleans, into the single `flags` slot via `romFlags`/`packFlags`
(`main.pil:483-486`). The binding lemma therefore delivers
`romFlags row = (program j).flags`; to turn that into individual column pins we
need that the 15-bit packing is injective. That is the content below.

`packFlags` is a weighted sum of the 15 booleans with the distinct powers
`2^1 … 2^15` (plus the leading `1`), so its value lies in `[1, 2^16-1]`,
comfortably below `GL_prime`. Injectivity is therefore the uniqueness of binary
representation, lifted from `ℕ` through the bounded `Fin GL_prime` cast. -/

open ZiskFv.AirsClean.Main (RomFlagBits packFlags romFlags)

/-- `Bool.toNat`-valued mirror of `packFlags`. -/
private def packNat (b : RomFlagBits) : ℕ :=
  1 + 2 * b.a_src_imm.toNat + 4 * b.a_src_mem.toNat + 8 * b.is_precompiled.toNat
    + 16 * b.b_src_imm.toNat + 32 * b.b_src_mem.toNat + 64 * b.is_external_op.toNat
    + 128 * b.store_pc.toNat + 256 * b.store_mem.toNat + 512 * b.store_ind.toNat
    + 1024 * b.set_pc.toNat + 2048 * b.m32.toNat + 4096 * b.b_src_ind.toNat
    + 8192 * b.a_src_reg.toNat + 16384 * b.b_src_reg.toNat + 32768 * b.store_reg.toNat

/-- `boolF` agrees with the `Bool.toNat` cast. (Stated against the
    fully-qualified `ZiskFv.AirsClean.boolF` that `packFlags`/`romFlags` use.) -/
private lemma boolF_eq_cast_toNat (x : Bool) :
    ZiskFv.AirsClean.boolF x = ((x.toNat : ℕ) : FGL) := by
  cases x <;> simp [ZiskFv.AirsClean.boolF]

private lemma cast_packNat (b : RomFlagBits) : ((packNat b : ℕ) : FGL) = packFlags b := by
  simp only [packNat, packFlags, boolF_eq_cast_toNat]
  push_cast
  ring

private lemma packNat_lt (b : RomFlagBits) : packNat b < GL_prime := by
  have h : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> simp
  have := h b.a_src_imm; have := h b.a_src_mem; have := h b.is_precompiled
  have := h b.b_src_imm; have := h b.b_src_mem; have := h b.is_external_op
  have := h b.store_pc; have := h b.store_mem; have := h b.store_ind
  have := h b.set_pc; have := h b.m32; have := h b.b_src_ind
  have := h b.a_src_reg; have := h b.b_src_reg; have := h b.store_reg
  simp only [packNat]
  omega

/-- **`packFlags` is injective.** The 15-bit ROM flag packing uniquely
    determines its bits — the uniqueness of binary representation, lifted from
    `ℕ` through the bounded `Fin GL_prime` cast. This is what lets the packed
    `flags` slot be unpacked back into individual decode columns. -/
lemma packFlags_inj {b c : RomFlagBits} (h : packFlags b = packFlags c) : b = c := by
  rw [← cast_packNat b, ← cast_packNat c] at h
  have hval := congrArg Fin.val h
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (packNat_lt b),
    Nat.mod_eq_of_lt (packNat_lt c)] at hval
  have toNat_inj : ∀ {x y : Bool}, x.toNat = y.toNat → x = y := by
    intro x y; cases x <;> cases y <;> simp
  have hbd : ∀ x : Bool, x.toNat ≤ 1 := fun x => by cases x <;> simp
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := b
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := c
  simp only [packNat] at hval
  have := hbd a0; have := hbd a1; have := hbd a2; have := hbd a3; have := hbd a4
  have := hbd a5; have := hbd a6; have := hbd a7; have := hbd a8; have := hbd a9
  have := hbd a10; have := hbd a11; have := hbd a12; have := hbd a13; have := hbd a14
  have := hbd d0; have := hbd d1; have := hbd d2; have := hbd d3; have := hbd d4
  have := hbd d5; have := hbd d6; have := hbd d7; have := hbd d8; have := hbd d9
  have := hbd d10; have := hbd d11; have := hbd d12; have := hbd d13; have := hbd d14
  simp only [RomFlagBits.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact toNat_inj (by omega)

/-! ## Bridging component booleanity to the concrete projected row

The component-level booleanity facts are stated as `Expression.eval env (…) = 0`
on the `rowInputVar`; the flag-unpacking lemma needs them as plain `FGL`
equations on the concrete projected row `mainTableRowAtOrZero …`. The bridge is
`Expression.eval`'s commutation with the `ProvableStruct` field projections. It
is proved for an ABSTRACT `var` (so the simp never expands the heavy
`componentWithRomMemAndOpBus` term — the #144 whnf trap) and then instantiated. -/

open ZiskFv.AirsClean.Main (MainRowWithRom)

/-- Per-field commutation of `Expression.eval` with the `core`/`rom` flag
    projections, in `x * (1 - x)` booleanity shape, for an abstract row var. -/
lemma eval_flagBool_bridge (env : Environment FGL)
    (var : Var MainRowWithRom FGL) :
    (Expression.eval env (var.core.is_external_op * (1 - var.core.is_external_op))
        = (eval env var).core.is_external_op * (1 - (eval env var).core.is_external_op))
  ∧ (Expression.eval env (var.core.m32 * (1 - var.core.m32))
        = (eval env var).core.m32 * (1 - (eval env var).core.m32))
  ∧ (Expression.eval env (var.core.set_pc * (1 - var.core.set_pc))
        = (eval env var).core.set_pc * (1 - (eval env var).core.set_pc))
  ∧ (Expression.eval env (var.core.store_pc * (1 - var.core.store_pc))
        = (eval env var).core.store_pc * (1 - (eval env var).core.store_pc))
  ∧ (Expression.eval env (var.rom.a_src_imm * (1 - var.rom.a_src_imm))
        = (eval env var).rom.a_src_imm * (1 - (eval env var).rom.a_src_imm))
  ∧ (Expression.eval env (var.rom.a_src_mem * (1 - var.rom.a_src_mem))
        = (eval env var).rom.a_src_mem * (1 - (eval env var).rom.a_src_mem))
  ∧ (Expression.eval env (var.rom.is_precompiled * (1 - var.rom.is_precompiled))
        = (eval env var).rom.is_precompiled * (1 - (eval env var).rom.is_precompiled))
  ∧ (Expression.eval env (var.rom.b_src_imm * (1 - var.rom.b_src_imm))
        = (eval env var).rom.b_src_imm * (1 - (eval env var).rom.b_src_imm))
  ∧ (Expression.eval env (var.rom.b_src_mem * (1 - var.rom.b_src_mem))
        = (eval env var).rom.b_src_mem * (1 - (eval env var).rom.b_src_mem))
  ∧ (Expression.eval env (var.rom.store_mem * (1 - var.rom.store_mem))
        = (eval env var).rom.store_mem * (1 - (eval env var).rom.store_mem))
  ∧ (Expression.eval env (var.rom.store_ind * (1 - var.rom.store_ind))
        = (eval env var).rom.store_ind * (1 - (eval env var).rom.store_ind))
  ∧ (Expression.eval env (var.rom.b_src_ind * (1 - var.rom.b_src_ind))
        = (eval env var).rom.b_src_ind * (1 - (eval env var).rom.b_src_ind))
  ∧ (Expression.eval env (var.rom.a_src_reg * (1 - var.rom.a_src_reg))
        = (eval env var).rom.a_src_reg * (1 - (eval env var).rom.a_src_reg))
  ∧ (Expression.eval env (var.rom.b_src_reg * (1 - var.rom.b_src_reg))
        = (eval env var).rom.b_src_reg * (1 - (eval env var).rom.b_src_reg))
  ∧ (Expression.eval env (var.rom.store_reg * (1 - var.rom.store_reg))
        = (eval env var).rom.store_reg * (1 - (eval env var).rom.store_reg)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field, circuit_norm, sub_eq_add_neg]

/-- The 15 ROM flag columns of the unified Main row at any in-range trace index
    are boolean, as plain `FGL` equations on the concrete projected row. Combines
    the component-level booleanity (`is_external_op` plus the 14-flag
    `romBoolSpec`) with the projection bridge. -/
theorem mainRow_flags_boolean
    {numInstructions : Nat} (trace : AcceptedZiskTrace numInstructions)
    (idx : Fin trace.mainTable.table.length) :
    let r := mainTableRowAtOrZero trace.program trace.mainTable idx.val
    r.core.is_external_op * (1 - r.core.is_external_op) = 0
  ∧ r.core.m32 * (1 - r.core.m32) = 0
  ∧ r.core.set_pc * (1 - r.core.set_pc) = 0
  ∧ r.core.store_pc * (1 - r.core.store_pc) = 0
  ∧ r.rom.a_src_imm * (1 - r.rom.a_src_imm) = 0
  ∧ r.rom.a_src_mem * (1 - r.rom.a_src_mem) = 0
  ∧ r.rom.is_precompiled * (1 - r.rom.is_precompiled) = 0
  ∧ r.rom.b_src_imm * (1 - r.rom.b_src_imm) = 0
  ∧ r.rom.b_src_mem * (1 - r.rom.b_src_mem) = 0
  ∧ r.rom.store_mem * (1 - r.rom.store_mem) = 0
  ∧ r.rom.store_ind * (1 - r.rom.store_ind) = 0
  ∧ r.rom.b_src_ind * (1 - r.rom.b_src_ind) = 0
  ∧ r.rom.a_src_reg * (1 - r.rom.a_src_reg) = 0
  ∧ r.rom.b_src_reg * (1 - r.rom.b_src_reg) = 0
  ∧ r.rom.store_reg * (1 - r.rom.store_reg) = 0 := by
  intro r
  have h_holds := mainOperationsConstraintsHold_at trace idx
  have h_ieo := ZiskFv.AirsClean.Main.is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints
    numInstructions trace.program _ h_holds
  obtain ⟨h_m32, h_set_pc, h_store_pc, h_a_src_imm, h_a_src_mem, h_is_precompiled,
    h_b_src_imm, h_b_src_mem, h_store_mem, h_store_ind, h_b_src_ind, h_a_src_reg,
    h_b_src_reg, h_store_reg⟩ :=
    ZiskFv.AirsClean.Main.romBoolSpec_of_componentWithRomMemAndOpBus_constraints
      numInstructions trace.program _ h_holds
  obtain ⟨b_ieo, b_m32, b_set_pc, b_store_pc, b_a_src_imm, b_a_src_mem,
    b_is_precompiled, b_b_src_imm, b_b_src_mem, b_store_mem, b_store_ind,
    b_b_src_ind, b_a_src_reg, b_b_src_reg, b_store_reg⟩ :=
    eval_flagBool_bridge (trace.mainTable.environment (trace.mainTable.table.get idx))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus numInstructions trace.program).rowInputVar
  show r.core.is_external_op * _ = 0 ∧ _
  rw [show r = _ from ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
    trace.program trace.mainTable idx]
  exact ⟨b_ieo ▸ h_ieo, b_m32 ▸ h_m32, b_set_pc ▸ h_set_pc, b_store_pc ▸ h_store_pc,
    b_a_src_imm ▸ h_a_src_imm, b_a_src_mem ▸ h_a_src_mem, b_is_precompiled ▸ h_is_precompiled,
    b_b_src_imm ▸ h_b_src_imm, b_b_src_mem ▸ h_b_src_mem, b_store_mem ▸ h_store_mem,
    b_store_ind ▸ h_store_ind, b_b_src_ind ▸ h_b_src_ind, b_a_src_reg ▸ h_a_src_reg,
    b_b_src_reg ▸ h_b_src_reg, b_store_reg ▸ h_store_reg⟩

/-- A boolean-constrained `FGL` value is `boolF` of some `Bool`. -/
private lemma bool_of_booleanity {col : FGL} (h : col * (1 - col) = 0) :
    ∃ d : Bool, col = ZiskFv.AirsClean.boolF d := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨false, by simpa [ZiskFv.AirsClean.boolF] using h0⟩
  · exact ⟨true, by simp only [ZiskFv.AirsClean.boolF_true]; exact (sub_eq_zero.mp h1).symm⟩

/-- **Unpacking the four ADD decode flags from the packed `flags` slot.**

Given that the concrete Main row's packed `romFlags` equals `packFlags bits`
and that the 15 flag columns are boolean, `packFlags` injectivity pins each
column to `boolF` of the corresponding bit. We expose the four columns ADD's
decode needs (`is_external_op`, `m32`, `set_pc`, `store_pc`). -/
theorem romFlagColumns_of_romFlags_eq_packFlags
    (row : MainRowWithRom FGL) (bits : RomFlagBits)
    (hbool :
      row.core.is_external_op * (1 - row.core.is_external_op) = 0
    ∧ row.core.m32 * (1 - row.core.m32) = 0
    ∧ row.core.set_pc * (1 - row.core.set_pc) = 0
    ∧ row.core.store_pc * (1 - row.core.store_pc) = 0
    ∧ row.rom.a_src_imm * (1 - row.rom.a_src_imm) = 0
    ∧ row.rom.a_src_mem * (1 - row.rom.a_src_mem) = 0
    ∧ row.rom.is_precompiled * (1 - row.rom.is_precompiled) = 0
    ∧ row.rom.b_src_imm * (1 - row.rom.b_src_imm) = 0
    ∧ row.rom.b_src_mem * (1 - row.rom.b_src_mem) = 0
    ∧ row.rom.store_mem * (1 - row.rom.store_mem) = 0
    ∧ row.rom.store_ind * (1 - row.rom.store_ind) = 0
    ∧ row.rom.b_src_ind * (1 - row.rom.b_src_ind) = 0
    ∧ row.rom.a_src_reg * (1 - row.rom.a_src_reg) = 0
    ∧ row.rom.b_src_reg * (1 - row.rom.b_src_reg) = 0
    ∧ row.rom.store_reg * (1 - row.rom.store_reg) = 0)
    (h : romFlags row = packFlags bits) :
    row.core.is_external_op = ZiskFv.AirsClean.boolF bits.is_external_op
  ∧ row.core.m32 = ZiskFv.AirsClean.boolF bits.m32
  ∧ row.core.set_pc = ZiskFv.AirsClean.boolF bits.set_pc
  ∧ row.core.store_pc = ZiskFv.AirsClean.boolF bits.store_pc := by
  obtain ⟨hb_ieo, hb_m32, hb_set_pc, hb_store_pc, hb_a_src_imm, hb_a_src_mem,
    hb_is_precompiled, hb_b_src_imm, hb_b_src_mem, hb_store_mem, hb_store_ind,
    hb_b_src_ind, hb_a_src_reg, hb_b_src_reg, hb_store_reg⟩ := hbool
  obtain ⟨d_ieo, e_ieo⟩ := bool_of_booleanity hb_ieo
  obtain ⟨d_m32, e_m32⟩ := bool_of_booleanity hb_m32
  obtain ⟨d_set_pc, e_set_pc⟩ := bool_of_booleanity hb_set_pc
  obtain ⟨d_store_pc, e_store_pc⟩ := bool_of_booleanity hb_store_pc
  obtain ⟨d_a_src_imm, e_a_src_imm⟩ := bool_of_booleanity hb_a_src_imm
  obtain ⟨d_a_src_mem, e_a_src_mem⟩ := bool_of_booleanity hb_a_src_mem
  obtain ⟨d_is_precompiled, e_is_precompiled⟩ := bool_of_booleanity hb_is_precompiled
  obtain ⟨d_b_src_imm, e_b_src_imm⟩ := bool_of_booleanity hb_b_src_imm
  obtain ⟨d_b_src_mem, e_b_src_mem⟩ := bool_of_booleanity hb_b_src_mem
  obtain ⟨d_store_mem, e_store_mem⟩ := bool_of_booleanity hb_store_mem
  obtain ⟨d_store_ind, e_store_ind⟩ := bool_of_booleanity hb_store_ind
  obtain ⟨d_b_src_ind, e_b_src_ind⟩ := bool_of_booleanity hb_b_src_ind
  obtain ⟨d_a_src_reg, e_a_src_reg⟩ := bool_of_booleanity hb_a_src_reg
  obtain ⟨d_b_src_reg, e_b_src_reg⟩ := bool_of_booleanity hb_b_src_reg
  obtain ⟨d_store_reg, e_store_reg⟩ := bool_of_booleanity hb_store_reg
  have hpack : romFlags row =
      packFlags ⟨d_a_src_imm, d_a_src_mem, d_is_precompiled, d_b_src_imm,
        d_b_src_mem, d_ieo, d_store_pc, d_store_mem, d_store_ind, d_set_pc,
        d_m32, d_b_src_ind, d_a_src_reg, d_b_src_reg, d_store_reg⟩ := by
    simp only [romFlags, packFlags, e_ieo, e_m32, e_set_pc, e_store_pc,
      e_a_src_imm, e_a_src_mem, e_is_precompiled, e_b_src_imm, e_b_src_mem,
      e_store_mem, e_store_ind, e_b_src_ind, e_a_src_reg, e_b_src_reg, e_store_reg]
  have hbits := packFlags_inj (hpack.symm.trans h)
  subst hbits
  exact ⟨e_ieo, e_m32, e_set_pc, e_store_pc⟩

/-! ## ADD pilot: reconstruct `Decode_add` from the committed program

`Decode_add_of_program` rebuilds the `Decode_add` decode pins from
`trace.constraints_hold` (the in-circuit ROM lookup) plus *program-level* decode
facts about the committed instruction bound to the row's `pc` — rather than
assuming the witness row's columns directly.

Accounting (which pins are now program-derived):
* `h_main_op`, `h_jmp1`, `h_jmp2` — DERIVED from the dedicated ROM-message slots
  (`op`, `jmp_offset1`, `jmp_offset2`) via the binding lemma + the program-level
  facts `(program entry at pc i).op = OP_ADD`, `… .jmp_offset1 = 4`,
  `… .jmp_offset2 = 4`.
* `h_main_active`, `h_m32`, `h_set_pc`, `h_store_pc` — DERIVED from the packed
  `flags` slot: the binding gives `romFlags row = (program entry).flags`, the
  program-level fact pins `(program entry).flags = packFlags bits`, and
  `packFlags` injectivity (with in-circuit flag booleanity) unpacks the four
  columns. The four ADD bit values are themselves program-level premises
  (`bits.is_external_op = true`, `bits.m32 = false`, …).
* `h_idx` — a structural next-row bound, unchanged (already a structural premise
  on `Decode_add`, not a decode-column fact).

The program-level decode premise is quantified over ALL program entries at the
row's committed line, so the membership witness discharges it without needing
program-line distinctness (see the R1 note above).

This MOVES decode trust from "the witness row's `op`/flag columns decode as ADD"
to "the committed program's instruction at `pc i` decodes as ADD" — a #61 step.
It does NOT yet tie `trace.program` to a raw instruction word's lowering (that is
block 2/3). -/
def Decode_add_of_program
    {numInstructions : Nat}
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (c : Claim_add trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h_bits_ieo : bits.is_external_op = true)
    (h_bits_m32 : bits.m32 = false)
    (h_bits_set_pc : bits.set_pc = false)
    (h_bits_store_pc : bits.store_pc = false)
    (h_prog : ∀ j : Fin numInstructions,
        (trace.program j).line
            = (mainOfTable trace.program trace.mainTable).pc i.val →
          (trace.program j).op = ZiskFv.Trusted.OP_ADD
        ∧ (trace.program j).jmp_offset1 = 4
        ∧ (trace.program j).jmp_offset2 = 4
        ∧ (trace.program j).flags = packFlags bits) :
    Decode_add trace i c := by
  have h_lt : i.val < trace.mainTable.table.length := trace.mainTable_index i
  -- The seven decode-column pins, proved in a `Prop` context (so the binding
  -- existential may be eliminated), then assembled into the `Type`-valued
  -- `Decode_add` below.
  have key :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_ADD
    ∧ (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1
    ∧ (mainOfTable trace.program trace.mainTable).m32 i.val = 0
    ∧ (mainOfTable trace.program trace.mainTable).store_pc i.val = 0
    ∧ (mainOfTable trace.program trace.mainTable).set_pc i.val = 0
    ∧ (mainOfTable trace.program trace.mainTable).jmp_offset1 i.val = 4
    ∧ (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4 := by
    obtain ⟨j, hline, hop, hjmp1, hjmp2, hflags⟩ :=
      mainDecodeColumns_at_eq_program trace ⟨i.val, h_lt⟩
    obtain ⟨hpo, hpj1, hpj2, hpf⟩ := h_prog j hline
    have hrom : romFlags (mainTableRowAtOrZero trace.program trace.mainTable i.val)
        = packFlags bits := hflags.symm.trans hpf
    obtain ⟨p_ieo, p_m32, p_set_pc, p_store_pc⟩ :=
      romFlagColumns_of_romFlags_eq_packFlags
        (mainTableRowAtOrZero trace.program trace.mainTable i.val) bits
        (mainRow_flags_boolean trace ⟨i.val, h_lt⟩) hrom
    refine ⟨hop.symm.trans hpo, ?_, ?_, ?_, ?_,
      hjmp1.symm.trans hpj1, hjmp2.symm.trans hpj2⟩
    · simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable_is_external_op]
      rw [p_ieo, h_bits_ieo, ZiskFv.AirsClean.boolF_true]
    · simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable_m32]
      rw [p_m32, h_bits_m32, ZiskFv.AirsClean.boolF_false]
    · simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable_store_pc]
      rw [p_store_pc, h_bits_store_pc, ZiskFv.AirsClean.boolF_false]
    · simp only [ZiskFv.AirsClean.FullEnsemble.mainOfTable_set_pc]
      rw [p_set_pc, h_bits_set_pc, ZiskFv.AirsClean.boolF_false]
  exact
    { h_main_op := key.1
      h_main_active := key.2.1
      h_m32 := key.2.2.1
      h_store_pc := key.2.2.2.1
      h_idx := h_idx
      h_set_pc := key.2.2.2.2.1
      h_jmp1 := key.2.2.2.2.2.1
      h_jmp2 := key.2.2.2.2.2.2 }

end ZiskFv.Compliance.RomDecodeBinding
