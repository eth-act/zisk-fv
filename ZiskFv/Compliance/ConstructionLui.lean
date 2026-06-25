import ZiskFv.Compliance.OpBusProviderMatch
import ZiskFv.Compliance.SailTrace
import ZiskFv.Compliance.Wrappers.Lui

/-!
# Sound LUI construction (`construction_lui_sound`)

The first **provider-free** (`is_external_op = 0`) honest sound construction in
the P4 sweep. LUI is realized by a single *internal* Zisk microinstruction
(`OP_COPYB`), so it emits **no** operation-bus entry: there is no op-bus provider
block at all (in contrast to `ConstructionSub.lean`, which derives the staticBinary
op-bus provider match from `trace.channels_balanced`). LUI is therefore STRICTLY MORE
derivable than the 28 provider-backed families — the entire LUI Main constraint
subset comes straight out of the per-row `Main.Spec`, and the rd-value is the
identity copy `c_0/c_1 = b_0/b_1 = imm`.

## The honest decomposition

* **(a) derived** — proven inside the body, NOT a binder:
  - the Main per-row `Spec` and from it the full LUI constraint subset
    (`lui_subset_holds`, including the `pc_handshake_with_next_pc` field, which
    is *definitional* — `next_pc` is chosen as the handshake RHS, so the field
    holds by `rfl` and contributes no residual),
  - the `StorePcMemoryWitness` (`row_eq` by `rowAt_mainOfTable`, `rd_write_match`
    by `matches_memory_entry_refl` off the real Clean Main `cMemMessage` row),
  - the rd-write memory-bus shape (`rd_mult`, `rd_as` by `rfl`),
  - the pure-spec `nextPC_eq` (`rfl`, since `nextPC_val` is chosen to be the
    pure-spec nextPC),
  - the circuit-internal rd arithmetic (`c_0/c_1 = b_0/b_1 = imm`), discharged
    inside `equiv_LUI` from `internal_op1_copies_*` + the imm-lane Nat pins.

* **(b) named residual** — explicit top-level binders (program/ROM/Sail facts):
  - decode pins (5): `h_main_op` (`OP_COPYB`), `h_main_active` (`= 0`),
    `h_m32` (`= 0`), `h_set_pc` (`= 0`), `h_store_pc` (`= 0`)
  - Sail-value bridges (6): `h_input_imm`, `h_input_rd`, `h_input_pc`,
    `h_rd_idx`, `h_imm_lo_nat`, `h_imm_hi_nat`
  - control-flow next-PC (1): `h_nextPC_matches` — the ORDINARY sequential
    `pc + 4` handshake every one of the 28 already carries; NOT the cross-row
    jump-target term.

* **(c) artifact** — pure `bus_effect`/`ExecutionBusEntry` bookkeeping:
  - exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the genuine
    `execRow : List (ExecutionBusEntry FGL)` ∀-binder.

## Residual budget: EXACTLY 15 + execRow

`5 + 6 + 1 + 3 = 15` hypothesis binders, plus the genuine `execRow` ∀-binder.
No `MainRowProvenance` / `*RowBinding` leaf appears anywhere in the binder set.

## Axioms

`construction_lui_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.EquivCore.Promises
open Interaction

set_option maxHeartbeats 2000000

/-- The honest unified Main+ROM row at trace index `i`, drawn from the real Main
    table.  Its `.core` equals `rowAt (mainOfTable …) i`. -/
@[reducible]
noncomputable def mainRowWithRomLui
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) :
    ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    trace.program trace.mainTable i.val

/-- Construction-chosen rd-write entry: the real Clean Main `c` memory-bus
    emission (rd write) of the honest unified row.  The `StorePcMemoryWitness`
    match is then `matches_memory_entry_refl`. -/
@[reducible]
noncomputable def eRdLui
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomLui trace binding i)) 1 1

/-- The Main per-row `Spec` at trace index `i`, derived from `trace.spec_holds`.
    (Standalone version of the in-wrapper `h_main_spec` derivation.) -/
theorem mainSpec_at
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions) :
    ZiskFv.AirsClean.Main.Spec
      (ZiskFv.AirsClean.Main.rowAt
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
        i.val) := by
  let mainIdx : Fin trace.mainTable.table.length := ⟨i.val, trace.mainTable_index i⟩
  let mainRow := trace.mainTable.table.get mainIdx
  have h_mainRow_mem : mainRow ∈ trace.mainTable.table := by simp [mainRow]
  have h_main_component_spec :
      trace.mainTable.component.Spec
        (trace.mainTable.environment (trace.mainTable.table.get mainIdx)) := by
    simpa [mainRow] using
      trace.spec_holds trace.mainTable trace.mainTable_mem mainRow h_mainRow_mem
  simpa [mainIdx] using
    ZiskFv.AirsClean.FullEnsemble.mainSpec_rowAt_mainOfTable_of_component_spec
      trace.program trace.mainTable mainIdx trace.mainTable_component
      h_main_component_spec

/-- Sound LUI construction: from the accepted trace + honest residual binders,
    conclude the canonical
    `(writeReg nextPC (pc+4); execute (UTYPE LUI)) = (bus_effect …).2`.

    Honest top-level residual binders (the validated 15 + `execRow` budget):
    * (b) decode pins (5): `h_main_op`, `h_main_active`, `h_m32`, `h_set_pc`,
      `h_store_pc`
    * (b) Sail-value bridges (6): `h_input_imm`, `h_input_rd`, `h_input_pc`,
      `h_rd_idx`, `h_imm_lo_nat`, `h_imm_hi_nat`
    * (b) next-PC (1): `h_nextPC_matches` (ordinary sequential `pc+4` handshake)
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): the Main per-row `Spec` and the full
    LUI constraint subset, the `StorePcMemoryWitness`, the rd-write MemBus shape,
    the pure-spec `nextPC_eq`, and the circuit-internal rd arithmetic. -/
theorem construction_lui_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20)
    (rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_COPYB)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 0)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_set_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail-value bridges
    (h_input_imm : lui_input.imm = imm)
    (h_input_rd : lui_input.rd = regidx_to_fin rd)
    (h_input_pc : (binding i).regs.get? Register.PC = .some lui_input.PC)
    (h_imm_lo_nat :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
        = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
        = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : execRow.length = 2)
    (h_e0_mult : execRow[0]!.multiplicity = -1)
    (h_e1_mult : execRow[1]!.multiplicity = 1)
    -- (b) next-PC residual (ordinary sequential pc+4 handshake)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
        = (PureSpec.execute_LUI_pure lui_input).nextPC)
    -- (b) rd-write entry ↔ register-index alignment
    (h_rd_idx :
      lui_input.rd =
        Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.LUI)) (binding i)
      = (bus_effect execRow [eRdLui trace binding i] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the LUI Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, h_b0, _h_c1, h_b1, _h_set_flag, h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_lui_subset :
      ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_b0, h_b1, h_clear_flag, h_handshake⟩
  -- (a) assemble `h_circuit` from FLAT top-level facts.
  have h_circuit :
      ZiskFv.Tactics.UTypeArchetype.lui_archetype_circuit_holds m i.val next_pc :=
    ZiskFv.EquivCore.Promises.lui_h_circuit_of_main_constraints
      m i.val next_pc h_main_active h_main_op h_m32 h_set_pc h_store_pc
      h_lui_subset
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  -- (a) the rd-write MemBus shape (`rd_mult`, `rd_as`) is `rfl`; the pure-spec
  -- `nextPC_eq` is `rfl` since `nextPC_val` is the pure-spec nextPC.
  let promises : ZiskFv.EquivCore.Promises.UTypePromises
      state lui_input.imm lui_input.rd lui_input.PC
      (PureSpec.execute_LUI_pure lui_input).nextPC
      imm rd execRow e_rd (PureSpec.execute_LUI_pure lui_input).nextPC :=
    { input_imm_eq := h_input_imm
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      nextPC_eq := rfl
      rd_idx := h_rd_idx }
  exact ZiskFv.EquivCore.Lui.equiv_LUI state lui_input imm rd
    m i.val next_pc execRow e_rd store_pc_mem
    (PureSpec.execute_LUI_pure lui_input).nextPC
    promises h_imm_lo_nat h_imm_hi_nat h_circuit

end ZiskFv.Compliance
