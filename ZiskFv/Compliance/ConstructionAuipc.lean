import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.Wrappers.Auipc

/-!
# Sound AUIPC construction (`construction_auipc_sound`)

The second **provider-free** (`is_external_op = 0`) honest sound construction in
the P4 sweep — the AUIPC clone of `ConstructionLui.construction_lui_sound`.
AUIPC is realized by a single *internal* `OP_FLAG` microinstruction with
`store_pc = 1`: it emits **no** operation-bus entry, so there is no op-bus
provider block. The rd-value is `pc + signExtend(imm << 12)`, derived inside
`equiv_AUIPC` from the `internal_op0_*` constraints + the PC/offset bridges.

## The honest decomposition

* **(a) derived** — proven inside the body, NOT a binder:
  - the Main per-row `Spec` and from it the full AUIPC constraint subset
    (`auipc_subset_holds`, including the *definitional* `pc_handshake_with_next_pc`
    field — `next_pc` is chosen as the handshake RHS, so it holds by `rfl`),
  - the `StorePcMemoryWitness` (`row_eq` by `rowAt_mainOfTable`, `rd_write_match`
    by `matches_memory_entry_refl` off the real Clean Main `cMemMessage` row),
  - the rd-write memory-bus shape (`rd_mult`, `rd_as` by `rfl`),
  - the pure-spec `nextPC_eq` (`rfl`),
  - the circuit-internal rd arithmetic (`pc + imm`), discharged inside
    `equiv_AUIPC` from `internal_op0_*` + the PC/offset bridges + the range pins.

* **(b) named residual** — explicit top-level binders (program/ROM/Sail facts):
  - decode pins (5): `h_main_op` (`OP_FLAG`), `h_main_active` (`= 0`),
    `h_m32` (`= 0`), `h_set_pc` (`= 0`), `h_store_pc` (`= 1`)
  - Sail-value bridges (5): `h_input_imm`, `h_input_rd`, `h_input_pc`,
    `h_rd_idx`, plus the intra-row current-PC bridge `h_pc_bridge`
    (the `m.pc` r_main column ⟷ Sail PC — a bucket-(b) Sail-value bridge,
    NOT the cross-row #100 term) and the offset bridge `h_offset_bridge`
  - control-flow next-PC (1): `h_nextPC_matches` — the ORDINARY sequential
    `pc + 4` handshake every one of the 28 already carries.
  - RANGE pins (2): `h_no_wrap`, `h_pc_offset_lt_2_32`.

* **(c) artifact** — pure `bus_effect`/`ExecutionBusEntry` bookkeeping:
  - exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the genuine
    `execRow : List (ExecutionBusEntry FGL)` ∀-binder.

## Residual budget: EXACTLY 18 + execRow

`5 + 6 + 1 + 3 + 2 + 1 = 18` hypothesis binders (the LUI 15, minus the two
imm-lane Nat pins, plus `h_offset_bridge` + `h_pc_bridge` + the two RANGE pins),
plus the genuine `execRow` ∀-binder. No `MainRowProvenance` / `*RowBinding` leaf
appears anywhere.

## Axioms

`construction_auipc_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.EquivCore.Promises
open Interaction

set_option maxHeartbeats 2000000

/-- Sound AUIPC construction: from the accepted trace + honest residual binders,
    conclude the canonical bare `execute (UTYPE AUIPC) = (bus_effect …).2`.

    Honest top-level residual binders (the validated 18 + `execRow` budget):
    * (b) decode pins (5): `h_main_op`, `h_main_active`, `h_m32`, `h_set_pc`,
      `h_store_pc`
    * (b) Sail-value bridges (6): `h_input_imm`, `h_input_rd`, `h_input_pc`,
      `h_rd_idx`, `h_offset_bridge`, `h_pc_bridge`
    * (b) next-PC (1): `h_nextPC_matches` (ordinary sequential `pc+4` handshake)
    * (b) RANGE (2): `h_no_wrap`, `h_pc_offset_lt_2_32`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): the Main per-row `Spec` and the full
    AUIPC constraint subset, the `StorePcMemoryWitness`, the rd-write MemBus
    shape, the pure-spec `nextPC_eq`, and the circuit-internal rd arithmetic. -/
theorem construction_auipc_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_FLAG)
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
        i.val = 1)
    -- (b) Sail-value bridges
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : (binding i).regs.get? Register.PC = .some auipc_input.PC)
    (h_offset_bridge :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset2
          i.val).val
        = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_pc_bridge :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
        = auipc_input.PC.toNat)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : execRow.length = 2)
    (h_e0_mult : execRow[0]!.multiplicity = -1)
    (h_e1_mult : execRow[1]!.multiplicity = 1)
    -- (b) next-PC residual (ordinary sequential pc+4 handshake)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
        = (PureSpec.execute_AUIPC_pure auipc_input).nextPC)
    -- (b) rd-write entry ↔ register-index alignment
    (h_rd_idx :
      auipc_input.rd =
        Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr)
    -- (b) RANGE pins
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) (binding i)
      = (bus_effect execRow [eRdLui trace binding i] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the AUIPC Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨h_c0, _h_b0, h_c1, _h_b1, h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_auipc_subset :
      ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0, h_c1, h_set_flag, h_handshake⟩
  -- (a) assemble `h_circuit` from FLAT top-level facts.
  have h_circuit :
      ZiskFv.Tactics.UTypeArchetype.auipc_archetype_circuit_holds m i.val next_pc :=
    ZiskFv.EquivCore.Promises.auipc_h_circuit_of_main_constraints
      m i.val next_pc h_main_active h_main_op h_m32 h_set_pc h_store_pc
      h_auipc_subset
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  -- (a) the rd-write MemBus shape (`rd_mult`, `rd_as`) is `rfl`; the pure-spec
  -- `nextPC_eq` is `rfl` since `nextPC_val` is the pure-spec nextPC.
  let promises : ZiskFv.EquivCore.Promises.UTypePromises
      state auipc_input.imm auipc_input.rd auipc_input.PC
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC
      imm rd execRow e_rd (PureSpec.execute_AUIPC_pure auipc_input).nextPC :=
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
  exact ZiskFv.EquivCore.Auipc.equiv_AUIPC state auipc_input imm rd
    execRow e_rd m i.val next_pc store_pc_mem
    (PureSpec.execute_AUIPC_pure auipc_input).nextPC
    promises h_circuit h_offset_bridge h_pc_bridge h_no_wrap h_pc_offset_lt_2_32

end ZiskFv.Compliance
