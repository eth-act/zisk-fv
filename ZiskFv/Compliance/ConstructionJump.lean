import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.Wrappers.Jal
import ZiskFv.Compliance.Wrappers.Jalr

/-!
# Sound jump constructions (`construction_jal_sound`, `construction_jalr_sound`)

The two RV64 unconditional/computed-jump envelopes of the P4 endgame, taking the
construction set 53 → 55. Each assembles the canonical jump conclusion from an
accepted full-ensemble trace plus an explicit, named, top-level set of residual
binders.

## Why jumps differ from branches

Branches (`ConstructionBranch.lean`) emit no memory bus and need no Main-row
pins. Jumps WRITE the link register `rd ← pc + 4`, so they emit an rd-write
memory-bus entry (`as = 1`, register space) and DO consume Main-row mode pins.
The construction mirrors `construction_auipc_sound` (also an internal store-PC
Main row): the rd-write entry is the Main row's OWN `cMemMessage` emission
(`eRdLui` / `StorePcMemoryWitness` discharged by `matches_memory_entry_refl`),
so there is no balance derivation against a separate provider.

* **JAL** is an internal `OP_FLAG` row (`is_external_op = 0`, `set_pc = 0`,
  `store_pc = 1`). Its `jump_subset_holds` (which forces `c = 0, flag = 1`,
  giving `next_pc = pc + jmp_offset1 = pc + imm`) is DERIVED inside the body from
  the per-row `Main.Spec` (`add_subset_holds`). The construction dispatches to
  `equiv_JAL_of_main_pins`.
* **JALR** is an external `OP_AND` row (`is_external_op = 1`, `set_pc = 1`,
  `store_pc = 1`). The target is COMPUTED `(rs1 + imm) & ~1`; the canonical
  `equiv_JALR` derives the link value `pc + 4` from circuit witnesses. The
  4-conjunct `jalr_subset` (flag/ext booleans + disjoint + handshake) is DERIVED
  from `add_subset_holds`. The construction dispatches to the Compliance wrapper
  `equiv_JALR`.

## The control-flow next-PC residual (#100)

Both jumps carry the next-PC obligation as the named residual
`JumpPromises.nextPC_matches` (inside the `promises` bundle): the circuit's
exec-bus PC field (`exec_row[1]!.pc`) equals `nextPC_val`, the jump target. This
is the SAME `h_nextPC_matches`-shaped #100 cross-row obligation every prior
construction carries — for JAL the target is the unconditional `pc + imm`, for
JALR the computed `(rs1 + imm) & ~1`. It is GENUINELY IRREDUCIBLE: the circuit's
next-row PC linkage is a cross-row fact not pinned by the local row.

The intra-row PC/target bridges (`h_pc_bridge` / `h_link_bridge`) are
bucket-(b) Sail-value bridges (the `m.pc` column ⟷ Sail PC), NOT the cross-row
#100 term.

## Axioms

Both constructions introduce **0 PROJECT (`ZiskFv.*`) axioms**. Their closure
includes the Sail-translation axioms (JALR's closure also includes the trusted
`execute_JALR_pure_equiv_axiom`, per `trusted-base.md`) and the Lean-kernel
postulates as documented external trust.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.EquivCore.Promises
open Interaction

set_option maxHeartbeats 2000000

/-- Sound JAL construction (unconditional `pc + imm` target). Mirrors
    `construction_auipc_sound`: the rd-write entry is the Main row's own
    `cMemMessage` emission (`eRdLui`), and `jump_subset_holds` is derived from
    the per-row `Main.Spec`. Dispatches to `equiv_JAL_of_main_pins`.

    Honest top-level residual binders:
    * (b) decode pins (5): `h_main_op` (`OP_FLAG`), `h_main_active` (`= 0`),
      `h_m32` (`= 0`), `h_set_pc` (`= 0`), `h_store_pc` (`= 1`)
    * (b) jump-target pin (1): `h_jmp2` (`jmp_offset2 = 4`, the link offset)
    * (b) Sail/PC bridges (1): `h_pc_bridge` (`m.pc` column ⟷ Sail PC — intra-row)
    * (b) JumpPromises fields (Sail reads + exec shape + the #100 cross-row
      next-PC `nextPC_matches` + rd alignment) carried in the bundle
    * (b) JAL-specific (2): `h_input_imm`, `h_not_throws`
    * (b) RANGE pins (2): `h_pc_bound`, `h_pc_offset_lt_2_32`
    * (c) exec artifacts: the `execRow` ∀-binder + its shape fields. -/
theorem construction_jal_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (nextPC_val : BitVec 64)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_FLAG)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 0)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_set_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 1)
    -- (b) jump-target pin
    (h_jmp2 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
        i.val = 4)
    -- (b) intra-row PC bridge
    (h_pc_bridge :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).pc i.val).val
        = jal_input.PC.toNat)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : execRow.length = 2)
    (h_e0_mult : execRow[0]!.multiplicity = -1)
    (h_e1_mult : execRow[1]!.multiplicity = 1)
    -- (b) control-flow next-PC residual (#100 cross-row obligation)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
        = nextPC_val)
    -- (b) Sail-value bridges + bundle facts
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option : (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr)
    -- (b) JAL-specific
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    -- (b) RANGE pins
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    execute_instruction (instruction.JAL (imm, rd)) (binding.stateAt i)
      = (bus_effect execRow [eRdLui trace binding i] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the JAL Main constraint subset.
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
  have h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0, h_c1, h_set_flag, h_handshake⟩
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_FLAG :=
    ⟨h_main_active, h_main_op⟩
  -- promises bundle: Sail reads + exec artifacts + the #100 nextPC residual.
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state jal_input.PC jal_input.rd misa_val
      (PureSpec.execute_JAL_pure jal_input).success
      (PureSpec.execute_JAL_pure jal_input).nextPC
      rd execRow e_rd nextPC_val :=
    { input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      success := h_success
      nextPC_option := h_nextPC_option
      rd_idx := h_rd_idx }
  exact ZiskFv.Compliance.equiv_JAL_of_main_pins
    state jal_input imm rd misa_val m i.val next_pc execRow e_rd nextPC_val
    store_pc_mem pins h_m32 h_set_pc h_store_pc h_jal_subset h_jmp2 h_pc_bridge
    promises h_input_imm h_not_throws h_pc_bound h_pc_offset_lt_2_32

/-- Sound JALR construction (computed `(rs1 + imm) & ~1` target). The Main row is
    an external `OP_AND` store-PC row; the 4-conjunct `jalr_subset` is derived
    from the per-row `Main.Spec`, and the rd-write entry is the Main row's own
    `cMemMessage` emission. Dispatches to the Compliance wrapper `equiv_JALR`.

    Honest top-level residual binders:
    * (b) decode pins (6): `h_main_op` (`OP_AND`), `h_main_active` (`= 1`),
      `h_flag` (`= 0`), `h_m32` (`= 0`), `h_set_pc` (`= 1`), `h_store_pc` (`= 1`)
    * (b) Sail reads (4): `h_input_rs1`, `h_cur_privilege`, `h_mseccfg`,
      `h_input_imm`
    * (b) link bridge (1): `h_link_bridge` (`m.pc + jmp_offset2` ⟷ `PC + 4`)
    * (b) JumpPromises fields (Sail reads + exec shape + the #100 cross-row
      next-PC `nextPC_matches` + rd alignment) carried in the bundle
    * (b) RANGE pins (2): `h_pc_bound`, `h_pc_offset_lt_2_32`
    * (c) exec artifacts: the `execRow` ∀-binder + its shape fields. -/
theorem construction_jalr_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (nextPC_val : BitVec 64)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_AND)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_flag :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).flag
        i.val = 0)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_set_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).set_pc
        i.val = 1)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 1)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : execRow.length = 2)
    (h_e0_mult : execRow[0]!.multiplicity = -1)
    (h_e1_mult : execRow[1]!.multiplicity = 1)
    -- (b) control-flow next-PC residual (#100 cross-row obligation)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (execRow[1]!.pc).val))
        = nextPC_val)
    -- (b) Sail-value bridges + bundle facts
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : (binding.stateAt i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option : (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx (eRdLui trace binding i).ptr)
    -- (b) Sail reads
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) (binding.stateAt i)
      = EStateM.Result.ok jalr_input.rs1_val (binding.stateAt i))
    (h_cur_privilege : Sail.readReg Register.cur_privilege (binding.stateAt i)
      = EStateM.Result.ok Privilege.Machine (binding.stateAt i))
    (h_mseccfg : Sail.readReg Register.mseccfg (binding.stateAt i)
      = EStateM.Result.ok mseccfg (binding.stateAt i))
    -- (b) link bridge (computed target)
    (h_link_bridge :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).pc i.val
        + (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).jmp_offset2
            i.val).val
        = (jalr_input.PC + 4#64).toNat)
    -- (b) RANGE pins
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) (binding.stateAt i)
      = (bus_effect execRow [eRdLui trace binding i] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let e_rd := eRdLui trace binding i
  -- (a) Main per-row Spec ⇒ the JALR Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, _h_b0, _h_c1, _h_b1, _h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m i.val
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m i.val
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m i.val
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_handshake⟩
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace binding i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace binding i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨h_main_active, h_main_op⟩
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state jalr_input.PC jalr_input.rd misa_val
      (PureSpec.execute_JALR_pure jalr_input).success
      (PureSpec.execute_JALR_pure jalr_input).nextPC
      rd execRow e_rd nextPC_val :=
    { input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      rd_mult := by rfl
      rd_as := by rfl
      success := h_success
      nextPC_option := h_nextPC_option
      rd_idx := h_rd_idx }
  exact ZiskFv.Compliance.equiv_JALR
    state jalr_input imm rs1 rd misa_val mseccfg execRow e_rd nextPC_val
    m i.val next_pc store_pc_mem pins h_flag h_m32 h_set_pc h_store_pc
    h_jalr_subset promises h_input_imm h_input_rs1 h_cur_privilege h_mseccfg
    h_link_bridge h_pc_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
