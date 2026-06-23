import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.Wrappers.Andi
import ZiskFv.Compliance.Wrappers.Ori
import ZiskFv.Compliance.Wrappers.Xori
import ZiskFv.Compliance.Wrappers.Slti
import ZiskFv.Compliance.Wrappers.Sltiu

/-!
# Sound I-type constructions (ANDI, ORI, XORI, SLTI, SLTIU)

The P4 SWEEP Wave 2 (PLAN_ENDGAME_P4_SWEEP.md PR3). Each construction is the
mechanical mirror of its R-type sibling
(`construction_and_sound` / `construction_or_sound` / `construction_xor_sound`
in `ConstructionAnd.lean` / `ConstructionLogic.lean`; `construction_slt_sound` /
`construction_sltu_sound` in `ConstructionCompare.lean`) through the **uniform
I-type immediate DELTA** described below. They assemble the canonical conclusion
(`execute (ITYPE …I) = (bus_effect …).2`) from an accepted full-ensemble trace
plus an explicit, named, top-level set of residual binders — with **no**
`*RowBinding` / `MainRowProvenance` record carrying any fact.

## The uniform I-type immediate DELTA

The second operand is NOT a register read; it is an immediate sourced from the
program binding. So relative to the R-type sibling each construction:

* **drops** the second-register Sail read `h_input_r2` and the two `b`-lane
  bridges `h_b_lo_t` / `h_b_hi_t` (no `xreg(rs2)` lane pin),
* **adds** the immediate binder `imm : BitVec 12` and the immediate-routing
  *constructibility-bundle* pin `itype_imm_subset_holds_main m i.val imm` as a
  NAMED top-level binder (`h_<op>_subset`) — a bucket-(b) program/decode residual
  (a `ProgramBinding` decode artifact), NEVER derived from Main
  constraints/balance and NEVER hidden in a record (SPINE §8 CRITICAL REPORTING
  RULE),
* **swaps** `RTypePromises → ITypePromises` (which carries
  `input_imm_eq : input_imm = imm` in place of the R-type r2 read), and
* **routes** the final call through `equiv_<OP>I`.

The op-bus provider match is operand-source-agnostic, so the SAME salvaged
Layer-A wrapper as the R-type sibling is reused verbatim
(`exists_staticBinary_provider_row_matches_logic_from_binding` for ANDI/ORI/XORI,
`exists_staticBinary_provider_row_matches_compare_from_binding` for SLTI/SLTIU,
with the SAME op-pin disjunct shape). The op-agnostic infra `busSub` /
`mainRowWithRomSub` (`ConstructionSub.lean`) and the lane-rd / row-shape / MemBus
derivations are reused verbatim.

The 8-byte Binary-row immediate form `h_input_imm_row`
(`BitVec.signExtend 64 imm = binaryRowB64 row`) that the logic wrappers
(`equiv_ANDI` / `equiv_ORI` / `equiv_XORI`) consume is DERIVED inside the body via
`Bridge.Binary.itype_imm_subset_binary_row_of_main_row` from the named
`h_<op>_subset` pin + the in-body `h_matches` + `h_m32` + the provider match
(NOT a binder). The compare wrappers (`equiv_SLTI` / `equiv_SLTIU`) re-derive that
8-byte form internally and instead take the Main-form `h_<op>_subset` plus the
`m32 = 0` pin directly, so no `h_input_imm_row` is passed.

## Residual budget (per family): 16 + `imm` + `execRow`

R-type sibling 17 binders, minus `h_input_r2` (−1), minus `h_b_lo_t`/`h_b_hi_t`
(−2), plus `h_<op>_subset` (+1) and the immediate-decode equality
`h_input_imm : input.imm = imm` (+1) = 16 hypothesis binders, plus the immediate
value binder `imm : BitVec 12`, plus the genuine `execRow` ∀-binder.
(`h_input_imm_row`, the 8-byte Binary-row form, is DERIVED, not a binder, for
every family.) No `MainRowProvenance` / `*RowBinding` leaf anywhere in any binder
set.

## Per-op DELTA from the R-type sibling

* **ANDI / ORI** (logic, `OP_AND = 14` / `OP_OR = 15`, both `< 16`): mirror
  `construction_and_sound` / `construction_or_sound` exactly (same `_op_lt_16` +
  `_64` data-effect route); the only change is the immediate DELTA + `equiv_ANDI` /
  `equiv_ORI`.
* **XORI** (logic, `OP_XOR = 16 ≥ 16`): inherits XOR's wrinkle — its body reuses
  `construction_xor_sound`'s op=16 route (`static_table_logic_mode_pins_of_emit` +
  `byte_chain_discharge_logic_of_static_row`), NOT the `_op_lt_16` + `_64` pair,
  plus the immediate DELTA + `equiv_XORI`.
* **SLTI / SLTIU** (compare, `OP_LT = 7` / `OP_LTU = 6`, both `< 16`): mirror
  `construction_slt_sound` / `construction_sltu_sound` (same `_op_lt_16` + `_64`
  route for the in-body `h_matches`; the signed/unsigned compare polarity lives
  inside the wrappers), plus the immediate DELTA. The compare wrappers consume the
  Main-form `h_<op>_subset` + `m32 = 0` directly (no `h_input_imm_row`).

## Anti-vacuity (PLAN §4.9)

`execRow` is a genuine top-level ∀-binder in EVERY family; the bus consumed by the
exec hypotheses is built from the real trace row (`busSub`), NOT chosen to
trivialize a hypothesis — exactly as in SUB/AND.

## Axioms

Every construction introduces **0 PROJECT (`ZiskFv.*`) axioms**. As with every
canonical theorem in this project, their closure still includes the
Sail-translation axioms and the Lean-kernel postulates as documented external
trust.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises
open ZiskFv.Tactics.ALUITypeArchetype

set_option maxHeartbeats 2000000

/-- Sound ANDI construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (ITYPE ANDI) = (bus_effect …).2`.

    Honest top-level residual binders (the §2 logic budget + the I-type immediate
    DELTA, 16 + `imm` + `execRow`):
    * (b) decode pins (4): `h_main_op` (= `OP_AND`), `h_main_active`, `h_m32`,
      `h_store_pc`
    * (b) Sail read + operands (5): `h_input_r1`, `h_input_imm`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) r1 lane bridges (2): `h_a_lo_t`, `h_a_hi_t`
    * (b) immediate-routing pin (1): `h_andi_subset`
      (`itype_imm_subset_holds_main`)
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.channels_balanced`, via the salvaged logic wrapper), row shape, the 8-byte
    immediate form `h_input_imm_row` (from `h_andi_subset` + `h_matches`),
    circuit-internal rd arithmetic, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the r1 lane→Sail binding fact. -/
theorem construction_andi_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (andi_input : PureSpec.AndiInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_AND)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail read + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok andi_input.r1_val (binding.stateAt i))
    (h_input_imm : andi_input.imm = imm)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some andi_input.PC)
    (h_input_rd : andi_input.rd = regidx_to_fin rd)
    -- (b) r1 lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    -- (b) immediate-routing pin (NAMED top-level binder, program/decode residual)
    (h_andi_subset : itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val andi_input.imm)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC)
    (h_rd_idx :
      andi_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ANDI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced` via the salvaged
  -- logic wrapper (serves AND/ANDI / OR/ORI / XOR/XORI; op pin = AND disjunct).
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_main_active (Or.inl h_main_op)
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨h_main_active, h_main_op⟩
  -- (a) lane-rd, derived from store_pc = 0 (no record consumed)
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  -- promises bundle: Sail read + immediate + exec artifacts as binders;
  -- MemBus `m0..m2` shape derived by `rfl`.
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
      (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
      r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_imm_eq := h_input_imm
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  -- (a) circuit-internal arithmetic + lane→Sail binding.
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
    allByteMatchesOfStaticOut64_local h_out
  -- Lane → Sail binding for r1: from r1 lane bridges (binders) + provider match.
  have h_input_r1_row :
      andi_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) andi_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  -- Immediate routing: DERIVE the 8-byte Binary-row form from the named Main-form
  -- pin + the in-body byte-match fact + `m32 = 0` + the provider match.
  have h_input_imm_row :
      BitVec.signExtend 64 andi_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val andi_input.imm h_matches h_m32_zero h_match
        h_andi_subset
  exact ZiskFv.Compliance.equiv_ANDI
    state andi_input r1 rd imm m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_imm_row h_andi_subset h_lane_rd promises

/-- Sound ORI construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (ITYPE ORI) = (bus_effect …).2`.

    Residual budget identical to ANDI (16 + `imm` + `execRow`). DELTA from
    `construction_andi_sound`: `Or.inl h_main_op → Or.inr (Or.inl h_main_op)`;
    `OP_AND → OP_OR`; `AndiInput → OriInput`; `equiv_ANDI → equiv_ORI`;
    `execute_ITYPE_andi_pure → execute_ITYPE_ori_pure`. `OP_OR = 15 < 16`, so the
    same `_op_lt_16` + `_64` data-effect route applies. -/
theorem construction_ori_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (ori_input : PureSpec.OriInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_OR)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail read + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok ori_input.r1_val (binding.stateAt i))
    (h_input_imm : ori_input.imm = imm)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some ori_input.PC)
    (h_input_rd : ori_input.rd = regidx_to_fin rd)
    -- (b) r1 lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    -- (b) immediate-routing pin (NAMED top-level binder, program/decode residual)
    (h_ori_subset : itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val ori_input.imm)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC)
    (h_rd_idx :
      ori_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ORI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_main_active (Or.inr (Or.inl h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_OR :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
      (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
      r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_imm_eq := h_input_imm
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_OR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_OR, ZiskFv.Trusted.OP_OR] using
      h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_OR (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_OR])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_OR h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      ori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) ori_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 ori_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val ori_input.imm h_matches h_m32_zero h_match
        h_ori_subset
  exact ZiskFv.Compliance.equiv_ORI
    state ori_input r1 rd imm m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_imm_row h_ori_subset h_lane_rd promises

/-- Sound XORI construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (ITYPE XORI) = (bus_effect …).2`.

    Residual budget identical to ANDI/ORI (16 + `imm` + `execRow`). XORI inherits
    XOR's wrinkle: `OP_XOR = 16` fails the `op_val < 16` precondition, so the
    in-body `h_matches` is derived via the 3-way-selector mode-pin lemma
    `static_table_logic_mode_pins_of_emit` + the `_logic` byte-chain
    `byte_chain_discharge_logic_of_static_row` (mirroring `construction_xor_sound`),
    NOT the `_op_lt_16` + `_64` pair. The I-type immediate DELTA is identical to
    ANDI/ORI; route via `equiv_XORI`. -/
theorem construction_xori_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_XOR)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail read + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok xori_input.r1_val (binding.stateAt i))
    (h_input_imm : xori_input.imm = imm)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some xori_input.PC)
    (h_input_rd : xori_input.rd = regidx_to_fin rd)
    -- (b) r1 lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    -- (b) immediate-routing pin (NAMED top-level binder, program/decode residual)
    (h_xori_subset : itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val xori_input.imm)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC)
    (h_rd_idx :
      xori_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_main_active (Or.inr (Or.inr h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_XOR :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
      (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
      r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_imm_eq := h_input_imm
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  -- The op=16 mode-pin route needs `Spec providerInput` + the static facts; both
  -- come from the static lookup component spec (cf. `construction_xor_sound`).
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (providerTable.environment providerRow) := by
    simpa [h_component] using h_table_spec providerRow h_provider_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_row_spec, h_static⟩ := h_component_spec
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_XOR : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_XOR, ZiskFv.Trusted.OP_XOR] using
      h_main_op
  obtain ⟨_, h_bop_row, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      providerInput h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      providerInput h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop_row h_bop_or_sext
  have h_input_r1_row :
      xori_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) xori_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_imm_row :
      BitVec.signExtend 64 xori_input.imm
        = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
        m providerInput i.val xori_input.imm h_matches h_m32_zero h_match
        h_xori_subset
  exact ZiskFv.Compliance.equiv_XORI
    state xori_input r1 rd imm m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_imm_row h_xori_subset h_lane_rd promises

/-- Sound SLTI construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (ITYPE SLTI) = (bus_effect …).2`.

    Residual budget identical to ANDI/ORI/XORI (16 + `imm` + `execRow`). Mirrors
    `construction_slt_sound` (compare Layer-A wrapper
    `exists_staticBinary_provider_row_matches_compare_from_binding`, `OP_LT = 7 < 16`
    so the in-body `h_matches` reuses the `_op_lt_16` + `_64` route) through the
    uniform I-type immediate DELTA. `equiv_SLTI` consumes the Main-form
    `h_slti_subset` + `m32 = 0` directly and re-derives the 8-byte immediate form
    internally, so NO `h_input_imm_row` is passed; the signed-compare polarity lives
    inside the wrapper. -/
theorem construction_slti_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (slti_input : PureSpec.SltiInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_LT)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail read + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok slti_input.r1_val (binding.stateAt i))
    (h_input_imm : slti_input.imm = imm)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slti_input.PC)
    (h_input_rd : slti_input.rd = regidx_to_fin rd)
    -- (b) r1 lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    -- (b) immediate-routing pin (NAMED top-level binder, program/decode residual)
    (h_slti_subset : itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val slti_input.imm)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC)
    (h_rd_idx :
      slti_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTI))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i h_main_active (Or.inl h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LT :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
      (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
      r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_imm_eq := h_input_imm
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      slti_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) slti_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  exact ZiskFv.Compliance.equiv_SLTI
    state slti_input r1 rd imm m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match h_m32_zero
    h_input_r1_row h_slti_subset h_lane_rd promises

/-- Sound SLTIU construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (ITYPE SLTIU) = (bus_effect …).2`.

    Residual budget identical to SLTI (16 + `imm` + `execRow`). DELTA from
    `construction_slti_sound`: `Or.inl → Or.inr`; `OP_LT → OP_LTU`;
    `SltiInput → SltiuInput`; `equiv_SLTI → equiv_SLTIU`;
    `execute_ITYPE_slti_pure → execute_ITYPE_sltiu_pure`. `OP_LTU = 6 < 16`, so the
    same `_op_lt_16` + `_64` route applies; the unsigned-compare polarity (and the
    RISC-V quirk that SLTIU sign-extends the 12-bit imm to 64 then compares
    unsigned) lives inside `equiv_SLTIU`. The imm packing is the uniform
    `BitVec.signExtend 64 imm` Main-form pin. -/
theorem construction_sltiu_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (sltiu_input : PureSpec.SltiuInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_LTU)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail read + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok sltiu_input.r1_val (binding.stateAt i))
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sltiu_input.PC)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    -- (b) r1 lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    -- (b) immediate-routing pin (NAMED top-level binder, program/decode residual)
    (h_sltiu_subset : itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable)
      i.val sltiu_input.imm)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC)
    (h_rd_idx :
      sltiu_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_compare_from_binding
      trace binding i h_main_active (Or.inr h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_LTU :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  have h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m i.val bus.e2 := by
    have h :=
      ZiskFv.AirsClean.Main.cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero
        (mainRowWithRomSub trace binding i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
      (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
      r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_imm_eq := h_input_imm
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using
      h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LTU :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      sltiu_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) sltiu_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  exact ZiskFv.Compliance.equiv_SLTIU
    state sltiu_input r1 rd imm m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match h_m32_zero
    h_input_r1_row h_sltiu_subset h_lane_rd promises

end ZiskFv.Compliance
