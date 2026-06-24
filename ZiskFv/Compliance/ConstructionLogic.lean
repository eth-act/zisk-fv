import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.Wrappers.Or
import ZiskFv.Compliance.Wrappers.Xor

/-!
# Sound logic constructions (`construction_or_sound`, `construction_xor_sound`)

The OR and XOR families of the P4 SWEEP Wave 1 (PLAN_ENDGAME_P4_SWEEP.md PR1).
Both mirror `construction_and_sound` (`ZiskFv/Compliance/ConstructionAnd.lean`):
they assemble the canonical conclusion (`execute (RTYPE OR/XOR) = (bus_effect …).2`)
from an accepted full-ensemble trace plus an explicit, named, top-level set of
residual binders — with **no** `*RowBinding` / `MainRowProvenance` record carrying
any fact.

Both reuse the op-agnostic infra `busSub` / `mainRowWithRomSub`
(`ZiskFv/Compliance/ConstructionSub.lean`) and the salvaged logic Layer-A wrapper
`exists_staticBinary_provider_row_matches_logic_from_binding` (which serves
AND / OR / XOR, taking the op pin as the disjunction
`op = OP_AND ∨ op = OP_OR ∨ op = OP_XOR`). The residual budget is identical to
SUB/AND: EXACTLY `4 + 5 + 4 + 1 + 3 = 17` hypothesis binders plus the genuine
`execRow` ∀-binder.

## OR (`construction_or_sound`)

`OP_OR = 15 < 16`, so the construction body reuses AND's exact data-effect route
(`logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` discharging
`by simp [OP_OR]` + `byte_chain_discharge_64_of_static_row`). DELTA from
`construction_and_sound`: `Or.inl h_main_op → Or.inr (Or.inl h_main_op)`;
`OP_AND → OP_OR`; `AndInput → OrInput`; `equiv_AND → equiv_OR`;
`execute_RTYPE_and_pure → execute_RTYPE_or_pure`.

## XOR (`construction_xor_sound`)

`OP_XOR = 0x10 = 16` does NOT satisfy the `op_val < 16` precondition of
`logic_row_mode_pins_of_emit_op_lt_16_of_static_spec`. So XOR's construction body
cannot reuse AND's `_op_lt_16` + `_64` route. It instead mirrors
`EquivCore/Xor.lean`:
* `Spec providerInput` (`h_row_spec`) is unpacked from `staticLookupComponent.Spec`
  (the `.1` of the component spec, alongside `h_static`),
* mode-pins via `static_table_logic_mode_pins_of_emit row … OP_XOR (.inr (.inr rfl))
  h_emit` (3-way selector, NO `< 16` bound), returning `b_op.val = OP_XOR` and
  `b_op_or_sext.val = OP_XOR`,
* the all-byte-matches fact via `byte_chain_discharge_logic_of_static_row` (the
  `_logic` variant, NOT the `_64` one) which already returns
  `all_byte_matches_wf_at_row`.
The downstream `h_matches` / lane-binding plumbing and the final `equiv_XOR` call
are the AND shape.

## Anti-vacuity (PLAN §4.9)

`execRow` is a genuine top-level ∀-binder in BOTH; the bus consumed by the exec
hypotheses is built from the real trace row (`busSub`), NOT chosen to trivialize a
hypothesis.

## Axioms

Both constructions introduce **0 PROJECT (`ZiskFv.*`) axioms**. As with every
canonical theorem in this project, their closure still includes the
Sail-translation axioms and the Lean-kernel postulates as documented external
trust.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- Sound OR construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (RTYPE OR) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 logic budget, 17 +
    `execRow`):
    * (b) decode pins (4): `h_main_op` (= `OP_OR`), `h_main_active`, `h_m32`,
      `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.channels_balanced`, via the salvaged logic wrapper), row shape, circuit-internal
    rd arithmetic, the MemBus `m0..m2` shape, `h_lane_rd`, and the lane→Sail
    binding facts. -/
theorem construction_or_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_OR)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok or_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok or_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some or_input.PC)
    (h_input_rd : or_input.rd = regidx_to_fin rd)
    -- (b) lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_or_pure or_input).nextPC)
    (h_rd_idx :
      or_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced` via the salvaged
  -- logic wrapper (serves AND / OR / XOR; op pin given as the OR disjunct).
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_main_active (Or.inr (Or.inl h_main_op))
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_OR :=
    ⟨h_main_active, h_main_op⟩
  -- (a) lane-rd, derived from store_pc = 0 (no record consumed)
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
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
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  -- promises bundle: Sail reads + exec artifacts as binders;
  -- MemBus `m0..m2` shape derived by `rfl`.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
      (PureSpec.execute_RTYPE_or_pure or_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
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
  -- Lane → Sail binding: from lane bridges (binders) + provider match.
  have h_input_r1_row :
      or_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) or_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      or_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) or_input.r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.Compliance.equiv_OR
    state or_input r1 r2 rd m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_r2_row h_lane_rd promises

/-- Sound XOR construction: from the accepted trace + honest residual binders,
    conclude the canonical `execute (RTYPE XOR) = (bus_effect …).2`.

    Residual budget identical to OR/AND (17 + `execRow`). The ONLY difference
    from `construction_or_sound` is the data-effect route: `OP_XOR = 16` fails the
    `op_val < 16` precondition, so `h_matches` is derived via the 3-way-selector
    mode-pin lemma `static_table_logic_mode_pins_of_emit` + the `_logic` byte-chain
    `byte_chain_discharge_logic_of_static_row` (mirroring `EquivCore/Xor.lean`),
    NOT the `_op_lt_16` + `_64` pair. -/
theorem construction_xor_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (xor_input : PureSpec.XorInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_XOR)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok xor_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok xor_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some xor_input.PC)
    (h_input_rd : xor_input.rd = regidx_to_fin rd)
    -- (b) lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC)
    (h_rd_idx :
      xor_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.XOR))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced` via the salvaged
  -- logic wrapper (serves AND / OR / XOR; op pin given as the XOR disjunct).
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_logic_from_binding
      trace binding i h_main_active (Or.inr (Or.inr h_main_op))
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_XOR :=
    ⟨h_main_active, h_main_op⟩
  -- (a) lane-rd, derived from store_pc = 0 (no record consumed)
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
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
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  -- promises bundle: Sail reads + exec artifacts as binders;
  -- MemBus `m0..m2` shape derived by `rfl`.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
      (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
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
  -- The `Spec providerInput` and `StaticBinaryTableSpecFacts providerInput` are
  -- both required by the op=16 mode-pin route; both come from the static lookup
  -- component spec.
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
  -- op=16 mode-pin route (3-way selector, no `< 16` bound).
  obtain ⟨_, h_bop_row, h_bop_or_sext⟩ :=
    ZiskFv.AirsClean.Binary.static_table_logic_mode_pins_of_emit
      providerInput h_row_spec h_static ZiskFv.Airs.Tables.BinaryTable.OP_XOR
      (.inr (.inr rfl)) h_emit
  -- `_logic` byte-chain (already returns `all_byte_matches_wf_at_row`).
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_XOR :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_logic_of_static_row
      providerInput h_facts ZiskFv.Airs.Tables.BinaryTable.OP_XOR h_bop_row h_bop_or_sext
  -- Lane → Sail binding: from lane bridges (binders) + provider match.
  have h_input_r1_row :
      xor_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) xor_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      xor_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) xor_input.r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.Compliance.equiv_XOR
    state xor_input r1 r2 rd m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_r2_row h_lane_rd promises

end ZiskFv.Compliance
