import ZiskFv.Compliance.OpBusProviderMatch
import ZiskFv.Compliance.SailTrace
import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Wrappers.Addw
import ZiskFv.Compliance.Wrappers.Subw
import ZiskFv.Compliance.Wrappers.Addiw
import ZiskFv.EquivCore.Addw

/-!
# Sound W-ALU constructions (`construction_subw_sound`, `construction_addw_sound`,
  `construction_addiw_sound`)

PR5 / Wave 6 of the P4 SWEEP: the m32 = 1 word-ALU families. These were
NEEDS-WORK because the prerequisite m32 = 1 32-bit lane-binding lemma did not
exist; it is now authored as
`ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row` /
`input_r2_packed_b32_row` (the binary analog of the BinaryExtension shift
bridge's `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range`). With that lemma in
place these three constructions instantiate the honest §2 ALU template against the
staticBinary provider in the **m32 = 1** path.

## The W-mode DELTA from `construction_sub_sound`

The W families differ from the 64-bit SUB construction on exactly these points:

1. **m32 = 1** (not 0): `h_m32` pins `m.m32 i.val = 1`. The op-bus `a_hi`/`b_hi`
   lanes collapse to `0` (provider high bytes pinned zero); the 32-bit operand is
   sourced from the `a_lo`/`b_lo` conjunct only.
2. **op-bus provider match** via the salvaged W Layer-A wrapper
   `main_request_w_provided` (op pin disjunction
   `OP_ADD_W ∨ OP_SUB_W`).
3. **lane → Sail binding** via the new m32 = 1 lane lemmas, producing the 32-bit
   `extractLsb _ 31 0` form `binaryRowA32 row % 2^32` (NOT the 64-bit
   `binaryRowA64`). The 4 low a/b byte ranges feeding the lemmas are projected
   from `h_facts` (`StaticBinaryTableWfFacts`) — no `byte_chain_discharge_64`
   (which requires `mode32 = 0`).
4. **equiv wrapper** `equiv_SUBW` / `equiv_ADDW` / `equiv_ADDIW`; Sail pure spec
   `execute_RTYPE_subw_pure` / `..._addw_pure` / `execute_ITYPE_addiw_pure`;
   conclusion `ropw.SUBW` / `ropw.ADDW` / `instruction.ADDIW`. All three KEEP the
   `writeReg Register.nextPC` prelude (the W-ALU wrappers carry it, unlike the
   bare-execute W-shifts).
5. **ADDIW** is ITYPE: immediate `imm : BitVec 12`, the named decode pin
   `h_addiw_subset : itype_imm_subset_holds_main`, `ITypePromises`. The wrapper
   derives the immediate byte decomposition `h_input_imm_extract` internally from
   `h_addiw_subset` + the `b_lo` field of `h_match`, so the construction supplies
   only the r1 lane extract.

## Residual budget

ADDW / SUBW: same flat top-level budget as `construction_sub_sound` — the 17
named residuals + `execRow` ∀-binder (`h_m32` value 1 instead of 0; otherwise the
identical decode pins / Sail reads / lane bridges / next-PC / exec artifacts).
ADDIW swaps the r2 lane bridges + r2 read for the immediate `imm` binder +
`h_input_imm` + `h_addiw_subset` (the I-type delta of PR3), `RTypePromises →
ITypePromises`.

## Anti-vacuity (PLAN §4.9)

`execRow` is a genuine top-level ∀-binder in all three; the bus is `busSub`
(built from the real trace row), so the exec hypotheses are jointly satisfiable.

## Axioms

Each of the three constructions, and the new lane lemmas they consume, introduce
**0 PROJECT (`ZiskFv.*`) axioms**; the closure includes only the Sail-translation
axioms and Lean-kernel postulates as documented external trust.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises
open ZiskFv.Tactics.ALUITypeArchetype

set_option maxHeartbeats 2000000

/-- Sound SUBW construction (m32 = 1 word ALU). Unique opcode `OP_SUB_W`
    (`Or.inr` of the shared W Layer-A wrapper). -/
theorem construction_subw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (subw_input : PureSpec.SubwInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SUB_W)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 1)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok subw_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok subw_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some subw_input.PC)
    (h_input_rd : subw_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC)
    (h_rd_idx :
      subw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.SUBW))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced`. SUBW = `Or.inr`.
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_w_provided
      trace i h_main_active (Or.inr h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SUB_W :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
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
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
      (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
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
  -- (a) provider correctness facts; byte ranges (a/b low 4) from `h_facts`.
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have hb0 : (providerInput.bBytes.free_in_b_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (providerInput.bBytes.free_in_b_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (providerInput.bBytes.free_in_b_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (providerInput.bBytes.free_in_b_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  -- Lane → Sail binding (m32 = 1, 32-bit extract) via the new lane lemmas.
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin r1) subw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowB32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b32_row
        m providerInput i.val (regidx_to_fin r2) subw_input.r2_val
        hb0 hb1 hb2 hb3 h_m32_one h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.Compliance.equiv_SUBW
    state subw_input r1 r2 rd m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_extract h_input_r2_extract h_lane_rd promises

/-- Sound ADDW construction (m32 = 1 word ALU). DELTA from
    `construction_subw_sound`: op pin `OP_ADD_W` (`Or.inl` of the shared W
    Layer-A wrapper), `ropw.ADDW`, `execute_RTYPE_addw_pure`, `equiv_ADDW`. -/
theorem construction_addw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (addw_input : PureSpec.AddwInput)
    (r1 r2 rd : regidx)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_ADD_W)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 1)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok addw_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok addw_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some addw_input.PC)
    (h_input_rd : addw_input.rd = regidx_to_fin rd)
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
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC)
    (h_rd_idx :
      addw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPEW (r2, r1, rd, ropw.ADDW))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_w_provided
      trace i h_main_active (Or.inl h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD_W :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
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
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
      (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
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
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have hb0 : (providerInput.bBytes.free_in_b_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.2.1
  have hb1 : (providerInput.bBytes.free_in_b_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.2.1
  have hb2 : (providerInput.bBytes.free_in_b_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.2.1
  have hb3 : (providerInput.bBytes.free_in_b_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.2.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin r1) addw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_extract :
      (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowB32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b32_row
        m providerInput i.val (regidx_to_fin r2) addw_input.r2_val
        hb0 hb1 hb2 hb3 h_m32_one h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.Compliance.equiv_ADDW
    state addw_input r1 r2 rd m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_extract h_input_r2_extract h_lane_rd promises

/-- Sound ADDIW construction (m32 = 1 word ALU, ITYPE immediate). DELTA from
    `construction_addw_sound`: drops the r2 read + r2 lane bridges; adds the
    immediate binder `imm : BitVec 12`, the immediate-decode equality
    `h_input_imm : addiw_input.imm = imm`, and the NAMED top-level decode pin
    `h_addiw_subset : itype_imm_subset_holds_main`; swaps `RTypePromises →
    ITypePromises`; routes via `equiv_ADDIW` (`execute_ITYPE_addiw_pure`,
    `instruction.ADDIW`). Shares `OP_ADD_W` with ADDW (`Or.inl`); the wrapper
    derives the immediate byte decomposition internally from `h_addiw_subset` +
    `h_match`, so the construction supplies only the r1 lane extract. -/
theorem construction_addiw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_ADD_W)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 1)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok addiw_input.r1_val (binding i))
    (h_input_imm : addiw_input.imm = imm)
    (h_input_pc : (binding i).regs.get? Register.PC = .some addiw_input.PC)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
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
    -- (b) immediate-routing pin (NAMED top-level binder, program/decode residual)
    (h_addiw_subset : itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      i.val addiw_input.imm)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC)
    (h_rd_idx :
      addiw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_w_provided
      trace i h_main_active (Or.inl h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD_W :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
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
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
      (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
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
  have h_m32_one : m.m32 i.val = 1 := h_m32
  have ha0 : (providerInput.aBytes.free_in_a_0).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.1.1.1
  have ha1 : (providerInput.aBytes.free_in_a_1).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.1.1.1
  have ha2 : (providerInput.aBytes.free_in_a_2).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.1.1.1
  have ha3 : (providerInput.aBytes.free_in_a_3).val < 256 := by
    simpa [ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using h_facts.2.2.2.1.1.1
  have h_input_r1_extract :
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 providerInput % 2^32 := by
    simpa [ZiskFv.EquivCore.Addw.binaryRowA32] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a32_row
        m providerInput i.val (regidx_to_fin r1) addiw_input.r1_val
        ha0 ha1 ha2 ha3 h_m32_one h_a_lo_t h_a_hi_t h_match h_input_r1
  exact ZiskFv.Compliance.equiv_ADDIW
    state addiw_input r1 rd imm m providerTable providerRow i.val bus pins
    h_addiw_subset h_component h_table_spec h_provider_row h_match
    h_input_r1_extract h_lane_rd promises

end ZiskFv.Compliance
