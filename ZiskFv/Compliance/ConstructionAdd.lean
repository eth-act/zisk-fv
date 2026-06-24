import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Wrappers.Add
import ZiskFv.Compliance.Wrappers.Addi
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.Tactics.ALUITypeArchetype

/-!
# Sound ADD / ADDI constructions (`construction_add_sound`, `construction_addi_sound`)

The ADD / ADDI families of the P4 SWEEP Wave 5 (PLAN_ENDGAME_P4_SWEEP.md PR4).
These are the NEEDS-WORK families: unlike SUB/AND/OR/XOR/… they are **not**
clones of `construction_and_sound`, because `OP_ADD = 0x0A = 10` may be served by
EITHER of two distinct providers with two distinct `opBusMessage` shapes:

* the lookup-aware Binary provider (`staticLookupComponent`), or
* the dedicated `BinaryAdd` provider (`BinaryAdd.component`).

The salvaged Layer-A wrapper `main_request_add_provided`
(`AcceptedZiskTrace.lean`) RESOLVES the op-bus from `trace.channels_balanced` into the
conjunction

```
add_subset_holds m i.val  ∧  (staticLookup-match ∨ BinaryAdd-match)
```

— a genuine provider DISJUNCTION, not a single unambiguous provider.

## The chosen approach — (a) two-arm case-split (PR4 design decision)

This construction takes **approach (a)** from the plan: it CASE-SPLITS the
provider disjunction and discharges the **same** canonical goal on EACH arm,
deriving the rd data effect independently per arm. No exclusion premise is
carried — the conclusion holds regardless of which provider served the op.

* **lookup arm** — mirrors `construction_sub_sound` / `construction_and_sound`:
  derives the all-byte-matches fact via
  `logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` (`OP_ADD = 10 < 16`) +
  `byte_chain_discharge_64_of_static_row`, then the lane→Sail binding
  (`input_r1_packed_a_row` / `input_r2_packed_b_row`), then calls
  `Compliance.equiv_ADD` (the lookup-arm wrapper).
* **BinaryAdd arm** — calls `Compliance.equiv_ADD_via_binaryadd`, which consumes
  the `add_subset_holds` conjunct (derived, NOT a binder), the r1/r2 lane bridges,
  `m32 = 0`, and the BinaryAdd component facts (all derived from the provider's
  Clean `Spec`). The data effect (`binary_add_chunks_eq_bv_add_via_component`)
  bottoms inside `equiv_ADD_of_binaryadd_row`.

Both arms share the SAME `bus` (`busSub`), `pins`, `promises`, `h_lane_rd`, and
r1/r2 lane bridges — the rd write (`bus.e2`) is the Main row's emission regardless
of which provider served the op. The disjunction only changes the op-bus
provider-match block and how the operand→Sail binding is routed.

## Residual budget: EXACTLY 17 + execRow (ADD), same as SUB/AND

The disjunction is RESOLVED inside the body — both `add_subset_holds` and the
provider match are DERIVED (bucket-(a)), not binders. So ADD's residual budget is
identical to SUB's: the same 17 named top-level binders + `execRow`. (ADDI grows
by the I-type immediate delta: it drops the r2 register lane bridges and gains the
`imm` binder, the `h_input_imm` decode equality, the `h_addi_subset` immediate
routing pin, and a `h_set_pc` pin consumed by the BinaryAdd arm.)

## Anti-vacuity (PLAN §4.9)

`execRow` is a genuine top-level ∀-binder in BOTH; the bus consumed by the exec
hypotheses is built from the real trace row (`busSub`), NOT chosen to trivialize a
hypothesis.

## Axioms

Both constructions introduce **0 PROJECT (`ZiskFv.*`) axioms**. As with every
canonical theorem in this project, their closure still includes the
Sail-translation axioms and the Lean-kernel postulates as documented external
trust (`TrustGate.AxiomClosure.isProjectAxiom` filters those by design).
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- Sound ADD construction (PR4, approach (a): two-arm provider case-split).

    From the accepted trace + honest residual binders, conclude the canonical
    `execute (RTYPE ADD) = (bus_effect …).2`. The op-bus provider is resolved from
    `trace.channels_balanced` into a `staticLookup ∨ BinaryAdd` disjunction; BOTH arms are
    discharged, each deriving the rd data effect from the corresponding provider's
    Clean `Spec`. The `add_subset_holds` conjunct and the provider match are
    DERIVED (bucket-(a)), so the residual budget matches SUB: 17 + `execRow`.

    Honest top-level residual binders (the validated §2 SUB budget, 17 +
    `execRow`):
    * (b) decode pins (4): `h_main_op`, `h_main_active`, `h_m32`, `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder. -/
theorem construction_add_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_ADD)
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
        = EStateM.Result.ok add_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok add_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some add_input.PC)
    (h_input_rd : add_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_rd_idx :
      add_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.ADD))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider RESOLUTION, derived from `trace.channels_balanced`: the
  -- `add_subset_holds` conjunct + a `staticLookup ∨ BinaryAdd` DISJUNCTION.
  obtain ⟨h_add_subset, h_disj⟩ :=
    main_request_add_provided
      trace i h_main_active h_main_op
  -- decode pins bundle (shared by both arms)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD :=
    ⟨h_main_active, h_main_op⟩
  -- (a) lane-rd, derived from store_pc = 0 (shared by both arms; no record)
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
  -- promises bundle: Sail reads + exec artifacts as binders; MemBus shape `rfl`.
  -- (shared by both arms)
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
      (PureSpec.execute_RTYPE_add_pure add_input).nextPC
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
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  -- CASE-SPLIT the provider disjunction; discharge the SAME goal on each arm.
  rcases h_disj with h_lookup | h_binaryadd
  · -- lookup arm: mirror the SUB / AND construction body.
    obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_lookup
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
    have h_emit :
        providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
          (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
      have h_match_op := h_match
      simp only [ZiskFv.Airs.OperationBus.matches_entry,
        ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
      have h_op_match :
          m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, ZiskFv.Trusted.OP_ADD] using
        h_main_op
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_ADD (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD])
        h_core h_emit
    have h_out :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        providerInput h_facts
        ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
    have h_matches :
        ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
          providerInput ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
      allByteMatchesOfStaticOut64_local h_out
    have h_input_r1_row :
        add_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
          m providerInput i.val (regidx_to_fin r1) add_input.r1_val
          h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
    have h_input_r2_row :
        add_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
          m providerInput i.val (regidx_to_fin r2) add_input.r2_val
          h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
    exact ZiskFv.Compliance.equiv_ADD
      state add_input r1 r2 rd m providerTable providerRow i.val bus pins
      h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  · -- BinaryAdd arm: discharge via `equiv_ADD_via_binaryadd`.
    obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    exact ZiskFv.Compliance.equiv_ADD_via_binaryadd
      state add_input r1 r2 rd m providerTable providerRow i.val bus pins
      h_component h_table_spec h_provider_row h_match
      h_add_subset h_a_lo_t h_a_hi_t h_b_lo_t h_b_hi_t h_m32_zero
      h_lane_rd promises

/-- Sound ADDI construction (PR4, approach (a): two-arm provider case-split).

    = `construction_add_sound` + the PR3 I-type immediate delta. The op-bus is the
    SAME `staticLookup ∨ BinaryAdd` disjunction (the op-bus match is
    operand-source-agnostic); the second operand is the immediate, sourced via the
    named `h_addi_subset` (`itype_imm_subset_holds_main`) decode pin instead of an
    r2 register read. The r2 register lane bridges are dropped; `imm`, the decode
    equality `h_input_imm`, the immediate routing pin `h_addi_subset`, and the
    BinaryAdd-arm `h_set_pc` pin are added.

    Residual budget = ADD's, minus the 2 r2 lane bridges (`h_b_lo_t`/`h_b_hi_t`)
    and `h_input_r2`, plus `imm`, `h_input_imm`, `h_addi_subset`, `h_set_pc`. -/
theorem construction_addi_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx)
    (imm : BitVec 12)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_ADD)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    (h_set_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).set_pc
        i.val = 0)
    -- (b) Sail read + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok addi_input.r1_val (binding i))
    (h_input_imm : addi_input.imm = imm)
    (h_input_pc : (binding i).regs.get? Register.PC = .some addi_input.PC)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    -- (b) r1 lane bridges
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
    (h_addi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
      i.val addi_input.imm)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_rd_idx :
      addi_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider RESOLUTION, derived from `trace.channels_balanced`: the
  -- `add_subset_holds` conjunct + a `staticLookup ∨ BinaryAdd` DISJUNCTION
  -- (the op-bus match is operand-source-agnostic, so the SAME wrapper serves ADDI).
  obtain ⟨h_add_subset, h_disj⟩ :=
    main_request_add_provided
      trace i h_main_active h_main_op
  -- decode pins bundle (shared by both arms)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_ADD :=
    ⟨h_main_active, h_main_op⟩
  -- (a) lane-rd, derived from store_pc = 0 (shared by both arms; no record)
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
  -- promises bundle: Sail read + immediate + exec artifacts as binders;
  -- MemBus shape `rfl`. (shared by both arms)
  let promises : ZiskFv.EquivCore.Promises.ITypePromises
      state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
      (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
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
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_set_pc_zero : m.set_pc i.val = 0 := h_set_pc
  -- CASE-SPLIT the provider disjunction; discharge the SAME goal on each arm.
  rcases h_disj with h_lookup | h_binaryadd
  · -- lookup arm: mirror the ANDI construction body (immediate routing).
    obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_lookup
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
    have h_emit :
        providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
          (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
      have h_match_op := h_match
      simp only [ZiskFv.Airs.OperationBus.matches_entry,
        ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
      have h_op_match :
          m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
        h_match_op.2.1
      rw [← h_op_match]
      simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, ZiskFv.Trusted.OP_ADD] using
        h_main_op
    obtain ⟨h_row_m32, h_bop, _⟩ :=
      ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
        providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_ADD (by
          simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD])
        h_core h_emit
    have h_out :=
      ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
        providerInput h_facts
        ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
    have h_matches :
        ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
          providerInput ZiskFv.Airs.Tables.BinaryTable.OP_ADD :=
      allByteMatchesOfStaticOut64_local h_out
    have h_input_r1_row :
        addi_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
          m providerInput i.val (regidx_to_fin r1) addi_input.r1_val
          h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
    -- Immediate routing: DERIVE the 8-byte Binary-row form from the named Main-form
    -- pin + the in-body byte-match fact + `m32 = 0` + the provider match.
    have h_input_imm_row :
        BitVec.signExtend 64 addi_input.imm
          = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.itype_imm_subset_binary_row_of_main_row
          m providerInput i.val addi_input.imm h_matches h_m32_zero h_match
          h_addi_subset
    exact ZiskFv.Compliance.equiv_ADDI
      state addi_input r1 rd imm m providerTable providerRow i.val bus pins
      h_component h_table_spec h_provider_row h_match
      h_addi_subset h_input_r1_row h_input_imm_row h_lane_rd promises
  · -- BinaryAdd arm: discharge via `equiv_ADDI_via_binaryadd`.
    obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    exact ZiskFv.Compliance.equiv_ADDI_via_binaryadd
      state addi_input r1 rd imm m providerTable providerRow i.val bus pins
      h_component h_table_spec h_provider_row h_match
      h_add_subset h_addi_subset h_a_lo_t h_a_hi_t h_m32_zero h_set_pc_zero
      h_lane_rd promises

end ZiskFv.Compliance
