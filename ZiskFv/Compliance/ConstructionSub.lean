import ZiskFv.Compliance.ProviderFromBinding
import ZiskFv.Compliance.Wrappers.Sub

/-!
# Sound SUB construction (`construction_sub_sound`)

This is the first honest sound construction in the P4 closeout: it assembles
the canonical SUB conclusion (`execute (RTYPE SUB) = (bus_effect …).2`) from an
accepted full-ensemble trace plus an explicit, named, top-level set of residual
binders — with **no** `*RowBinding` / `MainRowProvenance` record carrying any
fact. It supersedes the relabel `construction_<op>` stack (stripped): instead of
forwarding a caller-supplied decode bundle into an `*OfExtractedShape`
constructor, it **derives** the op-bus provider match, the row shape, the
circuit-internal rd arithmetic, and the MemBus write shape from the accepted
trace + channel balance + provider correctness.

## The honest decomposition (PLAN_ENDGAME_P4_CLOSEOUT.md §2)

A SUB envelope's content splits into three buckets against the live Clean
ensemble (channels = OpBus + MemBus only; per-row component model):

* **(a) derived** — proven inside the body, NOT a binder:
  - op-bus provider match (from `trace.channels_balanced`, via the salvaged Layer-A
    `exists_staticBinary_provider_row_matches_sub_from_binding`, bottoming in an
    axiom-free Layer-B permutation theorem),
  - row shape (`mainOfTable` / `rowAt_mainOfTable`),
  - circuit-internal rd arithmetic (the already-proven packed byte-chain lemmas),
  - MemBus `m0..m2` write shape (`by rfl` off the real trace row),
  - `h_lane_rd` (from `store_pc = 0`),
  - and the lane→Sail binding facts `h_input_r1_row` / `h_input_r2_row`.

* **(b) named residual** — explicit top-level binders (program/ROM/Sail facts
  the ensemble cannot finish; not new trust, but visible):
  - decode pins (4): `h_main_op`, `h_main_active`, `h_m32`, `h_store_pc`
  - Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
    `h_input_rd`, `h_rd_idx`
  - lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
  - control-flow next-PC (1): `h_nextPC_matches`
    (blocked by the cross-row Clean-model ceiling — filed prerequisite #1).

* **(c) artifact** — pure `bus_effect`/`ExecutionBusEntry` bookkeeping with no
  ZisK counterpart (eliminated when `bus_effect` is retired):
  - exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`,
  - PLUS the genuine `execRow : List (ExecutionBusEntry FGL)` **∀-binder**.

## Residual budget: EXACTLY 17 + execRow

The top-level residual binders are exactly `4 + 5 + 4 + 1 + 3 = 17` hypothesis
binders, plus the genuine `execRow` universally-quantified binder. No
`MainRowProvenance` / `SubRowBinding` leaf appears anywhere in the binder set.

## Anti-vacuity (PLAN §4.9)

`execRow` MUST be a genuine top-level ∀-binder. The bus consumed by the exec
hypotheses is built from the real trace row (`busSub`), NOT chosen to trivialize
a hypothesis. Hard-coding `execRow := []` would make `h_exec_len : [].length = 2`
(i.e. `0 = 2`) and the exec hypotheses contradictory → the theorem would be
vacuously true. The ∀-binder keeps the residual hypotheses jointly satisfiable.

## Axioms

`construction_sub_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**. As with
every canonical theorem in this project, its closure still includes the
Sail-translation axioms and the Lean-kernel postulates as documented external
trust (`TrustGate.AxiomClosure.isProjectAxiom` filters those by design).
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- Standalone projection over the public byte-chain lemmas.

    This was a `private` helper inside the (now-stripped) `construction_<op>`
    block of `AcceptedTrace.lean`; it survives here because the sound
    construction below is the only remaining consumer. It is a pure projection
    (`rcases`/`exact`) over a public structure — no trust content. -/
theorem consumerByteMatchOfChainWf_local
    {op : Nat} {a b c cin flags pos : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf op a b c cin flags pos) :
    ZiskFv.Airs.Binary.consumer_byte_match_wf op a b c := by
  rcases h with ⟨e, h_wf, h_op, h_a, h_b, h_c, _h_cin, _h_flags, _h_pos⟩
  exact ⟨e, h_wf, h_op, h_a, h_b, h_c⟩

/-- Standalone projection turning a `BinaryChainStaticOut64` into the
    `all_byte_matches_wf_at_row` bundle.

    As with `consumerByteMatchOfChainWf_local`, this was a `private` helper in
    the stripped construction block; it is a pure projection over public lemmas. -/
theorem allByteMatchesOfStaticOut64_local
    {row : ZiskFv.AirsClean.Binary.BinaryRow FGL} {op : Nat}
    (out : ZiskFv.EquivCore.Bridge.Binary.BinaryChainStaticOut64
      (ZiskFv.AirsClean.Binary.validOfRow row) 0 op) :
    ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row op := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_0
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_1
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_2
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_3
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_4
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_5
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_6
  · simpa [ZiskFv.AirsClean.Binary.validOfRow] using
      consumerByteMatchOfChainWf_local out.chain_7

/-- The honest unified Main+ROM row at trace index `i`, drawn from the
    real Main table.  Its `.core` equals `rowAt (mainOfTable …) i`. -/
@[reducible]
noncomputable def mainRowWithRomSub
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions) :
    ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    trace.program trace.mainTable i.val

/-- Construction-chosen bus: the three real Main memory-bus emissions
    (rs1 read, rs2 read, rd write) of the honest unified row.  The
    `m0..m2` shape facts are then `rfl`. -/
@[reducible]
noncomputable def busSub
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (execRow : List (Interaction.ExecutionBusEntry FGL)) :
    ZiskFv.Compliance.BusRows where
  exec_row := execRow
  e0 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.aMemMessage (mainRowWithRomSub trace binding i)) (-1) 1
  e1 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomSub trace binding i)) (-1) 1
  e2 := ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSub trace binding i)) 1 1

/-- Sound SUB construction: from the accepted trace + honest residual
    binders, conclude the canonical `execute (RTYPE SUB) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 SUB budget, 17 +
    `execRow`):
    * (b) decode pins (4): `h_main_op`, `h_main_active`, `h_m32`, `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder (NOT construction-chosen, so the hypotheses are
      not vacuous).

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.channels_balanced`), row shape, circuit-internal rd arithmetic, the MemBus
    `m0..m2` shape, `h_lane_rd`, and the lane→Sail binding facts. -/
theorem construction_sub_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (sub_input : PureSpec.SubInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SUB)
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
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok sub_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok sub_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sub_input.PC)
    (h_input_rd : sub_input.rd = regidx_to_fin rd)
    -- (b) lane bridges
    (h_a_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r2)))
    -- (c) exec artifacts: the exec row is a genuine top-level binder
    -- (foreign `bus_effect`/`ExecutionBusEntry` bookkeeping, no ZisK
    -- counterpart) — NOT construction-chosen, so the hypotheses are not
    -- vacuous.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC)
    (h_rd_idx :
      sub_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SUB))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_staticBinary_provider_row_matches_sub_from_binding
      trace binding i h_main_active h_main_op
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SUB :=
    ⟨h_main_active, h_main_op⟩
  -- (a) lane-rd, derived from store_pc = 0 (no record consumed)
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, binding.mainTable_index i⟩
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
        trace.program trace.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row] at h
    simpa [bus, busSub, ZiskFv.AirsClean.Main.validOfRow,
      ZiskFv.AirsClean.Main.rowAt] using h
  -- promises bundle: Sail reads + exec artifacts as binders;
  -- MemBus `m0..m2` shape derived by `rfl`.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
      (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
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
  -- Provider correctness facts, recomputed from the table Spec.
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
  -- m32 = 0 on `m` at `i.val` (needed by the lane-packing lemmas)
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  -- Derive the all-byte-matches fact from the provider match + Spec.
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_SUB : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_SUB, ZiskFv.Trusted.OP_SUB] using
      h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_SUB (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_SUB])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_SUB h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_SUB :=
    allByteMatchesOfStaticOut64_local h_out
  -- Lane → Sail binding: from lane bridges (binders) + provider match.
  have h_input_r1_row :
      sub_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) sub_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      sub_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) sub_input.r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.Compliance.equiv_SUB
    state sub_input r1 r2 rd m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_r2_row h_lane_rd promises

end ZiskFv.Compliance
