import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Wrappers.And

/-!
# Sound AND construction (`construction_and_sound`)

The second honest sound construction in the P4 closeout (PR3). It is the
mechanical mirror of `construction_sub_sound` (`ZiskFv/Compliance/ConstructionSub.lean`)
for the logic family: it assembles the canonical AND conclusion
(`execute (RTYPE AND) = (bus_effect …).2`) from an accepted full-ensemble trace
plus an explicit, named, top-level set of residual binders — with **no**
`*RowBinding` / `MainRowProvenance` record carrying any fact.

The only structural differences from `construction_sub_sound` are:

* the op-bus provider match is derived from the **salvaged logic Layer-A**
  wrapper `exists_staticBinary_provider_row_matches_logic_from_binding`
  (which serves AND / OR / XOR; it takes the op pin as the disjunction
  `op = OP_AND ∨ op = OP_OR ∨ op = OP_XOR`, here discharged by `Or.inl`),
* the op literal is `OP_AND` (`14`, still `< 16`, so the same
  `logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` / `BinaryTable.OP_AND`
  byte-chain path applies — a **different data-effect chain** than SUB's
  borrow-byte arithmetic, bottoming in the bitwise-AND byte rule), and
* the final call is `ZiskFv.Compliance.equiv_AND`, concluding with `rop.AND`
  / `execute_RTYPE_and_pure` instead of `rop.SUB` / `execute_RTYPE_sub_pure`.

Everything else — `busSub` / `mainRowWithRomSub` (op-agnostic), the `row_eq` /
booleanity derivation, the circuit-internal arithmetic derivation, the MemBus
`m0..m2` `rfl` shape, the lane→Sail binding via `input_r{1,2}_packed_{a,b}_row`,
and the residual budget — is reused verbatim.

## The honest decomposition (PLAN_ENDGAME_P4_SPINE.md §2)

An AND envelope's content splits into the same three buckets as SUB:

* **(a) derived** — proven inside the body, NOT a binder:
  - op-bus provider match (from `trace.balanced`, via the salvaged logic
    Layer-A wrapper, bottoming in an axiom-free Layer-B permutation theorem),
  - row shape (`mainOfTable` / `rowAt_mainOfTable`),
  - circuit-internal rd arithmetic (the already-proven packed byte-chain lemmas;
    AND's data effect bottoms in `binary_and_chunks_eq_bv_and_of_wf` inside
    `equiv_AND_of_static_row`),
  - MemBus `m0..m2` write shape (`by rfl` off the real trace row),
  - `h_lane_rd` (from `store_pc = 0`),
  - and the lane→Sail binding facts `h_input_r1_row` / `h_input_r2_row`.

* **(b) named residual** — explicit top-level binders:
  - decode pins (4): `h_main_op` (= `OP_AND`), `h_main_active`, `h_m32`,
    `h_store_pc`
  - Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
    `h_input_rd`, `h_rd_idx`
  - lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
  - control-flow next-PC (1): `h_nextPC_matches`
    (blocked by the cross-row Clean-model ceiling — filed prerequisite #100).

* **(c) artifact** — pure `bus_effect`/`ExecutionBusEntry` bookkeeping:
  - exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`,
  - PLUS the genuine `execRow : List (ExecutionBusEntry FGL)` **∀-binder**.

## Residual budget: EXACTLY 17 + execRow

Identical to `construction_sub_sound`: `4 + 5 + 4 + 1 + 3 = 17` hypothesis
binders, plus the genuine `execRow` universally-quantified binder. No
`MainRowProvenance` / `SubRowBinding` leaf anywhere in the binder set.

## Anti-vacuity (PLAN §4.9)

`execRow` MUST be a genuine top-level ∀-binder. The bus consumed by the exec
hypotheses is built from the real trace row (`busSub`), NOT chosen to trivialize
a hypothesis — exactly as in SUB.

## Axioms

`construction_and_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**. As with
every canonical theorem in this project, its closure still includes the
Sail-translation axioms and the Lean-kernel postulates as documented external
trust.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- Sound AND construction: from the accepted trace + honest residual
    binders, conclude the canonical `execute (RTYPE AND) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 logic budget, 17 +
    `execRow`):
    * (b) decode pins (4): `h_main_op` (= `OP_AND`), `h_main_active`, `h_m32`,
      `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder (NOT construction-chosen, so the hypotheses are
      not vacuous).

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.balanced`, via the salvaged logic wrapper), row shape,
    circuit-internal rd arithmetic, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail binding facts. -/
theorem construction_and_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (and_input : PureSpec.AndInput)
    (r1 r2 rd : regidx)
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
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok and_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok and_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some and_input.PC)
    (h_input_rd : and_input.rd = regidx_to_fin rd)
    -- (b) lane bridges
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
    (h_b_lo_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding.stateAt i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).b_1 i.val =
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
        = (PureSpec.execute_RTYPE_and_pure and_input).nextPC)
    (h_rd_idx :
      and_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.AND))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.balanced` via the salvaged
  -- logic wrapper (serves AND / OR / XOR; op pin given as the AND disjunct).
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
  -- promises bundle: Sail reads + exec artifacts as binders;
  -- MemBus `m0..m2` shape derived by `rfl`.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
      (PureSpec.execute_RTYPE_and_pure and_input).nextPC
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
  -- Lane → Sail binding: from lane bridges (binders) + provider match.
  have h_input_r1_row :
      and_input.r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) and_input.r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      and_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) and_input.r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.Compliance.equiv_AND
    state and_input r1 r2 rd m providerTable providerRow i.val bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_r2_row h_lane_rd promises

end ZiskFv.Compliance
