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

private lemma byte_ranges_of_static_match
    {op_val : ℕ} {a b c : FGL}
    (h : ZiskFv.Airs.Binary.consumer_byte_match_wf op_val a b c) :
    a.val < 256 ∧ b.val < 256 ∧ c.val < 256 := by
  obtain ⟨e, h_wf, _, h_a, h_b, h_c⟩ := h
  rcases h_wf.1 with ⟨ha, hb, hc, _⟩
  exact ⟨by simpa [h_a] using ha, by simpa [h_b] using hb,
    by simpa [h_c] using hc⟩

/-- A static Binary ADD row computes the packed 64-bit sum. -/
private lemma static_binary_add_packed
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (out : ZiskFv.EquivCore.Bridge.Binary.BinaryChainStaticOut64
      (ZiskFv.AirsClean.Binary.validOfRow row) 0
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD) :
    BitVec.ofNat 64
        (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
          + row.aBytes.free_in_a_2.val * 65536 + row.aBytes.free_in_a_3.val * 16777216
          + row.aBytes.free_in_a_4.val * 4294967296
          + row.aBytes.free_in_a_5.val * 1099511627776
          + row.aBytes.free_in_a_6.val * 281474976710656
          + row.aBytes.free_in_a_7.val * 72057594037927936)
      +
      BitVec.ofNat 64
        (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
          + row.bBytes.free_in_b_2.val * 65536 + row.bBytes.free_in_b_3.val * 16777216
          + row.bBytes.free_in_b_4.val * 4294967296
          + row.bBytes.free_in_b_5.val * 1099511627776
          + row.bBytes.free_in_b_6.val * 281474976710656
          + row.bBytes.free_in_b_7.val * 72057594037927936)
      =
      BitVec.ofNat 64
        (row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536 + row.cBytes.free_in_c_3.val * 16777216
          + row.cBytes.free_in_c_4.val * 4294967296
          + row.cBytes.free_in_c_5.val * 1099511627776
          + row.cBytes.free_in_c_6.val * 281474976710656
          + row.cBytes.free_in_c_7.val * 72057594037927936) := by
  have h_matches := allByteMatchesOfStaticOut64_local out
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨ha0, hb0, hc0⟩ := byte_ranges_of_static_match h0
  obtain ⟨ha1, hb1, hc1⟩ := byte_ranges_of_static_match h1
  obtain ⟨ha2, hb2, hc2⟩ := byte_ranges_of_static_match h2
  obtain ⟨ha3, hb3, hc3⟩ := byte_ranges_of_static_match h3
  obtain ⟨ha4, hb4, hc4⟩ := byte_ranges_of_static_match h4
  obtain ⟨ha5, hb5, hc5⟩ := byte_ranges_of_static_match h5
  obtain ⟨ha6, hb6, hc6⟩ := byte_ranges_of_static_match h6
  obtain ⟨ha7, hb7, hc7⟩ := byte_ranges_of_static_match h7
  exact ZiskFv.Airs.Binary.binary_add_chunks_eq_bv_add_of_wf
    row.aBytes.free_in_a_0 row.aBytes.free_in_a_1 row.aBytes.free_in_a_2 row.aBytes.free_in_a_3
    row.aBytes.free_in_a_4 row.aBytes.free_in_a_5 row.aBytes.free_in_a_6 row.aBytes.free_in_a_7
    row.bBytes.free_in_b_0 row.bBytes.free_in_b_1 row.bBytes.free_in_b_2 row.bBytes.free_in_b_3
    row.bBytes.free_in_b_4 row.bBytes.free_in_b_5 row.bBytes.free_in_b_6 row.bBytes.free_in_b_7
    row.cBytes.free_in_c_0 row.cBytes.free_in_c_1 row.cBytes.free_in_c_2 row.cBytes.free_in_c_3
    row.cBytes.free_in_c_4 row.cBytes.free_in_c_5 row.cBytes.free_in_c_6 row.cBytes.free_in_c_7
    0 row.chain.carry_0 row.chain.carry_1 row.chain.carry_2
    row.chain.carry_3 row.chain.carry_4 row.chain.carry_5 row.chain.carry_6
    (ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_0)
    (ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_1)
    (ZiskFv.AirsClean.Binary.lookupFlags012Row row row.chain.carry_2)
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_3)
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_4)
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_5)
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row row row.chain.carry_6)
    (ZiskFv.AirsClean.Binary.lookupFlags7Row row)
    (2 * row.mode.use_first_byte) 0 0 row.mode.mode32 0 0 0 (1 - row.mode.mode32)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_ne
    out.pi4_ne out.pi5_ne out.pi6_ne out.pi7_eq

/-- Circuit-only ADD semantics from the static Binary provider shape. -/
theorem main_add_packed_result_of_static_provider
    (m : Valid_Main FGL FGL)
    (i : Nat)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (h_op : m.op i = OP_ADD)
    (h_m32 : m.m32 i = 0)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_spec : ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts row)
    (h_match : matches_entry
      (opBus_row_Main m i)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1)) :
    BitVec.ofNat 64
        ((m.c_0 i).val + (m.c_1 i).val * 4294967296)
      =
      BitVec.ofNat 64
        ((m.a_0 i).val + (m.a_1 i).val * 4294967296)
      +
      BitVec.ofNat 64
        ((m.b_0 i).val + (m.b_1 i).val * 4294967296) := by
  have h_emit : row.chain.b_op + 16 * row.mode.mode32 =
      (ZiskFv.Airs.Tables.BinaryTable.OP_ADD : FGL) := by
    have hm := h_match
    simp only [matches_entry, opBus_row_Main] at hm
    rw [← hm.2.1]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_ADD, OP_ADD] using h_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      row h_spec ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (by simp [ZiskFv.Airs.Tables.BinaryTable.OP_ADD]) h_core h_emit
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core h_row_m32 h_bop
  have h_carry_bool :
      row.chain.carry_7 * (1 - row.chain.carry_7) = 0 := by
    simpa [ZiskFv.AirsClean.Binary.validOfRow] using h_core.2.1
  have h_matches := allByteMatchesOfStaticOut64_local out
  have ha := ZiskFv.EquivCore.Bridge.Binary.main_a_packing_of_match
    m row i h_matches h_m32 h_match
  have hb := ZiskFv.EquivCore.Bridge.Binary.main_b_packing_of_match
    m row i h_matches h_m32 h_match
  have hcarry : row.chain.carry_7 = 0 := by
    exact ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_ADD_of_static_chain
      (ZiskFv.AirsClean.Binary.validOfRow row) 0 out h_core h_carry_bool
  have hflag : m.flag i = 0 := by
    have hm := h_match
    simp only [matches_entry, opBus_row_Main] at hm
    exact hm.2.2.2.2.2.2.2.2.1.trans hcarry
  obtain ⟨hc0, hc1⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.main_c_lanes_carryfree_of_match
      m row i h_match hflag
  rcases h_matches with ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩
  obtain ⟨_, _, hc0_lt⟩ := byte_ranges_of_static_match hm0
  obtain ⟨_, _, hc1_lt⟩ := byte_ranges_of_static_match hm1
  obtain ⟨_, _, hc2_lt⟩ := byte_ranges_of_static_match hm2
  obtain ⟨_, _, hc3_lt⟩ := byte_ranges_of_static_match hm3
  obtain ⟨_, _, hc4_lt⟩ := byte_ranges_of_static_match hm4
  obtain ⟨_, _, hc5_lt⟩ := byte_ranges_of_static_match hm5
  obtain ⟨_, _, hc6_lt⟩ := byte_ranges_of_static_match hm6
  obtain ⟨_, _, hc7_lt⟩ := byte_ranges_of_static_match hm7
  have hc_lo_lt :
      row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536
        + row.cBytes.free_in_c_3.val * 16777216 < GL_prime := by omega
  have hc_hi_lt :
      row.cBytes.free_in_c_4.val + row.cBytes.free_in_c_5.val * 256
        + row.cBytes.free_in_c_6.val * 65536
        + row.cBytes.free_in_c_7.val * 16777216 < GL_prime := by omega
  rw [hc0, hc1, ha, hb]
  simp only [Fin.val_add, Fin.val_mul]
  norm_num at ⊢
  rw [Nat.mod_eq_of_lt hc_lo_lt, Nat.mod_eq_of_lt hc_hi_lt]
  simpa [Nat.add_assoc, Nat.mul_assoc, Nat.mul_add, Nat.add_mul] using
    (static_binary_add_packed row out).symm

/-- Circuit-only ADD semantics from the dedicated BinaryAdd provider shape. -/
theorem main_add_packed_result_of_binaryadd_provider
    (m : Valid_Main FGL FGL)
    (i : Nat)
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (h_m32 : m.m32 i = 0)
    (h_facts : ZiskFv.AirsClean.BinaryAdd.ComponentSpecFacts row)
    (h_match : matches_entry
      (opBus_row_Main m i)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage row) 1)) :
    BitVec.ofNat 64
        ((m.c_0 i).val + (m.c_1 i).val * 4294967296)
      =
      BitVec.ofNat 64
        ((m.a_0 i).val + (m.a_1 i).val * 4294967296)
      +
      BitVec.ofNat 64
        ((m.b_0 i).val + (m.b_1 i).val * 4294967296) := by
  have hadd :=
    ZiskFv.AirsClean.BinaryAdd.binary_add_chunks_eq_bv_add_via_component
      (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0
      (ZiskFv.AirsClean.BinaryAdd.core_every_row_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.a_chunks_in_range_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.b_chunks_in_range_of_component_spec_facts row h_facts)
      (ZiskFv.AirsClean.BinaryAdd.c_chunks_in_range_of_component_spec_facts row h_facts)
  have hm := h_match
  simp only [matches_entry, opBus_row_Main] at hm
  obtain ⟨_, _, ha0, ha1, hb0, hb1, hc0, hc1, _, _, _, _⟩ := hm
  obtain ⟨_, _, _, _, hc0_lt, hc1_lt, hc2_lt, hc3_lt⟩ := h_facts.2.2
  have hc_lo_lt :
      row.c_chunks_1.val * 65536 + row.c_chunks_0.val < GL_prime := by omega
  have hc_hi_lt :
      row.c_chunks_3.val * 65536 + row.c_chunks_2.val < GL_prime := by omega
  rw [h_m32] at ha1 hb1
  simp only [one_sub_zero_mul] at ha1 hb1
  rw [hc0, hc1, ha0, ha1, hb0, hb1]
  simp only [Fin.val_add, Fin.val_mul]
  norm_num at ⊢
  rw [Nat.mod_eq_of_lt hc_lo_lt, Nat.mod_eq_of_lt hc_hi_lt]
  have hc_pack :
      row.c_chunks_1.val * 65536 + row.c_chunks_0.val
          + (row.c_chunks_3.val * 65536 + row.c_chunks_2.val) * 4294967296
        =
      row.c_chunks_0.val + row.c_chunks_1.val * 65536
          + row.c_chunks_2.val * 4294967296
          + row.c_chunks_3.val * 281474976710656 := by omega
  rw [hc_pack]
  simpa [ZiskFv.AirsClean.BinaryAdd.validOfRow] using hadd.symm

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
    * (b) lane bridges (4): `h_a_lo`, `h_a_hi`, `h_b_lo`, `h_b_hi`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder. -/
theorem construction_add_sound_claimed_dead
    (trace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace trace.numInstructions)
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
    (h_a_lo :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_add_pure add_input).nextPC)
    (h_rd_idx :
      add_input.rd =
        Transpiler.wrap_to_regidx (busSub trace i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.ADD))) (binding i)
      = (bus_effect (busSub trace i execRow).exec_row
          [ (busSub trace i execRow).e0
          , (busSub trace i execRow).e1
          , (busSub trace i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace i execRow
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
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
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
        (mainRowWithRomSub trace i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
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
          h_matches h_m32_zero h_a_lo h_a_hi h_match h_input_r1
    have h_input_r2_row :
        add_input.r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
      simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
        ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
          m providerInput i.val (regidx_to_fin r2) add_input.r2_val
          h_matches h_m32_zero h_b_lo h_b_hi h_match h_input_r2
    exact ZiskFv.Compliance.equiv_ADD
      state add_input r1 r2 rd m
      ⟨providerTable, providerRow, h_component, h_table_spec, h_provider_row⟩
      i.val bus pins h_match
      h_input_r1_row h_input_r2_row h_lane_rd promises
  · -- BinaryAdd arm: discharge via `equiv_ADD_via_binaryadd`.
    obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    exact ZiskFv.Compliance.equiv_ADD_via_binaryadd
      state add_input r1 r2 rd m
      ⟨providerTable, providerRow, h_component, h_table_spec, h_provider_row⟩
      i.val bus pins h_match
      h_add_subset h_a_lo h_a_hi h_b_lo h_b_hi h_m32_zero
      h_lane_rd promises

/-- Sound ADDI construction (PR4, approach (a): two-arm provider case-split).

    = `construction_add_sound` + the PR3 I-type immediate delta. The op-bus is the
    SAME `staticLookup ∨ BinaryAdd` disjunction (the op-bus match is
    operand-source-agnostic); the second operand is the immediate, sourced via the
    named `h_addi_subset` (`itype_imm_subset_holds_main`) decode pin instead of an
    r2 register read. The r2 register lane bridges are dropped; `imm`, the decode
    equality `h_input_imm`, the immediate routing pin `h_addi_subset`, and the
    BinaryAdd-arm `h_set_pc` pin are added.

    Residual budget = ADD's, minus the 2 r2 lane bridges (`h_b_lo`/`h_b_hi`)
    and `h_input_r2`, plus `imm`, `h_input_imm`, `h_addi_subset`, `h_set_pc`. -/
theorem construction_addi_sound_claimed_dead
    (trace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace trace.numInstructions)
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
    (h_a_lo :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi :
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
    (h_exec_len : (busSub trace i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_rd_idx :
      addi_input.rd =
        Transpiler.wrap_to_regidx (busSub trace i execRow).e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) (binding i)
      = (bus_effect (busSub trace i execRow).exec_row
          [ (busSub trace i execRow).e0
          , (busSub trace i execRow).e1
          , (busSub trace i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace i execRow
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
      (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
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
        (mainRowWithRomSub trace i) h_core_store_pc
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt m i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub, m,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
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
          h_matches h_m32_zero h_a_lo h_a_hi h_match h_input_r1
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
      state addi_input r1 rd imm m
      ⟨providerTable, providerRow, h_component, h_table_spec, h_provider_row⟩
      i.val bus pins h_match
      h_addi_subset h_input_r1_row h_input_imm_row h_lane_rd promises
  · -- BinaryAdd arm: discharge via `equiv_ADDI_via_binaryadd`.
    obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
        h_component, h_table_spec, h_match⟩ := h_binaryadd
    exact ZiskFv.Compliance.equiv_ADDI_via_binaryadd
      state addi_input r1 rd imm m
      ⟨providerTable, providerRow, h_component, h_table_spec, h_provider_row⟩
      i.val bus pins h_match
      h_add_subset h_addi_subset h_a_lo h_a_hi h_m32_zero h_set_pc_zero
      h_lane_rd promises

end ZiskFv.Compliance
