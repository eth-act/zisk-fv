import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Wrappers.Sll
import ZiskFv.Compliance.Wrappers.Srl
import ZiskFv.Compliance.Wrappers.Sra
import ZiskFv.Compliance.Wrappers.Slli
import ZiskFv.Compliance.Wrappers.Srli
import ZiskFv.Compliance.Wrappers.Srai

/-!
# Sound shift constructions (`construction_{sll,srl,sra,slli,srli,srai}_sound`)

Sweep Wave 3 of the P4 closeout (PLAN_ENDGAME_P4_SWEEP.md §PR6, m32 = 0 group).
These six honest sound constructions assemble the canonical conclusions for the
m32 = 0 shift family — `execute_instruction (RTYPE/SHIFTIOP …) = (bus_effect …).2`
— from an accepted full-ensemble trace plus an explicit, named, top-level set of
residual binders, with **no** `*RowBinding` / `MainRowProvenance` record carrying
any fact.

## Why the shifts differ from SUB/AND (PLAN §PR6)

The shifts are a **separate template instantiation**, not the
`busSub` / `staticLookupComponent` path:

1. **BinaryExtension provider, not staticBinary.** The op-bus provider match is
   derived from the salvaged shift Layer-A wrapper
   `exists_binaryExtension_provider_row_matches_shift_from_binding` (which serves
   all twelve shifts; it takes the op pin as the 6-way disjunction
   `OP_SLL ∨ OP_SRL ∨ OP_SRA ∨ OP_SLL_W ∨ OP_SRL_W ∨ OP_SRA_W`, here discharged
   by the appropriate disjunct per family). The provider is
   `shiftStaticLookupComponent` and the match conclusion is in `opBusMessage`
   (rowInput) form, not the staticBinary `matches_entry` shape.

2. **Bare-execute conclusion (no `writeReg nextPC` prelude).** Unlike SUB/AND,
   whose canonical conclusion is `do writeReg nextPC; execute … = (bus_effect …).2`,
   the canonical shift conclusion is the **bare**
   `execute_instruction (…) = (bus_effect …).2`. So these constructions conclude
   `equiv_{SLL,…}`'s conclusion verbatim — there is no exec-bus prelude to carry,
   and the `nextPC_matches` residual lives inside the promises bundle against the
   bare-execute pure spec.

3. **m32 = 0 lane route via `one_sub_zero_mul`.** The lane→Sail binding
   `h_input_r1_row : r1_val = rowA64 row` is derived from the named lane bridges
   (`h_a_lo_t`/`h_a_hi_t`) + the Sail read via
   `packed_a_eq_of_shift_match_m32_0_of_a_range`
   (`EquivCore/Bridge/BinaryExtension.lean:240`), which is the
   `simp only [one_sub_zero_mul]` route (line 269) — correct for the m32 = 0
   group. (The m32 = 1 W-shifts use the `ring` route; that is a later wave.)
   The shift-amount pin `h_shift_pin_row` is derived analogously via
   `shift_pin_eq_of_shift_match_m32_0_of_b0_range` (register variants) /
   `shift_pin_immediate_eq_of_shift_match_of_b0_range` (immediate variants).

Everything else — `busSub` / `mainRowWithRomSub` (op-agnostic, reused VERBATIM
from `ConstructionSub.lean`), the `row_eq` derivation, `h_core_store_pc`,
`h_lane_rd` via `cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero`,
and the six `m*_*` MemBus `rfl` fields — is reused unchanged.

## Residual budget: EXACTLY 17 + execRow (register variants); 16 + execRow (immediate)

The register shifts (SLL/SRL/SRA) carry the same 17 + `execRow` residual budget
as SUB: 4 decode pins, 5 Sail reads + operands, 4 lane bridges, 1 next-PC, 3 exec
artifacts + the genuine `execRow` ∀-binder. The immediate shifts (SLLI/SRLI/SRAI)
drop r2's register read and its hi-lane bridge but add the `shamt : BitVec 6`
operand and pin the b_0 lane to `shamt_b_lo shamt` — the b lane bridge becomes a
single decode pin against the immediate rather than a register read + two lane
bridges.

## Anti-vacuity (PLAN §4.9)

`execRow` MUST be a genuine top-level ∀-binder. The bus consumed by the exec
hypotheses is built from the real trace row (`busSub`), NOT chosen to trivialize
a hypothesis. Hard-coding `execRow := []` would make `h_exec_len : [].length = 2`
contradictory → vacuous. The ∀-binder keeps the residual hypotheses jointly
satisfiable.

## Axioms

Each `construction_*_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**. As with
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

/-- Shared lane→Sail binding for the m32 = 0 shift group, stated against an
    **opaque** `row : BinaryExtensionRow FGL` so that `simp` does not unfold the
    giant `shiftStaticLookupComponent.rowInput …` provider term. Mirrors the
    internal block of `EquivCore.Sll.equiv_SLL_of_static_row`: it converts the
    rowInput-form op-bus match to `v = validOfRow row` form, derives the byte/wf
    facts + `op_is_shift = 1`, then applies the m32 = 0 lane bridge
    `packed_a_eq_of_shift_match_m32_0_of_a_range` (the `one_sub_zero_mul` route)
    and projects it to `rowA64 row`. Op-agnostic across the m32 = 0 shifts (the
    op pin only feeds `op_is_shift`, supplied by the caller). -/
theorem shift_m32_0_input_r1_row_of_facts
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg rs1))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_op_is_shift : (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op_is_shift 0 = 1) :
    r1_val = ZiskFv.AirsClean.BinaryExtension.rowA64 row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main)
      (opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry]
      using h_facts
  have h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v 0 := by
    obtain ⟨e0, h0, e1, h1, e2, h2, e3, h3, e4, h4, e5, h5, e6, h6, e7, h7⟩ :=
      h_bytes
    exact ⟨
      by simpa [h0.2.2.2.1] using h_wfs.1.1.1,
      by simpa [h1.2.2.2.1] using h_wfs.2.1.1.1,
      by simpa [h2.2.2.2.1] using h_wfs.2.2.1.1.1,
      by simpa [h3.2.2.2.1] using h_wfs.2.2.2.1.1.1,
      by simpa [h4.2.2.2.1] using h_wfs.2.2.2.2.1.1.1,
      by simpa [h5.2.2.2.1] using h_wfs.2.2.2.2.2.1.1.1,
      by simpa [h6.2.2.2.1] using h_wfs.2.2.2.2.2.2.1.1.1,
      by simpa [h7.2.2.2.1] using h_wfs.2.2.2.2.2.2.2.1.1 ⟩
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_eq_of_shift_match_m32_0_of_a_range
      m v r_main 0 rs1 r1_val
      h_m32 h_a_lo_t h_a_hi_t h_read_r1 h_op_is_shift h_match_v h_a_range
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowA64] using h

/-- Companion shift-amount pin for the m32 = 0 **register** shift group
    (SLL/SRL/SRA): `r2_val % 64 = rowShiftAmount row`. Opaque `row`; mirrors
    `shift_pin_eq_of_shift_match_m32_0_of_b0_range`. -/
theorem shift_m32_0_shift_pin_row_of_facts
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
    (h_m32 : m.m32 r_main = 0)
    (h_b_lo_t : m.b_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_b_hi_t : m.b_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg rs2))
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row)
    (h_op_is_shift : (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op_is_shift 0 = 1) :
    r2_val.toNat % 64 = ZiskFv.AirsClean.BinaryExtension.rowShiftAmount row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main)
      (opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry]
      using h_facts
  have h_b0_lt : (v.b_0 0).val < 2 ^ 24 := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_eq_of_shift_match_m32_0_of_b0_range
      m v r_main 0 rs2 r2_val
      h_m32 h_b_lo_t h_b_hi_t h_read_r2 h_op_is_shift h_match_v h_bytes h_wfs h_b0_lt
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount] using h

/-- Op pin in `validOfRow row` form: `(validOfRow row).op 0 = m.op r_main`,
    from the rowInput-form op-bus match. Opaque `row`. -/
theorem shift_op_pin_eq_of_match
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1)) :
    (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = m.op r_main := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main)
      (opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi m v r_main 0 h_match_v
  exact h_op_fgl.symm

/-- Op-is-shift derivation for the m32 = 0 shift group, opaque `row`: derives
    `(validOfRow row).op_is_shift 0 = 1` from the rowInput-form op-bus match,
    the wf facts, and an op-pin selector (the 6-way disjunction member). -/
theorem shift_op_is_shift_of_facts
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_op_sel :
      (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = ZiskFv.Trusted.OP_SLL
      ∨ (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = ZiskFv.Trusted.OP_SRL
      ∨ (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = ZiskFv.Trusted.OP_SRA
      ∨ (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = ZiskFv.Trusted.OP_SLL_W
      ∨ (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = ZiskFv.Trusted.OP_SRL_W
      ∨ (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op 0 = ZiskFv.Trusted.OP_SRA_W) :
    (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op_is_shift 0 = 1 := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main)
      (opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry]
      using h_facts
  exact (ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin_of_wf_hypotheses
    v 0 h_wfs).1 h_op_sel

/-- Shift-amount pin for the m32 = 0 **immediate** shift group (SLLI/SRLI/SRAI):
    `shamt.toNat = rowShiftAmount row`. The `b_0` lane is pinned to
    `shamt_b_lo shamt` (a decode pin against the immediate, not a register read).
    Opaque `row`; mirrors `shift_pin_immediate_eq_of_shift_match_of_b0_range`. -/
theorem shift_imm_shift_pin_row_of_facts
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ) (shamt : BitVec 6)
    (h_b_lo_t : m.b_0 r_main = shamt_b_lo shamt)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row)
    (h_op_is_shift : (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op_is_shift 0 = 1) :
    shamt.toNat = ZiskFv.AirsClean.BinaryExtension.rowShiftAmount row := by
  let v := ZiskFv.AirsClean.BinaryExtension.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main)
      (opBus_row_BinaryExtension v 0) := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension] using h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v 0
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes, ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry]
      using h_facts
  have h_b0_lt : (v.b_0 0).val < 2 ^ 24 := by
    simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
      ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact] using h_b0_range
  have h :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_immediate_eq_of_shift_match_of_b0_range
      m v r_main 0 shamt h_b_lo_t h_op_is_shift h_match_v h_bytes h_wfs h_b0_lt
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount] using h

/-- Sound SLL construction: from the accepted trace + honest residual binders,
    conclude the canonical bare `execute_instruction (RTYPE SLL) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 budget, 17 + `execRow`):
    * (b) decode pins (4): `h_main_op`, `h_main_active`, `h_m32`, `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.balanced`, via the salvaged shift Layer-A wrapper), the BinaryExtension
    wf/byte facts, `op_is_shift = 1`, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail bindings `h_input_r1_row` / `h_shift_pin_row` (m32 = 0 route). -/
theorem construction_sll_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SLL)
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
        = EStateM.Result.ok sll_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok sll_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sll_input.PC)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
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
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC)
    (h_rd_idx :
      sll_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_main_active (Or.inl h_main_op)
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
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
      state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
      (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
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
  -- (a) BinaryExtension provider wf/byte facts, recomputed from the table Spec.
  -- Generalize the provider rowInput term to an OPAQUE `row` so the helper
  -- lemmas below (and the final `equiv_SLL` unification) never unfold it.
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  -- op-is-shift, lane → Sail bindings (m32 = 0 route), via the opaque-`row`
  -- helper lemmas. Op pin selected by `Or.inl` (SLL).
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) sll_input.r1_val
      h_m32_zero h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin r2) sll_input.r2_val
      h_m32_zero h_b_lo_t h_b_hi_t h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  exact ZiskFv.Compliance.equiv_SLL
    state sll_input r1 r2 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRL construction: from the accepted trace + honest residual binders,
    conclude the canonical bare `execute_instruction (RTYPE SLL) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 budget, 17 + `execRow`):
    * (b) decode pins (4): `h_main_op`, `h_main_active`, `h_m32`, `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.balanced`, via the salvaged shift Layer-A wrapper), the BinaryExtension
    wf/byte facts, `op_is_shift = 1`, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail bindings `h_input_r1_row` / `h_shift_pin_row` (m32 = 0 route). -/
theorem construction_srl_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (srl_input : PureSpec.SrlInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRL)
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
        = EStateM.Result.ok srl_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok srl_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srl_input.PC)
    (h_input_rd : srl_input.rd = regidx_to_fin rd)
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
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC)
    (h_rd_idx :
      srl_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_main_active (Or.inr (Or.inl h_main_op))
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
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
      state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
      (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
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
  -- (a) BinaryExtension provider wf/byte facts, recomputed from the table Spec.
  -- Generalize the provider rowInput term to an OPAQUE `row` so the helper
  -- lemmas below (and the final `equiv_SRL` unification) never unfold it.
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  -- op-is-shift, lane → Sail bindings (m32 = 0 route), via the opaque-`row`
  -- helper lemmas. Op pin selected per family (SRL).
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op])))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) srl_input.r1_val
      h_m32_zero h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin r2) srl_input.r2_val
      h_m32_zero h_b_lo_t h_b_hi_t h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRL
    state srl_input r1 r2 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRA construction: from the accepted trace + honest residual binders,
    conclude the canonical bare `execute_instruction (RTYPE SLL) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 budget, 17 + `execRow`):
    * (b) decode pins (4): `h_main_op`, `h_main_active`, `h_m32`, `h_store_pc`
    * (b) Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
      `h_input_rd`, `h_rd_idx`
    * (b) lane bridges (4): `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
    * (b)-pending-infra (1): `h_nextPC_matches`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `execRow` ∀-binder.

    Derived inside the body (NOT binders): op-bus provider match (from
    `trace.balanced`, via the salvaged shift Layer-A wrapper), the BinaryExtension
    wf/byte facts, `op_is_shift = 1`, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail bindings `h_input_r1_row` / `h_shift_pin_row` (m32 = 0 route). -/
theorem construction_sra_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (sra_input : PureSpec.SraInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRA)
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
        = EStateM.Result.ok sra_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok sra_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some sra_input.PC)
    (h_input_rd : sra_input.rd = regidx_to_fin rd)
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
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC)
    (h_rd_idx :
      sra_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_main_active (Or.inr (Or.inr (Or.inl h_main_op)))
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
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
      state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
      (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
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
  -- (a) BinaryExtension provider wf/byte facts, recomputed from the table Spec.
  -- Generalize the provider rowInput term to an OPAQUE `row` so the helper
  -- lemmas below (and the final `equiv_SRA` unification) never unfold it.
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  -- op-is-shift, lane → Sail bindings (m32 = 0 route), via the opaque-`row`
  -- helper lemmas. Op pin selected per family (SRA).
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) sra_input.r1_val
      h_m32_zero h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_0_shift_pin_row_of_facts m _ i.val (regidx_to_fin r2) sra_input.r2_val
      h_m32_zero h_b_lo_t h_b_hi_t h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRA
    state sra_input r1 r2 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SLLI construction (m32 = 0 immediate shift exemplar). The DELTA from
    `construction_sll_sound`: the second operand is the 6-bit immediate `shamt`,
    not a register read. So r2's Sail read + its hi-lane bridge are dropped, the
    `b_0` lane is pinned to `shamt_b_lo shamt` (a decode pin against the
    immediate), the promises bundle is `ShiftImmPromises` (carrying
    `input_shamt_eq`), and the shift-amount pin is derived via
    `shift_imm_shift_pin_row_of_facts`. Conclusion is the bare
    `execute_instruction (SHIFTIOP SLLI) = (bus_effect …).2`.

    Residual budget: 16 hyp binders + `shamt` + `execRow` (vs the register
    variant's 17 + execRow): drop `h_input_r2`/`h_b_hi_t`, add `shamt` +
    `h_input_shamt`; the `b_0` decode pin replaces the register `h_b_lo_t`. -/
theorem construction_slli_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SLL)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is an immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok slli_input.r1_val (binding.stateAt i))
    (h_input_shamt : slli_input.shamt = shamt)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some slli_input.PC)
    (h_input_rd : slli_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
        shamt_b_lo shamt)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC)
    (h_rd_idx :
      slli_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_main_active (Or.inl h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
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
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
      (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
      r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_shamt_eq := h_input_shamt
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
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) slli_input.r1_val
      h_m32_zero h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      slli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val shamt
      h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  exact ZiskFv.Compliance.equiv_SLLI
    state slli_input r1 rd shamt m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRLI construction (m32 = 0 immediate shift; literal swap of SLLI). The DELTA from
    `construction_sll_sound`: the second operand is the 6-bit immediate `shamt`,
    not a register read. So r2's Sail read + its hi-lane bridge are dropped, the
    `b_0` lane is pinned to `shamt_b_lo shamt` (a decode pin against the
    immediate), the promises bundle is `ShiftImmPromises` (carrying
    `input_shamt_eq`), and the shift-amount pin is derived via
    `shift_imm_shift_pin_row_of_facts`. Conclusion is the bare
    `execute_instruction (SHIFTIOP SLLI) = (bus_effect …).2`.

    Residual budget: 16 hyp binders + `shamt` + `execRow` (vs the register
    variant's 17 + execRow): drop `h_input_r2`/`h_b_hi_t`, add `shamt` +
    `h_input_shamt`; the `b_0` decode pin replaces the register `h_b_lo_t`. -/
theorem construction_srli_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (srli_input : PureSpec.SrliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRL)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is an immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok srli_input.r1_val (binding.stateAt i))
    (h_input_shamt : srli_input.shamt = shamt)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srli_input.PC)
    (h_input_rd : srli_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
        shamt_b_lo shamt)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC)
    (h_rd_idx :
      srli_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_main_active (Or.inr (Or.inl h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
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
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
      (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
      r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_shamt_eq := h_input_shamt
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
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op])))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) srli_input.r1_val
      h_m32_zero h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      srli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val shamt
      h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRLI
    state srli_input r1 rd shamt m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRAI construction (m32 = 0 immediate shift; literal swap of SLLI). The DELTA from
    `construction_sll_sound`: the second operand is the 6-bit immediate `shamt`,
    not a register read. So r2's Sail read + its hi-lane bridge are dropped, the
    `b_0` lane is pinned to `shamt_b_lo shamt` (a decode pin against the
    immediate), the promises bundle is `ShiftImmPromises` (carrying
    `input_shamt_eq`), and the shift-amount pin is derived via
    `shift_imm_shift_pin_row_of_facts`. Conclusion is the bare
    `execute_instruction (SHIFTIOP SLLI) = (bus_effect …).2`.

    Residual budget: 16 hyp binders + `shamt` + `execRow` (vs the register
    variant's 17 + execRow): drop `h_input_r2`/`h_b_hi_t`, add `shamt` +
    `h_input_shamt`; the `b_0` decode pin replaces the register `h_b_lo_t`. -/
theorem construction_srai_sound
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.length)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRA)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is an immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok srai_input.r1_val (binding.stateAt i))
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some srai_input.PC)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
        shamt_b_lo shamt)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC)
    (h_rd_idx :
      srai_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program binding.mainTable with hm
  set state := binding.stateAt i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    exists_binaryExtension_provider_row_matches_shift_from_binding
      trace binding i h_main_active (Or.inr (Or.inr (Or.inl h_main_op)))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
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
  let promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
      state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
      (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
      r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
      input_shamt_eq := h_input_shamt
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
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inl (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))))
  have h_input_r1_row :=
    shift_m32_0_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) srai_input.r1_val
      h_m32_zero h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :
      srai_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)) := by
    rw [h_input_shamt]
    exact shift_imm_shift_pin_row_of_facts m _ i.val shamt
      h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRAI
    state srai_input r1 rd shamt m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

end ZiskFv.Compliance
