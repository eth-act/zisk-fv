import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Wrappers.Sll
import ZiskFv.Compliance.Wrappers.Srl
import ZiskFv.Compliance.Wrappers.Sra
import ZiskFv.Compliance.Wrappers.Slli
import ZiskFv.Compliance.Wrappers.Srli
import ZiskFv.Compliance.Wrappers.Srai
import ZiskFv.Compliance.Wrappers.Shift
import ZiskFv.Compliance.Wrappers.ShiftR
import ZiskFv.Compliance.Wrappers.ShiftRA
import ZiskFv.Compliance.Wrappers.ShiftLI
import ZiskFv.Compliance.Wrappers.ShiftRLI
import ZiskFv.Compliance.Wrappers.ShiftRAI

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
   `main_request_shift_provided` (which serves
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
    `trace.channels_balanced`, via the salvaged shift Layer-A wrapper), the BinaryExtension
    wf/byte facts, `op_is_shift = 1`, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail bindings `h_input_r1_row` / `h_shift_pin_row` (m32 = 0 route). -/
theorem construction_sll_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (sll_input : PureSpec.SllInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SLL)
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
        = EStateM.Result.ok sll_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok sll_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some sll_input.PC)
    (h_input_rd : sll_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC)
    (h_rd_idx :
      sll_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SLL)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inl h_main_op)
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
    `trace.channels_balanced`, via the salvaged shift Layer-A wrapper), the BinaryExtension
    wf/byte facts, `op_is_shift = 1`, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail bindings `h_input_r1_row` / `h_shift_pin_row` (m32 = 0 route). -/
theorem construction_srl_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (srl_input : PureSpec.SrlInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRL)
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
        = EStateM.Result.ok srl_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok srl_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some srl_input.PC)
    (h_input_rd : srl_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC)
    (h_rd_idx :
      srl_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inl h_main_op))
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
    `trace.channels_balanced`, via the salvaged shift Layer-A wrapper), the BinaryExtension
    wf/byte facts, `op_is_shift = 1`, the MemBus `m0..m2` shape, `h_lane_rd`, and
    the lane→Sail bindings `h_input_r1_row` / `h_shift_pin_row` (m32 = 0 route). -/
theorem construction_sra_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (sra_input : PureSpec.SraInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRA)
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
        = EStateM.Result.ok sra_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok sra_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some sra_input.PC)
    (h_input_rd : sra_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC)
    (h_rd_idx :
      sra_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced`
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inr (Or.inl h_main_op)))
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
theorem construction_slli_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SLL)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is an immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok slli_input.r1_val (binding i))
    (h_input_shamt : slli_input.shamt = shamt)
    (h_input_pc : (binding i).regs.get? Register.PC = .some slli_input.PC)
    (h_input_rd : slli_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inl h_main_op)
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL :=
    ⟨h_main_active, h_main_op⟩
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
theorem construction_srli_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (srli_input : PureSpec.SrliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRL)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is an immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok srli_input.r1_val (binding i))
    (h_input_shamt : srli_input.shamt = shamt)
    (h_input_pc : (binding i).regs.get? Register.PC = .some srli_input.PC)
    (h_input_rd : srli_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRLI)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inl h_main_op))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL :=
    ⟨h_main_active, h_main_op⟩
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
theorem construction_srai_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRA)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 0)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is an immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok srai_input.r1_val (binding i))
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_pc : (binding i).regs.get? Register.PC = .some srai_input.PC)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inr (Or.inl h_main_op)))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA :=
    ⟨h_main_active, h_main_op⟩
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

/-! ## m32 = 1 W-shift sibling helpers (PLAN §PR6b)

The W-shifts (SLLW/SRLW/SRAW + their I-forms) live in the **m32 = 1**
sub-group. Their lane→Sail binding closes the high-lane `(1 - m32) * a_1`
term by `ring` (NOT `one_sub_zero_mul`), takes the **low 32 bits** of the
operand via `Sail.BitVec.extractLsb _ 31 0`, and masks the shift amount to
the low **5** bits (`% 32`). These three opaque-`row` helpers mirror the
m32 = 0 trio above but route through the m32 = 1 bridge lemmas
`packed_a_lo32_eq_of_shift_match_m32_1_of_a_range` (`:402`, `ring`),
`shift_pin_w_eq_of_shift_match_of_b0_range` (`:452`, register `% 32`), and
`shift_pin_w_immediate_eq_of_shift_match_of_b0_range` (`:503`, immediate).
-/

/-- Shared lane→Sail binding for the m32 = 1 W-shift group, opaque `row`.
    Mirrors `shift_m32_0_input_r1_row_of_facts` but projects the 32-bit
    low-half operand: `(extractLsb r1_val 31 0).toNat = rowA32 row`, via the
    m32 = 1 bridge `packed_a_lo32_eq_of_shift_match_m32_1_of_a_range` (the
    `ring` route). -/
theorem shift_m32_1_input_r1_row_of_facts
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ) (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_m32 : m.m32 r_main = 1)
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
    (Sail.BitVec.extractLsb r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
      ZiskFv.AirsClean.BinaryExtension.rowA32 row := by
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
    ZiskFv.EquivCore.Bridge.BinaryExtension.packed_a_lo32_eq_of_shift_match_m32_1_of_a_range
      m v r_main 0 rs1 r1_val
      h_m32 h_a_lo_t h_a_hi_t h_read_r1 h_op_is_shift h_match_v h_a_range
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowA32] using h

/-- Companion shift-amount pin for the m32 = 1 **register** W-shift group
    (SLLW/SRLW/SRAW): `r2_val.toNat % 32 = rowShiftAmount32 row`. Opaque
    `row`. The m32 = 1 bridge `shift_pin_w_eq_of_shift_match_of_b0_range`
    yields `(extractLsb r2_val 31 0).toNat % 32 = free_in_b % 32`; the
    low-5-bit mask is invariant under taking the low 32 bits, so this
    rewrites the LHS to `r2_val.toNat % 32` via the same `extractLsb`-to-
    `% 2^32` lemma the bridge uses internally. -/
theorem shift_m32_1_shift_pin_row_of_facts
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ) (rs2 : Fin 32) (r2_val : BitVec 64)
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
    r2_val.toNat % 32 = ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32 row := by
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
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_w_eq_of_shift_match_of_b0_range
      m v r_main 0 rs2 r2_val
      h_b_lo_t h_b_hi_t h_read_r2 h_op_is_shift h_match_v h_bytes h_wfs h_b0_lt
  -- bridge LHS is `(extractLsb r2_val 31 0).toNat % 32`; the low 5 bits are
  -- preserved by the low-32 extract, so it equals `r2_val.toNat % 32`.
  have h_extract :
      (Sail.BitVec.extractLsb r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = r2_val.toNat % 2 ^ 32 := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
          BitVec.toNat_ofNat, Nat.mod_mod_of_dvd]
  rw [h_extract] at h
  rw [Nat.mod_mod_of_dvd _ (by decide : (32 : ℕ) ∣ 2 ^ 32)] at h
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32] using h

/-- Shift-amount pin for the m32 = 1 **immediate** W-shift group
    (SLLIW/SRLIW/SRAIW): `shamt.toNat = rowShiftAmount32 row` for a 5-bit
    immediate `shamt`. The `b_0` lane is pinned to `shamt_w_b_lo shamt`
    (a decode pin against the immediate). Opaque `row`; mirrors
    `shift_pin_w_immediate_eq_of_shift_match_of_b0_range`. -/
theorem shift_m32_1_imm_shift_pin_row_of_facts
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL)
    (r_main : ℕ) (shamt : BitVec 5)
    (h_b_lo_t : m.b_0 r_main = shamt_w_b_lo shamt)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage row) 1))
    (h_facts : ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts row)
    (h_b0_range : ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact row)
    (h_op_is_shift : (ZiskFv.AirsClean.BinaryExtension.validOfRow row).op_is_shift 0 = 1) :
    shamt.toNat = ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32 row := by
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
    ZiskFv.EquivCore.Bridge.BinaryExtension.shift_pin_w_immediate_eq_of_shift_match_of_b0_range
      m v r_main 0 shamt h_b_lo_t h_op_is_shift h_match_v h_bytes h_wfs h_b0_lt
  simpa [v, ZiskFv.AirsClean.BinaryExtension.validOfRow,
    ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32] using h

/-- Sound SLLW construction (m32 = 1 W-shift exemplar). The DELTA from
    `construction_sll_sound`: m32 = 1 (not 0), so the lane→Sail binding uses
    the m32 = 1 `ring`-route helper `shift_m32_1_input_r1_row_of_facts`
    (yielding the 32-bit low-half operand `(extractLsb r1_val 31 0).toNat =
    rowA32 row`) and the `% 32` register shift-pin
    `shift_m32_1_shift_pin_row_of_facts`; the op pin is `OP_SLL_W` (the 4th
    disjunct of the shared 6-way Layer-A wrapper); the Sail form is `RTYPEW`,
    sign-extending the 32-bit shift result to 64. Conclusion is the bare
    `execute_instruction (RTYPEW SLLW) = (bus_effect …).2`.

    Honest top-level residual binders (the validated §2 budget, 17 + `execRow`):
    same 17 named residuals + `execRow` as `construction_sll_sound`, with the
    op pin pinned to `OP_SLL_W`, `h_m32` pinned to 1, and the next-PC against
    `execute_RTYPE_sllw_pure`. -/
theorem construction_sllw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SLL_W)
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
        = EStateM.Result.ok sllw_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok sllw_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some sllw_input.PC)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC)
    (h_rd_idx :
      sllw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- abbreviations
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  -- (a) op-bus provider match, derived from `trace.channels_balanced`. SLLW = 4th
  -- disjunct of the shared shift Layer-A wrapper.
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))
  -- decode pins bundle
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL_W :=
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
      state sllw_input.r1_val sllw_input.r2_val sllw_input.rd sllw_input.PC
      (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC
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
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := h_m32
  -- op-is-shift, lane → Sail bindings (m32 = 1 route), via the opaque-`row`
  -- helper lemmas. Op pin selected by the 4th disjunct (SLL_W).
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op])))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) sllw_input.r1_val
      h_m32_one h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_shift_pin_row_of_facts m _ i.val (regidx_to_fin r2) sllw_input.r2_val
      h_b_lo_t h_b_hi_t h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  exact ZiskFv.Compliance.equiv_SLLW
    state sllw_input r1 r2 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRLW construction (m32 = 1 W-shift; literal swap of SLLW). DELTA
    from `construction_sllw_sound`: op pin `OP_SRL_W` (5th disjunct of the
    shared Layer-A wrapper), `ropw.SRLW`, `execute_RTYPE_srlw_pure`. Same
    m32 = 1 lane (`ring`) + `% 32` register shift-pin route. -/
theorem construction_srlw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRL_W)
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
        = EStateM.Result.ok srlw_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok srlw_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some srlw_input.PC)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_rd_idx :
      srlw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL_W :=
    ⟨h_main_active, h_main_op⟩
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
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state srlw_input.r1_val srlw_input.r2_val srlw_input.rd srlw_input.PC
      (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
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
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) srlw_input.r1_val
      h_m32_one h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_shift_pin_row_of_facts m _ i.val (regidx_to_fin r2) srlw_input.r2_val
      h_b_lo_t h_b_hi_t h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRLW
    state srlw_input r1 r2 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRAW construction (m32 = 1 W signed shift; literal swap of SLLW).
    DELTA from `construction_sllw_sound`: op pin `OP_SRA_W` (6th disjunct of
    the shared Layer-A wrapper), `ropw.SRAW`, `execute_RTYPE_sraw_pure`. Same
    m32 = 1 lane (`ring`) + `% 32` register shift-pin route. -/
theorem construction_sraw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (sraw_input : PureSpec.SrawInput)
    (r1 r2 rd : regidx)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRA_W)
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
        = EStateM.Result.ok sraw_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok sraw_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some sraw_input.PC)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
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
        = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC)
    (h_rd_idx :
      sraw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA_W :=
    ⟨h_main_active, h_main_op⟩
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
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      state sraw_input.r1_val sraw_input.r2_val sraw_input.rd sraw_input.PC
      (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC
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
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_one : m.m32 i.val = 1 := h_m32
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) sraw_input.r1_val
      h_m32_one h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_shift_pin_row_of_facts m _ i.val (regidx_to_fin r2) sraw_input.r2_val
      h_b_lo_t h_b_hi_t h_input_r2 h_match h_shift_facts.1 h_shift_facts.2
      h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRAW
    state sraw_input r1 r2 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SLLIW construction (m32 = 1 W immediate-shift exemplar). The DELTA
    from `construction_sllw_sound`: the second operand is the 5-bit immediate
    `slliw_input.shamt`, not a register read. So r2's Sail read + its hi-lane
    bridge are dropped, the `b_0` lane is pinned to `shamt_w_b_lo
    slliw_input.shamt` (a decode pin against the 5-bit immediate), the
    promises bundle is `ShiftWImmPromises` (no `input_shamt_eq` field — the
    immediate is carried directly), and the shift-amount pin is derived via
    `shift_m32_1_imm_shift_pin_row_of_facts`. Conclusion is the bare
    `execute_instruction (SHIFTIWOP SLLIW) = (bus_effect …).2`.

    Residual budget: 15 hyp binders + `execRow` (vs the W-register variant's
    17 + execRow): drop `h_input_r2`/`h_b_hi_t`; the `b_0` decode pin against
    `slliw_input.shamt` replaces the register `h_b_lo_t`. The 5-bit immediate
    rides inside `slliw_input`, so it is NOT a separate top-level binder. -/
theorem construction_slliw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SLL_W)
    (h_main_active :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).is_external_op
        i.val = 1)
    (h_m32 :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).m32
        i.val = 1)
    (h_store_pc :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).store_pc
        i.val = 0)
    -- (b) Sail reads + operands (no r2 read; shamt is a 5-bit immediate)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok slliw_input.r1_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some slliw_input.PC)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    -- (b) lane bridges (a-lanes for r1; the b_0 lane is a decode pin on shamt)
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
        shamt_w_b_lo slliw_input.shamt)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC)
    (h_rd_idx :
      slliw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inr (Or.inr (Or.inl h_main_op))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SLL_W :=
    ⟨h_main_active, h_main_op⟩
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
  let promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
      state slliw_input.r1_val slliw_input.rd slliw_input.PC
      (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
      r1 rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
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
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op])))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) slliw_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_imm_shift_pin_row_of_facts m _ i.val slliw_input.shamt
      h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  exact ZiskFv.Compliance.equiv_SLLIW
    state slliw_input r1 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRLIW construction (m32 = 1 W immediate-shift; literal swap of
    SLLIW). DELTA: op pin `OP_SRL_W` (5th disjunct), `sopw.SRLIW`,
    `execute_SHIFTIWOP_srliw_pure`. -/
theorem construction_srliw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRL_W)
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
        = EStateM.Result.ok srliw_input.r1_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some srliw_input.PC)
    (h_input_rd : srliw_input.rd = regidx_to_fin rd)
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
        shamt_w_b_lo srliw_input.shamt)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC)
    (h_rd_idx :
      srliw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRL_W :=
    ⟨h_main_active, h_main_op⟩
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
  let promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
      state srliw_input.r1_val srliw_input.rd srliw_input.PC
      (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
      r1 rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
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
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) srliw_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_imm_shift_pin_row_of_facts m _ i.val srliw_input.shamt
      h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRLIW
    state srliw_input r1 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

/-- Sound SRAIW construction (m32 = 1 W signed immediate-shift; literal swap
    of SLLIW). DELTA: op pin `OP_SRA_W` (6th disjunct), `sopw.SRAIW`,
    `execute_SHIFTIWOP_sraiw_pure`. -/
theorem construction_sraiw_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace)
    (i : Fin trace.numInstructions)
    (sraiw_input : PureSpec.SraiwInput)
    (r1 rd : regidx)
    (h_main_op :
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).op
        i.val = ZiskFv.Trusted.OP_SRA_W)
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
        = EStateM.Result.ok sraiw_input.r1_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some sraiw_input.PC)
    (h_input_rd : sraiw_input.rd = regidx_to_fin rd)
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
        shamt_w_b_lo sraiw_input.shamt)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC)
    (h_rd_idx :
      sraiw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr) :
    execute_instruction
      (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSub trace binding i execRow
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_shift_provided
      trace i h_main_active
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main_op)))))
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_SRA_W :=
    ⟨h_main_active, h_main_op⟩
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
  let promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
      state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
      (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
      r1 rd bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { input_r1_eq := h_input_r1
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
  have h_op_is_shift :=
    shift_op_is_shift_of_facts m _ i.val h_match h_shift_facts.1
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (by rw [shift_op_pin_eq_of_match m _ i.val h_match, h_main_op]))))))
  have h_input_r1_row :=
    shift_m32_1_input_r1_row_of_facts m _ i.val (regidx_to_fin r1) sraiw_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1 h_match h_shift_facts.1 h_op_is_shift
  have h_shift_pin_row :=
    shift_m32_1_imm_shift_pin_row_of_facts m _ i.val sraiw_input.shamt
      h_b_lo_t h_match h_shift_facts.1 h_shift_facts.2 h_op_is_shift
  exact ZiskFv.Compliance.equiv_SRAIW
    state sraiw_input r1 rd m providerTable providerRow i.val bus
    promises pins h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

end ZiskFv.Compliance
