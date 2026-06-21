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


end ZiskFv.Compliance
