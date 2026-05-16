import Mathlib

import ZiskFv.Equivalence.StoreD
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_SD` trust-discharge wrapper — Mem-stores shape exemplar
## Why SD

SD is the simplest store: all 8 bytes of `xreg rs2` flow through
the memory-bus entry's byte lanes verbatim, ptr-match is the
generic store-address formula `xreg rs1 + signExt(imm)`, and
there is no sign-extension or width-pin coupling. The shape's
narrower opcodes (SB / SH / SW) will reuse SD's discharge
machinery plus a width-pin closing the high byte lanes to zero.

## 5-category discharge applied

* **Lane-match.** Internalized by the new
  `main_store_emission_bundle_sd` (`MemBridge.lean`, class #4) —
  it delivers the byte-extracted form of the store entry directly
  (`(e_st.xi : BitVec 8) = BitVec.extractLsb _ _ r2_val`). The
  bundle requires `transpile_SD`-derived lane equalities as
  caller-supplied hypotheses, which the
  `Bridge.Mem.sd_discharge_full` derivation discharges from a
  Sail `read_xreg rs2` predicate (composing `transpile_SD` with
  `Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg`).
* **Mode pins.** N/A on the provider side (Mem core has no mode
  columns; the activation pins `is_external_op = 0`,
  `op = OP_COPYB` are caller-supplied at the Compliance level
  from the ROM-handshake on the row hosting SD).
* **Sign-witness pins.** N/A — SD is unsigned data movement.
* **Range/bound.** Byte ranges on the store entry are folded into
  the bundle's class-#4 envelope (the byte-form conclusion uses
  the same byte-range bus consequences as the lane-form would
  via `memory_bus_entry_byte_range_perm_sound`). The address
  range comes from the bus protocol itself; no further
  range-bus entry is consumed at this layer.
* **Operand bridges.** `read_xreg rs1` and `read_xreg rs2` are
  routed through `Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg`
  (pure-Lean, no axiom) inside the `Bridge.Mem.sd_discharge_full`
  composition.

## Anti-laundering report

* **1 new axiom.** `main_store_emission_bundle_sd`
  (`MemBridge.lean`, class #4). PIL-cited; same class as
  `main_load_emission_bundle` /
  `main_external_arith_emission_bundle`. Matches the per-AIR
  prediction map's 0-2 estimate for Mem-stores (lower-middle of
  the range — only 1 new entry).
* **No new bridges.** `Bridge.Mem.sd_discharge_full` is pure
  Lean composing the new axiom with `transpile_SD` (class #1)
  and `Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg`
  (pure Lean, no axiom).
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_SD` (canonical): 31 binders / 20 hypotheses.
`equiv_SD_from_trust` (this file): 26 binders / 14 hypotheses.

Net −5 binders / −6 hypotheses per Mem-store-shape opcode.
Composition:

* Drops `h_ptr_match` + 8 `h_byte_{0..7}` (9 binders, all
  hypotheses): the entire byte-and-ptr promise bundle is
  discharged via `Bridge.Mem.sd_discharge_full` consuming the
  new `main_store_emission_bundle_sd` plus `transpile_SD`.
* Adds `(main : Valid_Main)`, `(r_main : ℕ)` (2 non-hypothesis
  binders) and `h_main_active`, `h_main_op` (2 hypothesis
  binders) — Compliance.lean shares `(main, r_main)` across all
  opcodes and derives `h_main_*` from its ROM handshake.

Net: −9 (byte+ptr) + 4 (validator + activation) = −5 binders.
Hypothesis count drops by −6 (the 9 promise hyps drop, 2 light
activation pins added, plus the bundle-shape includes 1
implicit hyp reduction).

This matches the discharge-recipe.md "caller-burden must shrink"
discipline. At the global `Compliance.lean` level the reduction
extends further because `(main, r_main)` collapse into shared
parameters across all 4 Mem-store opcodes (SD/SW/SH/SB), and
`h_main_active` / `h_main_op` come from Compliance.lean's
program-counter handshake.

## Cross-shape lessons

* The `Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg`
  utility composes cleanly with any opcode using
  register-routed operands, not just ALU shapes. SD reuses it
  verbatim for both rs1 (address base) and rs2 (store value).
* The store-side **byte-form bundle** pattern (axiom delivering
  byte extracts directly, rather than lane-form + pure-Lean
  byte derivation) trades axiom-shape complexity for clean
  caller composition. The auditability is preserved because the
  byte extracts are PIL-derivable from the lane-form + byte-range
  bus consequences (same class #4 envelope).
* **Width specialization.** SD's bundle pins all 8 byte lanes
  meaningful (`ind_width = 8`). SB/SH/SW each need their own
  width-specialized bundle in their respective exemplar wrappers,
  with the high byte lanes zero-pinned per the bus's `ind_width`
  selector. The shape generalizes to a four-axiom family
  (`main_store_emission_bundle_{sd,sw,sh,sb}`) all in class #4.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.StoreD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_SD`.**

    Caller obligations (signature header, ordered):
    1. Sail-side inputs (`state`, `sd_input`, `rs1`, `rs2`, and
       the platform-state records `mstatus`, `pmaRegion`, `misa`,
       `mseccfg`).
    2. AIR validator + row index (`main : Valid_Main`,
       `r_main : ℕ`). Compliance.lean shares `main` across all
       opcodes.
    3. The structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    4. Activation + opcode pins on Main (`h_main_active`,
       `h_main_op`). Both come from Compliance.lean's ROM
       handshake on the row hosting the SD instruction.
    5. Sail-side state predicates (SPEC-PRE):
       `risc_v_assumptions`, `h_input_pc`, `h_input_r1`,
       `h_input_r2`, plus the address-bound + alignment
       precondition (`h_addr_bound`, `h_align`).
    6. Bus-protocol structural hypotheses — pass-through from
       `equiv_SD`.

    Derived internally (NOT caller-supplied):
    * `h_ptr_match : e2.ptr.toNat = (sd_input.r1_val + signExt(imm)).toNat` —
      from `Bridge.Mem.sd_discharge_full`.
    * `h_byte_0 .. h_byte_7 : (e2.xi : BitVec 8) = extractLsb _ _ sd_input.r2_val` —
      from `Bridge.Mem.sd_discharge_full`.

    Trust footprint: `main_store_emission_bundle_sd` (class #4,
    NEW), `transpile_SD` (class #1), plus `equiv_SD`'s existing
    closure. The `Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg`
    bridge is pure Lean (no axiom). -/
theorem equiv_SD_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sd_input : PureSpec.SdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    -- AIR validator + row index. Compliance.lean shares `main`.
    (main : Valid_Main C FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins. Compliance.lean derives these
    -- from Main's ROM handshake on the row hosting SD.
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op : main.op r_main = OP_COPYB)
    -- Sail-side state predicates (SPEC-PRE), absorbed from
    -- `sd_state_assumptions` and `RISC_V_assumptions`.
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.sd_state_assumptions sd_input state)
    -- Bus-protocol structural hypotheses — pass-through from `equiv_SD`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_STORED_pure sd_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    execute_instruction (instruction.STORE (
      sd_input.imm,
      regidx.Regidx sd_input.r2,
      regidx.Regidx sd_input.r1,
      8
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Discharge the 9 ptr+byte hypotheses via the Mem-stores bridge.
  -- The bridge consumes the Sail `read_xreg` facts from
  -- `sd_state_assumptions`, which lives at SPEC-PRE level (it is
  -- already required by `equiv_SD` as `h_opcode_assumptions`).
  have h_read_r1 := h_opcode_assumptions.2.1
  have h_read_r2 := h_opcode_assumptions.2.2.1
  -- Convert from `rX_bits (regidx.Regidx r) state` to
  -- `read_xreg rs_fin state` via the existing
  -- `rX_read_xreg_equiv` bridge.
  have h_read_r1' :
      read_xreg (regidx_to_fin (regidx.Regidx sd_input.r1)) state
        = EStateM.Result.ok sd_input.r1_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sd_input.r1)
          (regidx_to_fin (regidx.Regidx sd_input.r1))
          (by simp [regidx_to_fin])]
    exact h_read_r1
  have h_read_r2' :
      read_xreg (regidx_to_fin (regidx.Regidx sd_input.r2)) state
        = EStateM.Result.ok sd_input.r2_val state := by
    rw [← rX_read_xreg_equiv state (regidx.Regidx sd_input.r2)
          (regidx_to_fin (regidx.Regidx sd_input.r2))
          (by simp [regidx_to_fin])]
    exact h_read_r2
  -- Compose the discharge bundle.
  obtain ⟨h_ptr_match, h_byte_0, h_byte_1, h_byte_2, h_byte_3,
          h_byte_4, h_byte_5, h_byte_6, h_byte_7⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.sd_discharge_full
      main r_main e2 state
      (regidx_to_fin (regidx.Regidx sd_input.r1))
      (regidx_to_fin (regidx.Regidx sd_input.r2))
      sd_input.r1_val sd_input.r2_val sd_input.imm
      h_main_active h_main_op h_m2_mult h_m2_as
      h_read_r1' h_read_r2'
  -- Delegate to canonical `equiv_SD`.
  exact ZiskFv.Equivalence.StoreD.equiv_SD
    state sd_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2
    { risc_v_assumptions := risc_v_assumptions
      opcode_assumptions_ := h_opcode_assumptions
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := h_m0_mult
      m0_as := h_m0_as
      m1_mult := h_m1_mult
      m1_as := h_m1_as
      m2_mult := h_m2_mult
      m2_as := h_m2_as }
    h_ptr_match h_byte_0 h_byte_1 h_byte_2 h_byte_3
    h_byte_4 h_byte_5 h_byte_6 h_byte_7

end ZiskFv.Compliance
