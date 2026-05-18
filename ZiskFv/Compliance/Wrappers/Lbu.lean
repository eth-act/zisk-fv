import Mathlib

import ZiskFv.Equivalence.LoadBU
import ZiskFv.Equivalence.Promises.Load
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LBU` Compliance wrapper — Mem-loads (zero-ext) shape

> **Status:** within-shape wrapper, derived mechanically from
> `Wrappers/Ld.lean`. Lives outside the canonical
> surface so V1 anti-laundering metrics on the canonical theorem
> are unaffected.

## 5-category discharge applied

* **Lane-match.** Pre-discharged on the canonical surface via
  `Bridge.Mem.lbu_discharge_full` (consumes `main_load_emission_bundle`,
  class #4).
* **Mode pins.** N/A on the provider side (Mem core has no mode columns).
* **Sign-witness pins.** N/A — LBU is zero-extended.
* **Range/bound.** Pre-discharged via
  `memory_bus_entry_byte_range_perm_sound` (class #5b).
* **Operand bridges.** The load address bridge is consumed via
  `lbu_state_assumptions` (SPEC-PRE). Zero-extension to 64 bits is
  pinned by the pre-existing pure-Lean derivation
  `memalign_subdoubleword_load_high_bytes_zero` (consumed inside
  `load_lbu_c_packed`).

## Anti-laundering report

* **Zero new axioms** — consumes only `equiv_LBU`'s existing
  transitive closure. Matches per-AIR axiom map's 0-new-axioms
  prediction for the zero-extended narrow loads.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_LBU`.** Mirrors
    `equiv_LD`'s structure with `equiv_LBU` substituted and
    the additional `h_width` pin tracked for the sub-doubleword case. -/
theorem equiv_LBU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (align : ZiskFv.Compliance.MemAlignWitness C)
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation + opcode pins (Compliance ROM handshake).
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  -- `OP_COPYB := 1` definitionally; canonical accepts `pins`/`align` verbatim.
  exact ZiskFv.Equivalence.LoadBU.equiv_LBU
    state lbu_input regs bus
    promises
    main mem r_main align pins h_width

end ZiskFv.Compliance
