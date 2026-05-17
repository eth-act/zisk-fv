import Mathlib

import ZiskFv.Equivalence.LoadBU
import ZiskFv.Equivalence.Promises.Load
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus

/-!
# `equiv_LBU` Compliance wrapper — Mem-loads (zero-ext) shape

> **Status:** within-shape wrapper, derived mechanically from
> `FromTrust/Ld.lean`. Lives outside the canonical
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
    `equiv_LD_from_trust`'s structure with `equiv_LBU` substituted and
    the additional `h_width` pin tracked for the sub-doubleword case. -/
theorem equiv_LBU_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lbu_input : PureSpec.LbuInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    -- AIR validators + row index.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL)
    (h_low :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation + opcode pins (Compliance ROM handshake).
    (h_main_active : main.is_external_op r_main = 0)
    (h_main_op_lbu : main.op r_main = OP_COPYB)
    (h_width : main.ind_width r_main = (1 : FGL))
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.Equivalence.Promises.LoadPromises
        state mstatus pmaRegion misa mseccfg
        (PureSpec.lbu_state_assumptions lbu_input state)
        (PureSpec.execute_LOADBU_pure lbu_input).nextPC
        exec_row e0 e1 e2) :
    execute_instruction (instruction.LOAD (
      lbu_input.imm,
      regidx.Regidx lbu_input.r1,
      regidx.Regidx lbu_input.rd,
      true,
      1
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- `OP_COPYB := 1` definitionally; align names for `equiv_LBU`.
  have h_op : main.op r_main = (1 : FGL) := by
    rw [h_main_op_lbu]; rfl
  exact ZiskFv.Equivalence.LoadBU.equiv_LBU
    state lbu_input mstatus pmaRegion misa mseccfg
    exec_row e0 e1 e2
    promises
    main mem r_main mab marb ma h_low h_main_active h_op h_width

end ZiskFv.Compliance
