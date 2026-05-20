import Mathlib

import ZiskFv.Equivalence_v1.Ld
import ZiskFv.Equivalence_v1.Promises.Load
import ZiskFv.Equivalence_v1.Bridge.Mem
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LD` trust-discharge wrapper — Mem-loads shape exemplar
## Why LD

LD is the simplest load: all 8 bytes of `state.mem[ptr..ptr+7]` flow
through the load-side memory-bus entry's byte lanes verbatim, ptr-match
is the generic load-address formula `xreg rs1 + signExt(imm)`, and the
copyb passthrough delivers the rd-write entry's bytes byte-for-byte
from the load consumer entry. There is no sign-extension and no
sub-doubleword width-pin coupling.

The shape's narrower zero-extended opcodes (LBU / LHU / LWU) will
reuse LD's discharge machinery plus the `memalign_subdoubleword_load_high_bytes_zero`
derived theorem (in `Airs/MemoryBus/MemAlignBridge.lean`, already a
pure-Lean derivation atop `memalign_load_perm_sound` + the MemAlignRom
zero-pin axiom) closing the high byte lanes to zero. The signed
narrow loads (LB / LH / LW) take a different path through the
BinaryExtension AIR (`Circuit/SextLoadBridge.lean`) and are a separate
sub-pattern.

## 5-category discharge applied

* **Lane-match.** Pre-discharged on the canonical surface.
  `equiv_LD`'s proof already invokes
  `Bridge.Mem.ld_discharge_full` (consuming `main_load_emission_bundle`,
  class #4) to deliver the seven-tuple of load-side promise hypotheses
  (`h_main_emit_b`, `h_main_emit_c`, `h_ptr_match`, `h_rd_zero_iff`,
  `h_rd_idx`, `h_copy0`, `h_copy1`) from the activation + opcode pin +
  bus-shape pins. The wrapper inherits this; nothing to add.
* **Mode pins.** N/A on the provider side (Mem core has no mode
  columns; the activation pins `is_external_op = 0`, `op = OP_COPYB`
  are caller-supplied at the Compliance level from the ROM-handshake
  on the row hosting LD).
* **Sign-witness pins.** N/A — LD is full-doubleword data movement,
  no sign extension.
* **Range/bound.** Byte ranges on the load consumer entry are
  internalized by `equiv_LD` via
  `memory_bus_entry_byte_range_perm_sound` (class #5b) inside the
  copyb-passthrough derivation
  (`ZiskFv.ZiskCircuit.LoadDerivation.load_copyb_e1_e2_bytes_eq_bv`).
  Pre-discharged on the canonical surface.
* **Operand bridges.** `read_xreg rs1` (the load address base) is
  routed through `ld_state_assumptions` (SPEC-PRE) and consumed
  inside `equiv_LD`'s memory-derivation step
  (`mem_load_correct` + the `state.mem` keys from
  `ld_state_assumptions.h_d{0..7}`). The wrapper inherits this;
  the cross-shape `SailStateBridge` is not needed because the load's
  rd-value derives from `state.mem`, not from a register read of
  the value itself.

## Anti-laundering report

* **Zero new axioms.** This wrapper consumes only existing
  trust-ledger axioms transitively via `equiv_LD`. The Mem-loads
  load-side bundle (`main_load_emission_bundle`, class #4) was
  already in place before this pilot; LD's discharge needs were
  fully covered. Trust ledger unchanged — matches the per-AIR
  per-AIR axioms map's 0-2 prediction for Mem (lower bound).
* **No new bridges.** The existing `Bridge.Mem.ld_discharge_full`
  is consumed verbatim by `equiv_LD`; no wrapper-level helper is
  needed.
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_LD` (canonical): 28 binders / 13 hypotheses.
`equiv_LD` (this file): 27 binders / 13 hypotheses.

Net −1 binder / 0 hypothesis at the per-opcode level.

The wrapper's principal contribution is **canonical-naming**:
* Renames `h_op : main.op r_main = (1 : FGL)` to
  `h_main_op_ld : main.op r_main = OP_COPYB`. Since `OP_COPYB := 1`
  definitionally, the hypothesis content is identical but the
  symbolic form aligns with the Compliance-level handshake convention
  used by the SD / LUI / ADD / OR / SLL exemplars.
* Renames `h_ext : main.is_external_op r_main = 0` to
  `h_main_active : main.is_external_op r_main = 0` (same content,
  Compliance naming).

The −1 binder comes from collapsing the implicit-`mem` slot via the
Compliance shared-validator convention (the wrapper accepts `mem`
positionally rather than as a named parameter; at the global
`Compliance.lean` level `mem` collapses into a single parameter
shared across LD / LBU / LHU / LWU / SD / SH / SW / SB).

At the global `Compliance.lean` level the reduction extends much
further:

* `(main, mem, exec_row, e0, e1, e2)` collapse into shared
  parameters across all 4 Mem-loads opcodes (LD/LBU/LHU/LWU) — and
  further across all 8 Mem opcodes when the stores fold in.
* `h_main_active` / `h_main_op_ld` come from Compliance.lean's
  program-counter handshake on the row hosting LD.
* The 10 bus-protocol structural pins (`h_exec_len`, `h_e0_mult`,
  `h_e1_mult`, `h_nextPC_matches`, `h_m0_mult`, `h_m0_as`,
  `h_m1_mult`, `h_m1_as`, `h_m2_mult`, `h_m2_as`) are uniform across
  the load shape and absorbed into the global bus-shape obligations.

## Cross-shape lessons

* **Mem-loads is heavily pre-discharged on the canonical surface.**
  Unlike DIV / OR / ADD where the wrapper has substantial discharge
  work (mode pins, lane-match assembly, byte-range unpacking), the
  LD canonical theorem already internalizes lane-match, byte-range,
  and operand-bridge discharges via the pre-existing
  `Bridge.Mem.ld_discharge_full` and `mem_load_correct` /
  `load_copyb_e1_e2_bytes_eq_bv` chains. The wrapper's per-opcode
  surface is therefore mostly canonical naming.
* The Mem-loads load-side **emission bundle**
  (`main_load_emission_bundle`, class #4, `MemBridge.lean:374`) is
  shape-uniform: LD / LBU / LHU / LWU all consume it identically.
  The width difference is encoded downstream on the memory-bus
  entry (`ind_width` selector pinned by the MemAlign* path for
  sub-doubleword loads), not on the Main row.
* **Zero-extended narrow loads (LBU / LHU / LWU)** generalize from
  LD mechanically: swap `transpile_LD` for `transpile_<LBU,LHU,LWU>`
  and consume `memalign_subdoubleword_load_high_bytes_zero` (a pure
  Lean derivation, already in place) to pin the high byte lanes to
  zero. The wrapper-level work is ~30 lines apiece (essentially a
  copy of this file with the width-specific `transpile_<OP>` and
  zero-pad invocation).
* **Signed narrow loads (LB / LH / LW)** take a different path
  through the BinaryExtension AIR's `OP_SIGNEXTEND_{B,H,W}` rows.
  The `sext_load_discharge_full` family in `Bridge/Mem.lean` already
  exists and exposes a parallel five-tuple discharge for those
  signed loads. Their wrapper is a separate sub-pattern — same
  shape as this exemplar but consuming the BinaryExtension-rooted
  bundle instead of the copyb-rooted bundle.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Trust-discharged wrapper for `equiv_LD`.**

    Caller obligations (signature header, ordered):
    1. Sail-side inputs (`state`, `ld_input`, and the platform-state
       records `mstatus`, `pmaRegion`, `misa`, `mseccfg`).
    2. AIR validators + row index (`main : Valid_Main`,
       `mem : Valid_Mem`, `r_main : ℕ`). Compliance.lean shares
       `(main, mem)` across all Mem opcodes (LD/LBU/LHU/LWU/SD/SB/
       SH/SW).
    3. Structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    4. Activation + opcode pins on Main (`h_main_active`,
       `h_main_op_ld`). Both come from Compliance.lean's
       program-counter handshake on the row hosting LD.
    5. Sail-side state predicates (SPEC-PRE):
       `risc_v_assumptions`, `h_opcode_assumptions`.
    6. Bus-protocol structural hypotheses — pass-through from
       `equiv_LD`; Compliance.lean supplies these from the same
       bus-shape obligations as every other opcode in the shape.

    Derived internally (NOT caller-supplied):
    * `equiv_LD`'s internal `ld_discharge_full` invocation already
      derives `h_main_emit_b`, `h_main_emit_c`, `h_ptr_match`,
      `h_rd_zero_iff`, `h_rd_idx`, `h_copy0`, `h_copy1` from
      `main_load_emission_bundle` (class #4); this wrapper inherits
      that discharge transparently.

    Trust footprint: `equiv_LD`'s existing closure (which
    transitively consumes `main_load_emission_bundle` (class #4),
    `memory_bus_entry_byte_range_perm_sound` (class #5b),
    `lookup_consumer_matches_provider_load` (class #4),
    `row_models_sail_state_load` (class #2), `transpile_LD` (class #1)
    and the load-output derivation chain). Zero new axioms — matches
    `docs/fv/per-air-axiom-map.md`'s 0-2 prediction for Mem
    (lower-bound endpoint, like LUI/ADD/SLL among the prior pilots). -/
theorem equiv_LD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index. Compliance.lean shares
    -- `(main, mem)` across all Mem opcodes.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins. Compliance.lean derives these
    -- from Main's ROM handshake on the row hosting LD.
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.Equivalence_v1.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  -- Delegate to canonical `equiv_LD`. `pins`'s opKind `OP_COPYB` is
  -- definitionally `(1 : FGL)` (see `Trusted/Transpiler.lean:147`).
  exact ZiskFv.Equivalence_v1.Ld.equiv_LD
    state ld_input regs bus
    promises
    main mem r_main pins

end ZiskFv.Compliance
