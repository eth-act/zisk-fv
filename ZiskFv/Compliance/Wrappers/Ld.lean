import Mathlib

import ZiskFv.EquivCore.Ld
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
import ZiskFv.EquivCore.Promises.Load
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
derived theorem (in `Airs/MemoryBus/MemAlignBridge.lean`, over the
structural MemAlign provider witness) closing the high byte lanes to zero. The signed
narrow loads (LB / LH / LW) take a different path through the
BinaryExtension AIR (`Circuit/SextLoadBridge.lean`) and are a separate
sub-pattern.

## 5-category discharge applied

* **Lane-match.** Discharged through the Clean Main/Mem load witness.
  The wrapper delivers the seven-tuple of load-side facts
  (`h_main_emit_b`, `h_main_emit_c`, `h_ptr_match`, `h_rd_zero_iff`,
  `h_rd_idx`, `h_copy0`, `h_copy1`) from concrete PIL-shaped memory-bus
  messages and explicit legacy adapters.
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

* **Zero new axioms.** This wrapper consumes the Clean memory bridge
  route; the former load-side bundle and provider permutation axioms are
  absent from canonical/global closure.
* **Bridge route.** `Bridge.MemClean.ld_discharge_full_clean_provider`
  supplies the legacy facts from PIL-shaped Clean messages.
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

* **Mem-loads now use the Clean memory channel.** LD / LBU / LHU / LWU
  share the same Main `b` consumer and Mem provider adapter shape. The
  width difference is encoded downstream on the memory-bus entry
  (`ind_width` selector pinned by the MemAlign* path for sub-doubleword
  loads), not on the Main row.
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
      the Clean memory witness and adapters.

    Trust footprint: canonical LD no longer reaches the retired
    load-side Main/provider memory axioms. Its remaining closure is the
    platform scope, range-bus, Sail-state load bridge, and transpiler
    trust already tracked in the regenerated baselines. -/
lemma equiv_LD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    -- AIR validators + row index. Compliance.lean shares
    -- `(main, mem)` across all Mem opcodes.
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    -- Structural bus rows.
    (bus : ZiskFv.Compliance.BusRows)
    -- Activation / opcode pins. Compliance.lean derives these
    -- from Main's ROM handshake on the row hosting LD.
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    -- Structural promise bundle (12 fields, see Promises/Load.lean).
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LdCleanWitness
        main mem r_main bus ld_input) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact ZiskFv.EquivCore.Ld.equiv_LD_clean_provider_witness
    state ld_input regs bus
    promises
    main mem r_main pins w

/-- LD wrapper rooted at selected full-ensemble Main/Mem memory rows.

This is the migration target for the LD `OpEnvelope` arm: callers expose the
selected full-ensemble row evaluations and same-message evidence, while the
Mem provider payload match inside `LdCleanWitness` is derived by the
reducible full-ensemble constructor. The row-equality, ROM/transpile, and
legacy Main-side bus-entry pins remain explicit structural facts. -/
theorem ld_eq_of_full_ensemble_mem_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    {mainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    (h_mainEval :
      mainInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRowVar)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRowVar)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_row :
      (eval mainEnv mainRowVar).core =
        ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      eval memEnv memRowVar = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec (eval mainEnv mainRowVar).core)
    (h_store_pc : (eval mainEnv mainRowVar).core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRowVar)) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (eval mainEnv mainRowVar)) 1 1))
    (h_addr1 :
      (eval mainEnv mainRowVar).rom.addr1.toNat =
        ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2 = 0 ↔
        ld_input.rd = 0)
    (h_addr2_idx :
      ld_input.rd.toNat =
        (Transpiler.wrap_to_regidx (eval mainEnv mainRowVar).rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_legacy_addr : mem.addr r_mem = bus.e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let w :=
    ZiskFv.EquivCore.Bridge.MemClean.ldCleanWitness_of_full_ensemble_main_b_mem_provider
      main mem r_main r_mem bus ld_input
      h_mainEval h_providerEval h_msg h_main_row h_mem_row h_main_spec
      h_store_pc h_main_b_match h_main_c_match h_addr1 h_addr2_zero_iff
      h_addr2_idx h_mem_sel h_mem_legacy_addr h_mem_wr
  exact equiv_LD state ld_input regs main mem r_main bus pins promises w

end ZiskFv.Compliance
