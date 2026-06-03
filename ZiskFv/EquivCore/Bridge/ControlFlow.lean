import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.Airs.Main.Main
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.ZiskCircuit.Jalr
import ZiskFv.EquivCore.Bridge.StateBridge
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge

/-!
# ControlFlow discharge bridge

Implements *promise discharge* for the Main-only opcode shapes
that don't consume from an arithmetic Provider AIR — branches
(`BEQ` / `BNE` / `BLT` / `BLTU` / `BGE` / `BGEU`), the U-type
opcodes (`AUIPC` / `LUI`), the jumps (`JAL` / `JALR`), and
`FENCE`.

For these opcodes the only per-row content is the Main AIR's
emission (encoded in PC routing and, for JAL / JALR, a register
write). There is no separate Provider AIR for arithmetic — the
"discharge" reduces to:

* For branches: derive `r1_val` and `r2_val` packed-lane forms
  from `transpile_<BRANCH>` + `SailStateBridge`.
  Each `transpile_<BRANCH>` axiom shares the same shape: 5 mode
  pins then `a_0 = lane_lo (state.xreg rs1)`, `a_1 = lane_hi
  (state.xreg rs1)`, `b_0 = lane_lo (state.xreg rs2)`, `b_1 =
  lane_hi (state.xreg rs2)`.
* For JALR: the proof consumes the production final `OP_AND` row;
  the unaligned `ADD -> lastc -> AND` facts are carried by explicit
  source-C / selector bridge axioms and assembled in `ZiskCircuit.Jalr`.
* For AUIPC / LUI / JAL / FENCE: no register reads — the input
  bridge step is vacuous; the discharge is the PC-routing axioms
  `transpile_PC_for_{JAL,JALR,AUIPC}` consumed directly by the
  equiv proofs.

This file provides one helper for the branch shape (covering all
6 branches by parameterizing on the transpile axiom's application
result). Other shapes are direct one-line uses of existing
`SailStateBridge` helpers and don't warrant their own wrappers.
-/

namespace ZiskFv.EquivCore.Bridge.ControlFlow

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.EquivCore.Bridge.StateBridge
open ZiskFv.EquivCore.Bridge.SailStateBridge


/-- **Branch-shape input bridges (r1 + r2 in one call).** Given the
    a and b lane conjuncts already projected from a branch
    `transpile_<OP>` axiom application (`h_a_lo_t`, `h_a_hi_t`,
    `h_b_lo_t`, `h_b_hi_t`), plus the Sail `read_xreg` facts the
    caller already carries for `equiv_<BRANCH>_sail`, deliver the
    packed-lane equations for both r1_val and r2_val.

    Each `transpile_<BRANCH>` axiom (BEQ, BNE, BLT, BLTU, BGE,
    BGEU) has the same lane-conjunct shape modulo opcode and
    `neg`-or-order flags; this helper consumes the projected
    conjuncts opaquely so all 6 branches can share it.

    Internally calls `packed_lane_eq_of_read_xreg` once per
    register. No new axioms; pure composition of + 1.7b
    infrastructure. -/
lemma branch_input_bridges_of_read_xreg
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) (r1_val r2_val : BitVec 64)
    (a_lo a_hi b_lo b_hi : FGL)
    (h_a_lo : a_lo = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi : a_hi = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_b_lo : b_lo = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi : b_hi = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r1_val = BitVec.ofNat 64 (a_lo.val + a_hi.val * 4294967296)
    ∧ r2_val = BitVec.ofNat 64 (b_lo.val + b_hi.val * 4294967296) :=
  ⟨packed_lane_eq_of_read_xreg state rs1 r1_val a_lo a_hi h_a_lo h_a_hi h_read_r1,
   packed_lane_eq_of_read_xreg state rs2 r2_val b_lo b_hi h_b_lo h_b_hi h_read_r2⟩

/-! ## Non-branch discharge entry points

The entry point below packages the AUIPC transpile-pinnable FGL ↔
`Nat` offset identity that `equiv_AUIPC` currently takes as a
separate parameter.

Each consumes the per-shape `*_circuit_holds` predicate (already a
required input to the equiv, for the PC-advance + store_value
formula derivations) and the relevant `transpile_<OP>` axiom from
`Fundamentals/Transpiler.lean` instantiated at the appropriate
ghost operand. The transpile axiom delivers an FGL equation; the
discharge then extracts `.val` and uses `Fin.val_natCast` plus a
`< GL_prime` no-wrap bound to land on the shape the equiv expects.

No new axioms — every discharge here is pure composition of
existing trust-ledger pieces (`transpile_<OP>` + Fin / FGL
arithmetic). FENCE is already minimal and needs no entry point.

Caller-burden reduction (per opcode):
* JALR: the old `h_jmp2` discharge no longer applies because the
  production final row uses `jmp_offset2 = 4` only in the aligned
  lowering and `jmp_offset2 = 3` in the unaligned lowering.
* AUIPC: dynamic PC/offset facts are now caller-supplied by the
  compliance route instead of discharged through the legacy transpiler
  bridge.

Anti-laundering metric:
* `trust/generated/baseline-hypothesis-count.txt` strictly shrinks for
  JALR (14 → 13).
* No new axiom.
-/

end ZiskFv.EquivCore.Bridge.ControlFlow
