import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Equivalence.Bridge.StateBridge
import ZiskFv.Equivalence.Bridge.SailStateBridge

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
  from `transpile_<BRANCH>` + Step 1.7b's `SailStateBridge`.
  Each `transpile_<BRANCH>` axiom shares the same shape: 5 mode
  pins then `a_0 = lane_lo (state.xreg rs1)`, `a_1 = lane_hi
  (state.xreg rs1)`, `b_0 = lane_lo (state.xreg rs2)`, `b_1 =
  lane_hi (state.xreg rs2)`.
* For JALR: derive r1_val packed form (uses transpile_JALR which
  has ITYPE shape).
* For AUIPC / LUI / JAL / FENCE: no register reads — the input
  bridge step is vacuous; the discharge is the PC-routing axioms
  `transpile_PC_for_{JAL,JALR,AUIPC}` consumed directly by the
  equiv proofs.

This file provides one helper for the branch shape (covering all
6 branches by parameterizing on the transpile axiom's application
result). Other shapes are direct one-line uses of existing
`SailStateBridge` helpers and don't warrant their own wrappers.
-/

namespace ZiskFv.Equivalence.Bridge.ControlFlow

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Equivalence.Bridge.StateBridge
open ZiskFv.Equivalence.Bridge.SailStateBridge

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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
    register. No new axioms; pure composition of Step 1.7a + 1.7b
    infrastructure. -/
theorem branch_input_bridges_of_read_xreg
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

end ZiskFv.Equivalence.Bridge.ControlFlow
