import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Equivalence.Bridge.StateBridge

/-!
# Shared *discharge bridge* helper — Sail-state ↔ `RV64State`

Step 1.7b of `/home/cody/.claude/plans/plan-to-completely-resolve-wild-lynx.md`.
Closes the final step of the input-bridge derivation chain consumed by
every ALU-shape *discharge bridge*.

The bridge takes a Sail register-read fact and the `transpile_<OP>`
lane equalities and produces the packed-lane form of `r_val`:

```
read_xreg rs state = .ok r_val state          (caller-supplied; Sail-form)
transpile_<OP> at (sail_to_rv64 state) rs     (trust-ledger)
  → m.a_0 r_main = lane_lo r_val
  → m.a_1 r_main = lane_hi r_val
bv64_packed_eq_of_lanes (Step 1.7a)
  → r_val = BitVec.ofNat 64 ((m.a_0).val + (m.a_1).val * 2^32)
```

The trust footprint is unchanged: this module adds no axioms. The
universal-over-`RV64State` shape of the `transpile_<OP>` axioms makes
the instantiation at `sail_to_rv64 state` go through — we materialize
the RV64 state whose `xreg` agrees with Sail's `read_xreg`, instantiate
the axiom there, and recover the lane equalities at `r_val`.

(The universal-over-state shape of the `transpile_<OP>` family is a
known *trust-ledger* coarsening — a sound formulation would
existentially quantify the state. Step 1.7b extracts exactly the
state-instantiation that the sound formulation would deliver. A
narrowing PR for `transpile_<OP>` to existential form is tracked
separately and does not affect this module's API.)
-/

namespace ZiskFv.Equivalence.Bridge.SailStateBridge

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Equivalence.Bridge.StateBridge

/-- Materialize the `RV64State` whose `xreg` accessor pulls each
    register slot through Sail's `read_xreg`. The `pc` field is
    irrelevant to the input-bridge derivation in every ALU-shape
    *discharge bridge* — those consume only `transpile_<OP>`'s
    a/b-lane conjuncts, not its pc-related conjuncts — so we fix it
    to `0#64` rather than threading a `Sail.readReg Register.PC`
    unwrap.

    `noncomputable` because `read_xreg`'s `match` on `EStateM.Result`
    is not directly compiled here (the bridge consumers don't
    `decide` the result; they `rw` with `sail_to_rv64_xreg_eq_of_read_xreg`
    below). -/
noncomputable def sail_to_rv64
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    : RV64State :=
  { xreg := fun rs =>
      match read_xreg rs state with
      | EStateM.Result.ok v _ => v
      | EStateM.Result.error _ _ => 0#64
    pc := 0#64 }

/-- The `xreg rs` field of `sail_to_rv64 state` agrees with the value
    delivered by a successful `read_xreg rs state` call. The single
    rewrite consumed by every ALU-shape bridge's input-bridge step. -/
theorem sail_to_rv64_xreg_eq_of_read_xreg
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs : Fin 32) (r_val : BitVec 64)
    (h : read_xreg rs state = EStateM.Result.ok r_val state) :
    (sail_to_rv64 state).xreg rs = r_val := by
  unfold sail_to_rv64; simp [h]

/-- **Packed-lane recovery from a Sail register read.** Given a
    Main-row lane pair `(a_lo, a_hi)` known to equal the `lane_lo` /
    `lane_hi` of `(sail_to_rv64 state).xreg rs`, plus a Sail
    `read_xreg rs state = .ok r_val state` fact, conclude
    `r_val = BitVec.ofNat 64 (a_lo.val + a_hi.val * 2^32)`.

    Composes `sail_to_rv64_xreg_eq_of_read_xreg` (above) with
    `bv64_packed_eq_of_lanes` (Step 1.7a). Opcode-independent — every
    `transpile_<OP>` lane-equality pair has this shape after the rs
    is the right register. -/
theorem packed_lane_eq_of_read_xreg
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs : Fin 32) (r_val : BitVec 64)
    (a_lo a_hi : FGL)
    (h_a_lo : a_lo = lane_lo ((sail_to_rv64 state).xreg rs))
    (h_a_hi : a_hi = lane_hi ((sail_to_rv64 state).xreg rs))
    (h_read : read_xreg rs state = EStateM.Result.ok r_val state) :
    r_val = BitVec.ofNat 64 (a_lo.val + a_hi.val * 4294967296) := by
  rw [sail_to_rv64_xreg_eq_of_read_xreg state rs r_val h_read] at h_a_lo h_a_hi
  exact bv64_packed_eq_of_lanes h_a_lo h_a_hi

/-- **ADD-shape input bridges (r1 + r2 in one call).** Specializes
    `packed_lane_eq_of_read_xreg` to the `transpile_ADD` row contract.
    Delivers both r1 and r2 packed-lane equations in a single axiom
    application — consumed by `Bridge.BinaryAdd.add_discharge` to
    replace its two caller-supplied `h_input_r{1,2}_main` *promise
    hypotheses* with the Sail-form `read_xreg` facts that
    `equiv_ADD` already carries. -/
theorem add_input_bridges_of_read_xreg
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (r_main : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) (r1_val r2_val : BitVec 64)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = OP_ADD)
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r1_val
      = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296)
    ∧ r2_val
      = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) := by
  obtain ⟨h_a_lo, h_a_hi, h_b_lo, h_b_hi, _, _, _, _, _⟩ :=
    transpile_ADD m r_main (sail_to_rv64 state) rs1 rs2 h_active h_op
  refine ⟨?_, ?_⟩
  · exact packed_lane_eq_of_read_xreg state rs1 r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_a_lo h_a_hi h_read_r1
  · exact packed_lane_eq_of_read_xreg state rs2 r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_b_lo h_b_hi h_read_r2

/-- **ADDI-shape r1 input bridge.** Specializes
    `packed_lane_eq_of_read_xreg` to the `transpile_ADDI` row contract
    — single register read (`rs1`), with the b-lanes carrying an
    immediate the axiom leaves caller-routed. Consumed by
    `equiv_ADDI` to discharge `h_input_r1_circuit` after translating
    Main lanes to BinaryAdd-row lanes via the existing
    `matches_entry` projection inside `addi_circuit_holds_with_binaryadd`. -/
theorem addi_input_r1_main_eq_of_read_xreg
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (r_main : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rd_dummy : Fin 32) (r1_val : BitVec 64)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = OP_ADD)
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state) :
    r1_val
      = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) := by
  -- `transpile_ADDI`'s `imm_b_lo`/`imm_b_hi` are caller-routed; we
  -- instantiate them to `m.b_0`/`m.b_1` so the unused b-conjuncts
  -- become reflexive and we extract only the a-lane facts.
  obtain ⟨_, _, _, _, _, _, h_a_lo, h_a_hi, _, _⟩ :=
    transpile_ADDI m r_main rs1 rd_dummy
      (m.b_0 r_main) (m.b_1 r_main) (sail_to_rv64 state) h_active h_op
  exact packed_lane_eq_of_read_xreg state rs1 r1_val
    (m.a_0 r_main) (m.a_1 r_main) h_a_lo h_a_hi h_read_r1

end ZiskFv.Equivalence.Bridge.SailStateBridge
