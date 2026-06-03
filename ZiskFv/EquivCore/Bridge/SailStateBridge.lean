import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.SailSpec.Auxiliaries
import ZiskFv.EquivCore.Bridge.StateBridge

/-!
# Shared *discharge bridge* helper — Sail-state ↔ `RV64State`

Closes the final step of the input-bridge derivation chain consumed by
every ALU-shape *discharge bridge*. Distinct from `StateBridge.lean`:
that file holds the **opcode-independent packed-lane arithmetic**
(`bv64_packed_eq_of_lanes`), while this file holds the **Sail-state
materialisation** that turns a Sail `read_xreg` fact into a `RV64State`
suitable for instantiating the `transpile_<OP>` axioms.

The bridge takes a Sail register-read fact and the `transpile_<OP>`
lane equalities and produces the packed-lane form of `r_val`:

```
read_xreg rs state = .ok r_val state          (caller-supplied; Sail-form)
transpile_<OP> at (sail_to_rv64 state) rs     (trust-ledger)
  → m.a_0 r_main = lane_lo r_val
  → m.a_1 r_main = lane_hi r_val
bv64_packed_eq_of_lanes
  → r_val = BitVec.ofNat 64 ((m.a_0).val + (m.a_1).val * 2^32)
```

The trust footprint is unchanged: this module adds no axioms. The
universal-over-`RV64State` shape of the `transpile_<OP>` axioms makes
the instantiation at `sail_to_rv64 state` go through — we materialize
the RV64 state whose `xreg` agrees with Sail's `read_xreg`, instantiate
the axiom there, and recover the lane equalities at `r_val`.

(The universal-over-state shape of the `transpile_<OP>` family is a
known *trust-ledger* coarsening — a sound formulation would
existentially quantify the state. This module extracts exactly the
state-instantiation that the sound formulation would deliver, so
narrowing `transpile_<OP>` to existential form later would not
affect this module's API.)
-/

namespace ZiskFv.EquivCore.Bridge.SailStateBridge

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.EquivCore.Bridge.StateBridge

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
lemma sail_to_rv64_xreg_eq_of_read_xreg
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
    `bv64_packed_eq_of_lanes`. Opcode-independent — every
    `transpile_<OP>` lane-equality pair has this shape after the rs
    is the right register. -/
lemma packed_lane_eq_of_read_xreg
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
    `packed_lane_eq_of_read_xreg` to explicit Main source-lane facts.
    Delivers both r1 and r2 packed-lane equations without consulting the
    retired transpiler bridge. -/
lemma add_input_bridges_of_read_xreg

    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) (r1_val r2_val : BitVec 64)
    (h_a_lo : m.a_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi : m.a_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_b_lo : m.b_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi : m.b_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r1_val
      = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296)
    ∧ r2_val
      = BitVec.ofNat 64 ((m.b_0 r_main).val + (m.b_1 r_main).val * 4294967296) := by
  refine ⟨?_, ?_⟩
  · exact packed_lane_eq_of_read_xreg state rs1 r1_val
      (m.a_0 r_main) (m.a_1 r_main) h_a_lo h_a_hi h_read_r1
  · exact packed_lane_eq_of_read_xreg state rs2 r2_val
      (m.b_0 r_main) (m.b_1 r_main) h_b_lo h_b_hi h_read_r2

/-- **ADDI-shape r1 input bridge.** Specializes
    `packed_lane_eq_of_read_xreg` to explicit Main source-lane facts. -/
lemma addi_input_r1_main_eq_of_read_xreg

    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 : Fin 32) (r1_val : BitVec 64)
    (h_a_lo : m.a_0 r_main = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi : m.a_1 r_main = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state) :
    r1_val
      = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 4294967296) := by
  exact packed_lane_eq_of_read_xreg state rs1 r1_val
    (m.a_0 r_main) (m.a_1 r_main) h_a_lo h_a_hi h_read_r1

/-! ## Signed-form Sail-state bridge

Signed-form companion to `packed_lane_eq_of_read_xreg`. Where the
unsigned form recovers `r_val = BitVec.ofNat 64 (a_lo.val + a_hi.val * 2^32)`,
the signed form derives the integer-form lane equation
`r_val.toInt = packed4 c0..c3 - sign * 2^64` from:

* a Sail register read `read_xreg rs state = .ok r_val state`,
* a chunk-packed nat identity `r_val.toNat = packed4 c0 c1 c2 c3` with each
  `c_i < 2^16` (sourced from the unsigned form),
* the sign-witness MSB equation `sign = if 2^63 ≤ packed4 c0 c1 c2 c3 then 1 else 0`
  (sourced from the relevant class-#6b axiom — e.g.
  `arith_div_np_eq_msb_of_dividend`).

This bridge is **generic** — it has no Arith-specific hypotheses, no
Valid_AIR records, no row indices. It composes the BitVec.toInt
characterization (`Init.Data.BitVec.Lemmas.toInt_eq_toNat_cond`) with
the caller-supplied chunk identities to land on the signed-form lane
equation. Consumed by every signed/W discharge bridge (DIV, REM, MUL
signed variants, and W-variants downstream). -/

/-- **Signed packed-lane integer equation from a Sail register read.**
    Given a Sail `read_xreg rs state = .ok r_val state` fact, a
    chunk-packed identity `r_val.toNat = packed4 c0 c1 c2 c3` (with
    each chunk `< 2^16`, ensuring `packed4 < 2^64`), and a
    sign-witness MSB equation
    `sign = if 2^63 ≤ packed4 c0 c1 c2 c3 then 1 else 0`, conclude

    ```
    r_val.toInt = (packed4 c0 c1 c2 c3 : ℤ) - sign * 2^64
    ```

    Pure arithmetic step combining `BitVec.toInt_eq_toNat_cond` with
    the substitution of the chunk identity for `r_val.toNat` and the
    case-split on the sign witness. No Arith-AIR dependencies. -/
lemma signed_packed_toInt_eq_of_read_xreg
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {rs : Fin 32} {r_val : BitVec 64}
    (_h_read : read_xreg rs state = EStateM.Result.ok r_val state)
    {c0 c1 c2 c3 : ℕ} {sign : ℕ}
    (h_packed : r_val.toNat
        = ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3)
    (h_chunks_bounded : c0 < 65536 ∧ c1 < 65536 ∧ c2 < 65536 ∧ c3 < 65536)
    (h_sign_eq_msb : sign
        = (if 2^63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3 then 1 else 0)) :
    r_val.toInt
      = (ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3 : ℤ)
          - (sign : ℤ) * (2:ℤ)^64 := by
  -- Unpack chunk bounds and derive packed4 < 2^64.
  obtain ⟨h0, h1, h2, h3⟩ := h_chunks_bounded
  have h_packed_lt : ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3
      < 18446744073709551616 :=
    ZiskFv.PackedBitVec.MulNoWrap.packed4_lt_2_64 h0 h1 h2 h3
  -- Characterize r_val.toInt via toInt_eq_toNat_cond, then substitute h_packed.
  rw [BitVec.toInt_eq_toNat_cond, h_packed]
  -- The condition `2 * packed4 < 2^64` collapses to `packed4 < 2^63`.
  have hpow : (2 ^ 64 : ℕ) = 18446744073709551616 := by decide
  -- Case split on whether the packed value is in the signed-negative half.
  by_cases h_neg : 2 ^ 63 ≤ ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3
  · -- `packed4 ≥ 2^63` → MSB is set → sign = 1 → toInt = toNat - 2^64.
    have h_two_mul : ¬ 2 * ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3 < 2 ^ 64 := by
      rw [hpow]
      have : (2 ^ 63 : ℕ) = 9223372036854775808 := by decide
      omega
    rw [if_neg h_two_mul]
    rw [if_pos h_neg] at h_sign_eq_msb
    subst h_sign_eq_msb
    push_cast
    ring
  · -- `packed4 < 2^63` → MSB clear → sign = 0 → toInt = toNat.
    have h_lt : ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3 < 2 ^ 63 := by
      omega
    have h_two_mul : 2 * ZiskFv.PackedBitVec.MulNoWrap.packed4 c0 c1 c2 c3 < 2 ^ 64 := by
      rw [hpow]
      have : (2 ^ 63 : ℕ) = 9223372036854775808 := by decide
      omega
    rw [if_pos h_two_mul]
    rw [if_neg h_neg] at h_sign_eq_msb
    subst h_sign_eq_msb
    push_cast
    ring

end ZiskFv.EquivCore.Bridge.SailStateBridge
