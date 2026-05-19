import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Field.GoldilocksBridge
import ZiskFv.Trusted.Transpiler

/-!
# Shared *discharge bridge* helper — packed-lane BitVec reconstruction

Opcode-independent packed-lane arithmetic. Distinct from
`SailStateBridge.lean`: that file materialises the Sail-state and
instantiates the `transpile_<OP>` axioms, while this file holds the
pure-arithmetic step that turns two lane equalities into a packed
`BitVec`.

When discharging the per-opcode `h_input_r1_main` / `h_input_r2_main`
*promise hypotheses* — currently of the form
`add_input.r1_val = BitVec.ofNat 64 ((m.a_0 r_main).val + (m.a_1 r_main).val * 2^32)`
— the *trust ledger*'s `transpile_<OP>` axioms supply the lane
equalities `m.a_0 r_main = lane_lo (state.xreg rs1)` and
`m.a_1 r_main = lane_hi (state.xreg rs1)`. The arithmetic step that
converts those two lane equalities into the packed-BitVec form is
opcode-independent — `bv64_packed_eq_of_lanes` below.

A discharge bridge typically chains:

```
h_input_r1_sail   →   state.xreg rs1 = add_input.r1_val
                          (Sail-state semantics — caller-supplied or
                           derived from `read_xreg`'s definition)

transpile_<OP>    →   m.a_0 r_main = lane_lo (state.xreg rs1)
                  →   m.a_1 r_main = lane_hi (state.xreg rs1)

bv64_packed_eq_of_lanes (this helper)
                  →   state.xreg rs1
                    = BitVec.ofNat 64 ((m.a_0 r_main).val
                                       + (m.a_1 r_main).val * 2^32)

substitute        →   add_input.r1_val
                    = BitVec.ofNat 64 ((m.a_0 r_main).val
                                       + (m.a_1 r_main).val * 2^32)
```

This helper handles the last arithmetic step generically. Each bridge
(BinaryAdd, Binary, BinaryExtension, Arith, Mem) can reuse it
verbatim.
-/

namespace ZiskFv.Equivalence_v1.Bridge.StateBridge

open Goldilocks
open ZiskFv.Trusted

/-- **Packed-lane BitVec reconstruction.** Given a `BitVec 64` whose
    low and high 32-bit lanes have been split into FGL elements via
    `lane_lo` / `lane_hi`, recover the BitVec from the lane values:

    ```
    a_lo = lane_lo bv ∧ a_hi = lane_hi bv  →
      bv = BitVec.ofNat 64 (a_lo.val + a_hi.val * 2^32)
    ```

    This is the opcode-independent arithmetic step shared by every
    discharge bridge's input-bridge derivation. The two hypotheses
    come from a `transpile_<OP>` axiom's conclusion (`m.a_0 = lane_lo
    (state.xreg rs)`, `m.a_1 = lane_hi (state.xreg rs)`); the
    conclusion gives the packed form `r1_val` is expected in.

    Proof: `BitVec.eq_of_toNat_eq`, then
    `lane_lo_val` / `lane_hi_val_eq_div` to express the lane `.val`s
    in terms of `bv.toNat`, then `Nat.mod_add_div` and modular
    arithmetic. -/
lemma bv64_packed_eq_of_lanes
    {bv : BitVec 64} {a_lo a_hi : FGL}
    (h_lo : a_lo = lane_lo bv) (h_hi : a_hi = lane_hi bv) :
    bv = BitVec.ofNat 64 (a_lo.val + a_hi.val * 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have h_lo_val : a_lo.val = bv.toNat % 4294967296 := by
    rw [h_lo]; exact lane_lo_val bv
  have h_hi_val : a_hi.val = bv.toNat / 4294967296 := by
    rw [h_hi]; exact lane_hi_val_eq_div bv
  rw [h_lo_val, h_hi_val]
  have h_decomp : bv.toNat % 4294967296 + bv.toNat / 4294967296 * 4294967296 = bv.toNat := by
    have := Nat.mod_add_div bv.toNat 4294967296; omega
  rw [h_decomp]
  -- Now: bv.toNat = bv.toNat % 2^64. Since bv.toNat < 2^64, the % is a no-op.
  have h_lt : bv.toNat < 18446744073709551616 := by
    have := bv.isLt; simpa using this
  omega

end ZiskFv.Equivalence_v1.Bridge.StateBridge
