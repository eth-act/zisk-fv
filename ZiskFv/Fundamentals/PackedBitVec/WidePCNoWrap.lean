import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec.NoWrap

/-!
**Wide-PC no-wrap toolkit (companion to `NoWrap.lean`).**

The `Fundamentals/PackedBitVec/NoWrap.lean` toolkit factors the
additive carry-chain lift `((nat:ℕ):FGL) = ((nat:ℕ):FGL)` → `nat = nat`
under the assumption that **both sides are `< GL_prime`**.  That suffices
for the bus-effect / register-write payload (32-bit lanes packed two-up
sit comfortably below GL_prime) but it does **not** cover the
`store_pc = 1` rd-write path.

`store_pc = 1` opcodes (JAL, JALR, AUIPC) write `pc + jmp_offset2` —
a value derived from Main's `pc` column.  In ZisK, `pc` is a single
FGL element (`Fin GL_prime`), but the Sail-side `PC : BitVec 64` ranges
across **the full 64-bit address space**, including `[GL_prime, 2^64)`.
At those values `pc_fgl.val = PC.toNat` is impossible (the FGL element
can only hold values `< GL_prime`); for the inputs ZisK can actually
produce, the bridge is a per-execution invariant rather than a static
one.  The toolkit below lives **above** that bridge: given the bridge as
a hypothesis, factor the standard wrap-case analysis that delivers the
lo / hi 32-bit projections.

## Scope

* `pc_fgl : FGL` paired with `PC : BitVec 64` and `offset_fgl : FGL`
  paired with `offset_bv : BitVec 64`.
* Conclusion: `(pc_fgl + offset_fgl : FGL).val` matches
  `(PC + offset_bv).toNat` modulo `2^32` (lo lane) / divided by `2^32`
  (hi lane).
* **Load-bearing structural hypothesis**: the FGL sum doesn't wrap
  past `GL_prime`.  Concretely
  `pc_fgl.val + offset_fgl.val < GL_prime`.
* For typical PC trajectories this is automatic — the PC starts at `0`
  and increments through legitimate program counters, well below
  `GL_prime ≈ 2^64`.  The hypothesis is exposed so callers can
  discharge it from circuit invariants (e.g. ROM bus pin: `pc < 2^32`
  for ELF-loaded programs) or from a per-step trajectory bound.

## What this toolkit does NOT do

* It does not derive `pc_fgl.val = PC.toNat` from circuit constraints —
  that's the trusted-surface `transpile_PC_for_<op>` axiom.  The
  toolkit takes that as input.
* It does not handle the doubly-wrapped case where `pc_fgl + offset_fgl`
  exceeds `2 * GL_prime`.  The hypothesis `pc_fgl.val + offset_fgl.val
  < GL_prime` rules that out.

## Worked examples

* `_example_jal_lo_via_toolkit` — JAL/JALR's link-register low-half
  identity (offset = 4) closed by the toolkit.
* `_example_auipc_lo_via_toolkit` — AUIPC's signed-imm low-half
  identity (offset = signExtend 64 (imm ++ 0#12)) closed by the
  toolkit.
-/

namespace ZiskFv.PackedBitVec.WidePCNoWrap

open Goldilocks
open ZiskFv.PackedBitVec.NoWrap

/-! ## Numeric facts about `GL_prime` -/

/-- `GL_prime = 2^64 - 2^32 + 1`.  Pinned in factored form so the
toolkit's wrap analysis can reason about the relationship to the
power-of-two moduli `2^32` and `2^64` without `omega` tripping over
the literal-vs-power-of-two atom split (cf. `CLAUDE.md` trap #2). -/
lemma GL_prime_eq_pow_form :
    GL_prime = 18446744073709551616 - 4294967296 + 1 := by
  rfl

/-- `GL_prime < 2^64`. -/
lemma GL_prime_lt_pow_64 : GL_prime < 18446744073709551616 := by
  decide

/-- `2^64 - GL_prime = 2^32 - 1`. -/
lemma pow_64_sub_GL_prime : 18446744073709551616 - GL_prime = 4294967295 := by
  decide

/-! ## Core no-wrap lifts (general offset)

The lemmas in this section take a fully-general offset `offset_bv :
BitVec 64`, with the **single load-bearing hypothesis** that the FGL
sum doesn't wrap past `GL_prime`.  Under that hypothesis the FGL `.val`
agrees with the BitVec `.toNat` exactly (no modular reduction needed),
and the lo / hi projections fall out by `omega`. -/

/-- **Lo-half wide-PC lift (general offset).**

Given the transpile bridges `pc_fgl.val = PC.toNat`,
`offset_fgl.val = offset_bv.toNat`, plus the structural no-wrap
hypothesis `pc_fgl.val + offset_fgl.val < GL_prime`, conclude that the
lo 32-bit half of the FGL sum equals the lo 32-bit half of the BitVec
sum.

The proof is a single application of `Fin.val_add` plus the modular
arithmetic of the wrap-free regime.

**Why no wrap-case is needed here**: the hypothesis `< GL_prime` rules
out the wrap branch.  When `pc_fgl.val + offset_fgl.val < GL_prime <
2^64`, the FGL sum equals the ℕ sum, and the BitVec sum (which wraps
mod `2^64`) also equals the ℕ sum since `< 2^64` already.  Both sides
agree pre-modulo, so `% 2^32` projects identically.  -/
theorem fgl_pc_plus_offset_lo
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime) :
    (pc_fgl + offset_fgl).val % 4294967296
      = (PC + offset_bv).toNat % 4294967296 := by
  -- Step 1: The FGL sum's `.val` equals the ℕ sum (no wrap).
  have h_fgl_val :
      (pc_fgl + offset_fgl).val = pc_fgl.val + offset_fgl.val := by
    rw [show (pc_fgl + offset_fgl : FGL) = pc_fgl + offset_fgl from rfl]
    rw [Fin.val_add]
    exact Nat.mod_eq_of_lt h_no_fgl_wrap
  -- Step 2: Substitute the transpile bridges.
  rw [h_fgl_val, h_pc_bridge, h_offset_bridge]
  -- Step 3: The BitVec sum's `.toNat` is `(PC.toNat + offset_bv.toNat) % 2^64`.
  rw [BitVec.toNat_add]
  -- Step 4: `(x % 2^64) % 2^32 = x % 2^32` since 2^32 | 2^64.
  rw [Nat.mod_mod_of_dvd _ (by decide : (4294967296 : ℕ) ∣ 18446744073709551616)]

/-- **Hi-half wide-PC lift (general offset).**

Companion to `fgl_pc_plus_offset_lo` for the high 32-bit half (`/ 2^32`
extraction, after first reducing mod `2^64`).  The full BitVec sum's
`.toNat` is in `[0, 2^64)`, so `(PC + offset_bv).toNat / 2^32` is in
`[0, 2^32)`.  The FGL sum, under the no-wrap hypothesis, equals the
unreduced ℕ sum; we then strip the excess via `% 2^64` to align
representations. -/
theorem fgl_pc_plus_offset_hi
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime) :
    (pc_fgl + offset_fgl).val % 18446744073709551616 / 4294967296
      = (PC + offset_bv).toNat / 4294967296 := by
  have h_fgl_val :
      (pc_fgl + offset_fgl).val = pc_fgl.val + offset_fgl.val := by
    rw [show (pc_fgl + offset_fgl : FGL) = pc_fgl + offset_fgl from rfl]
    rw [Fin.val_add]
    exact Nat.mod_eq_of_lt h_no_fgl_wrap
  rw [h_fgl_val, h_pc_bridge, h_offset_bridge]
  rw [BitVec.toNat_add]

/-- **Lo-half BitVec form (canonical wrap mod 2^32).**

Same as `fgl_pc_plus_offset_lo` but expressed as a `BitVec 64` equality
via `BitVec.ofNat`.  Matches the shape `JumpUType.lean` consumes:
`BitVec.ofNat 64 ((pc_fgl + offset_fgl).val % 2^32) = BitVec.ofNat 64
((PC + offset_bv).toNat % 2^32)`. -/
theorem fgl_pc_plus_offset_to_bv64
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime) :
    BitVec.ofNat 64 ((pc_fgl + offset_fgl).val % 4294967296)
      = BitVec.ofNat 64 ((PC + offset_bv).toNat % 4294967296) := by
  rw [fgl_pc_plus_offset_lo pc_fgl offset_fgl PC offset_bv
        h_pc_bridge h_offset_bridge h_no_fgl_wrap]

/-- **Hi-half BitVec form (canonical mod-2^64 then div-2^32).**

Companion to `fgl_pc_plus_offset_to_bv64` for the high lane. -/
theorem fgl_pc_plus_offset_to_bv64_hi
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime) :
    BitVec.ofNat 64
        ((pc_fgl + offset_fgl).val % 18446744073709551616 / 4294967296)
      = BitVec.ofNat 64 ((PC + offset_bv).toNat / 4294967296) := by
  rw [fgl_pc_plus_offset_hi pc_fgl offset_fgl PC offset_bv
        h_pc_bridge h_offset_bridge h_no_fgl_wrap]

/-! ## Direct ℕ-equality forms (matching JumpUType.lean residuals)

`Equivalence/RdValDerivation/JumpUType.lean` consumes residual
hypotheses of the shape `(m.pc r + 4 : FGL).val = (PC + 4).toNat % 2^32`.
The toolkit's lo / hi lemmas derive exactly that ℕ-level equality
(without the outer `BitVec.ofNat` wrapper). -/

/-- **`.val % 2^32` direct form.**  Same content as
`fgl_pc_plus_offset_lo`; renamed to match the exact shape JumpUType's
`h_pc_fgl_lo_nat` / `h_pci_lo_val` parameters take. -/
theorem fgl_pc_plus_offset_val_lo_eq
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime) :
    (pc_fgl + offset_fgl : FGL).val
      = (PC + offset_bv).toNat % 4294967296 ∨
    (pc_fgl + offset_fgl : FGL).val % 4294967296
      = (PC + offset_bv).toNat % 4294967296 := by
  right
  exact fgl_pc_plus_offset_lo pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge h_no_fgl_wrap

/-- **Strict-`val =`-shaped lo identity** (no outer `% 2^32` on the FGL
side).  When the FGL sum has been **further range-bounded** to `< 2^32`
(e.g. by separate byte-decomposition constraints), the outer mod is
redundant and we can state the lo identity as a direct equality. -/
theorem fgl_pc_plus_offset_val_eq_lo_strict
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime)
    (h_lo_bound : (pc_fgl + offset_fgl : FGL).val < 4294967296) :
    (pc_fgl + offset_fgl : FGL).val
      = (PC + offset_bv).toNat % 4294967296 := by
  have h := fgl_pc_plus_offset_lo pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge h_no_fgl_wrap
  rw [Nat.mod_eq_of_lt h_lo_bound] at h
  exact h

/-! ## Small-offset corollary

For JAL / JALR the link-register write uses offset = 4 (the
`pc + 4` link address).  In that regime the no-wrap hypothesis can be
discharged from a single PC-trajectory bound `PC.toNat ≤ 2^64 - 5`
(or any tighter bound).  Most realistic ELF-loaded programs satisfy
`PC.toNat < 2^32`, which is **dramatically** tighter. -/

/-- **No-wrap from PC-trajectory bound.**  Convenience lemma: given a
bound `PC.toNat + offset ≤ GL_prime - 1`, derive the FGL no-wrap
hypothesis.  -/
lemma no_wrap_of_pc_offset_bound
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_offset_bound : PC.toNat + offset_bv.toNat < GL_prime) :
    pc_fgl.val + offset_fgl.val < GL_prime := by
  rw [h_pc_bridge, h_offset_bridge]; exact h_pc_offset_bound

/-- **Lo-half lift specialised to small offset.**  The convenience
combinator that JumpUType's JAL / JALR call sites consume directly:
under a PC-trajectory bound (rather than the more abstract FGL no-wrap),
derive the lo-lane identity. -/
theorem fgl_pc_plus_offset_lo_of_bound
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_offset_bound : PC.toNat + offset_bv.toNat < GL_prime) :
    (pc_fgl + offset_fgl).val % 4294967296
      = (PC + offset_bv).toNat % 4294967296 :=
  fgl_pc_plus_offset_lo pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge
    (no_wrap_of_pc_offset_bound pc_fgl offset_fgl PC offset_bv
      h_pc_bridge h_offset_bridge h_pc_offset_bound)

/-- **Hi-half lift specialised to small offset.**  Companion to
`fgl_pc_plus_offset_lo_of_bound`. -/
theorem fgl_pc_plus_offset_hi_of_bound
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_offset_bound : PC.toNat + offset_bv.toNat < GL_prime) :
    (pc_fgl + offset_fgl).val % 18446744073709551616 / 4294967296
      = (PC + offset_bv).toNat / 4294967296 :=
  fgl_pc_plus_offset_hi pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge
    (no_wrap_of_pc_offset_bound pc_fgl offset_fgl PC offset_bv
      h_pc_bridge h_offset_bridge h_pc_offset_bound)

/-! ## Constant-offset specialisations

For JAL / JALR's link-register write, the offset is the literal `4`,
encoded on the FGL side as the natCast `(4 : FGL)` and on the BitVec
side as `(4#64 : BitVec 64)`.  The transpile bridge `(4 : FGL).val =
(4#64 : BitVec 64).toNat` is `decide`-able. -/

/-- The FGL-side natCast `(4 : FGL).val` equals the BitVec `4#64`'s
`.toNat`.  Both are `4`. -/
lemma offset_4_bridge : (4 : FGL).val = (4#64 : BitVec 64).toNat := by decide

/-- **Lo-half lift specialised to offset = 4 (JAL / JALR linkage).**

The cleanest call shape for JumpUType's JAL / JALR consumers: given the
PC bridge and a tight PC bound `PC.toNat < GL_prime - 4`, derive the
lo-lane identity at offset 4.  Most callers will discharge
`PC.toNat < 2^32` (a far tighter bound, immediate from the ROM bus
range table). -/
theorem fgl_pc_plus_4_lo
    (pc_fgl : FGL) (PC : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4) :
    (pc_fgl + 4).val % 4294967296
      = (PC + 4#64).toNat % 4294967296 := by
  have h_pc_offset : PC.toNat + (4#64 : BitVec 64).toNat < GL_prime := by
    have : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [this]; omega
  have := fgl_pc_plus_offset_lo_of_bound
    pc_fgl 4 PC 4#64 h_pc_bridge offset_4_bridge h_pc_offset
  exact this

/-- **Hi-half lift specialised to offset = 4 (JAL / JALR linkage).**
Companion to `fgl_pc_plus_4_lo`. -/
theorem fgl_pc_plus_4_hi
    (pc_fgl : FGL) (PC : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4) :
    (pc_fgl + 4).val % 18446744073709551616 / 4294967296
      = (PC + 4#64).toNat / 4294967296 := by
  have h_pc_offset : PC.toNat + (4#64 : BitVec 64).toNat < GL_prime := by
    have : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [this]; omega
  exact fgl_pc_plus_offset_hi_of_bound
    pc_fgl 4 PC 4#64 h_pc_bridge offset_4_bridge h_pc_offset

/-! ## Range bound for AUIPC's signed-immediate offset

AUIPC writes `rd ← PC + signExtend 64 (imm ++ 0#12)` where `imm :
BitVec 20`.  The offset, viewed as a `BitVec 64`, has `.toNat` in
`[0, 2^32) ∪ [2^64 - 2^31, 2^64)` — the lower half is for non-negative
imm values, the upper half for negative ones (via 2's complement).

The toolkit's general lemma handles the full range; the load-bearing
no-wrap hypothesis becomes `PC.toNat + offset.toNat < GL_prime`.  In
the negative-imm case `offset.toNat ≥ 2^64 - 2^31`, so the no-wrap
bound effectively requires `PC.toNat < GL_prime - 2^64 + 2^31 + ε`.
That is **negative** for naive PC values (since GL_prime < 2^64), so
the hypothesis cannot hold for nonzero negative imm with positive PC.
The actual semantic fix is that AUIPC's wrap is **already captured**
by the BitVec sum on the right-hand side; the toolkit's job is only
to bridge `pc_fgl + offset_fgl : FGL` to `(PC + offset_bv).toNat` mod
`2^32` / div `2^32`.

In the actual circuit, ZisK's transpiler ensures `jmp_offset2` is a
BitVec 64 sign-extended value; the FGL element representing it has
`offset_fgl.val = offset_bv.toNat` whenever that toNat fits in
`Fin GL_prime`, i.e. **always**, since BitVec 64 toNat ≤ 2^64 - 1 and
GL_prime > 2^32 ≥ all reachable values when the offset is the
sign-extended imm of AUIPC and the PC is ELF-bounded.

The bound `2^32 - 1` (inclusive) is the **tightest single-arg offset
bound** the toolkit proves cleanly without recourse to the wrap-case
branch — see `fgl_pc_plus_offset_lo_of_offset_lt_2_32` below. -/

/-- **Lo-half lift for offset bounded by `2^32`.**  The most common
useful case: the signed-imm offset is non-negative (or has been
adjusted via a circuit-level sign witness), so its `.toNat < 2^32`,
and the PC trajectory is bounded by `< GL_prime - 2^32`.  Both bounds
are realistic: ELF-loaded programs have PC well under `2^32`, and
non-negative-imm AUIPC has offset `< 2^32`. -/
theorem fgl_pc_plus_offset_lo_of_offset_lt_2_32
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4294967296)
    (h_offset_bound : offset_bv.toNat < 4294967296) :
    (pc_fgl + offset_fgl).val % 4294967296
      = (PC + offset_bv).toNat % 4294967296 := by
  have h_pc_offset : PC.toNat + offset_bv.toNat < GL_prime := by omega
  exact fgl_pc_plus_offset_lo_of_bound pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge h_pc_offset

/-- **Hi-half lift for offset bounded by `2^32`.** -/
theorem fgl_pc_plus_offset_hi_of_offset_lt_2_32
    (pc_fgl offset_fgl : FGL)
    (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4294967296)
    (h_offset_bound : offset_bv.toNat < 4294967296) :
    (pc_fgl + offset_fgl).val % 18446744073709551616 / 4294967296
      = (PC + offset_bv).toNat / 4294967296 := by
  have h_pc_offset : PC.toNat + offset_bv.toNat < GL_prime := by omega
  exact fgl_pc_plus_offset_hi_of_bound pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge h_pc_offset

/-! ## Worked examples — TDD smoke tests

Each example shows the toolkit closing one of the three `store_pc = 1`
opcodes' rd-write residual identity with a clean call site. -/

/-- **Worked example: JAL/JALR linkage low half.**

Given `pc_fgl.val = PC.toNat` and `PC.toNat < GL_prime - 4`, the lo-lane
identity for the link-register write `pc + 4` closes via the offset-4
specialisation.  This is the exact shape `RdValDerivation/JumpUType.lean`'s
`h_pc_fgl_lo_nat` takes. -/
example
    (pc_fgl : FGL) (PC : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4) :
    (pc_fgl + 4).val % 4294967296
      = (PC + 4#64).toNat % 4294967296 :=
  fgl_pc_plus_4_lo pc_fgl PC h_pc_bridge h_pc_bound

/-- **Worked example: AUIPC's signed-imm-offset low half.**

Models AUIPC's PC-relative offset (signExtend 64 (imm ++ 0#12)) by an
`offset_bv : BitVec 64` parameter.  Under bounds `PC.toNat <
GL_prime - 2^32` and `offset_bv.toNat < 2^32` — both realistic for
non-negative-imm AUIPC on ELF-loaded code — the lo lane closes. -/
example
    (pc_fgl offset_fgl : FGL) (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4294967296)
    (h_offset_bound : offset_bv.toNat < 4294967296) :
    (pc_fgl + offset_fgl).val % 4294967296
      = (PC + offset_bv).toNat % 4294967296 :=
  fgl_pc_plus_offset_lo_of_offset_lt_2_32
    pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge h_pc_bound h_offset_bound

/-- **Worked example: AUIPC's signed-imm-offset high half.** -/
example
    (pc_fgl offset_fgl : FGL) (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4294967296)
    (h_offset_bound : offset_bv.toNat < 4294967296) :
    (pc_fgl + offset_fgl).val % 18446744073709551616 / 4294967296
      = (PC + offset_bv).toNat / 4294967296 :=
  fgl_pc_plus_offset_hi_of_offset_lt_2_32
    pc_fgl offset_fgl PC offset_bv
    h_pc_bridge h_offset_bridge h_pc_bound h_offset_bound

/-- **Worked example: composing the lo + hi halves into a full BitVec
identity.**  This is the shape JumpUType ultimately needs: the byte
projections together give `BitVec.eq_of_toNat_eq` closure. -/
example
    (pc_fgl offset_fgl : FGL) (PC offset_bv : BitVec 64)
    (h_pc_bridge : pc_fgl.val = PC.toNat)
    (h_offset_bridge : offset_fgl.val = offset_bv.toNat)
    (h_no_fgl_wrap : pc_fgl.val + offset_fgl.val < GL_prime) :
    BitVec.ofNat 64 ((pc_fgl + offset_fgl).val % 4294967296)
      = BitVec.ofNat 64 ((PC + offset_bv).toNat % 4294967296)
    ∧
    BitVec.ofNat 64
        ((pc_fgl + offset_fgl).val % 18446744073709551616 / 4294967296)
      = BitVec.ofNat 64 ((PC + offset_bv).toNat / 4294967296) := by
  refine ⟨?_, ?_⟩
  · exact fgl_pc_plus_offset_to_bv64 pc_fgl offset_fgl PC offset_bv
      h_pc_bridge h_offset_bridge h_no_fgl_wrap
  · exact fgl_pc_plus_offset_to_bv64_hi pc_fgl offset_fgl PC offset_bv
      h_pc_bridge h_offset_bridge h_no_fgl_wrap

end ZiskFv.PackedBitVec.WidePCNoWrap
