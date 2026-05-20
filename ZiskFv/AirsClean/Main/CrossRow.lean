import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.Airs.Main.Main

/-!
# Main cross-row PC handshake adjacency predicate

Phase B.1 follow-up to Phase B (`a456e0d`). The 9 F-typed per-row
constraints of `Valid_Main` ported in Phase B do NOT include the
cross-row PC handshake, which relates `pc(row)` to the previous row's
witness cells through the `set_pc` / `jmp_offset1` / `jmp_offset2`
multiplexer.

This file defines `pc_handshake_at` — the adjacency predicate that
*lives outside the per-row Clean Component* (which is intentionally
single-row). The closed form is **identical** to v1's
`ZiskFv.Airs.Main.pc_handshake` so the Bridge can pass through caller
hypotheses unchanged; the v1 record's `pc_handshake` constraint IS
this predicate evaluated at row `r`.

## Boot-row case

At `row = 0`, the closed form mentions `v.… (row - 1) = v.… 0` because
`ℕ.sub` saturates. The `(1 - segment_l1 row)` gate evaluates to `0`
at row 0 (by definition `SEGMENT_L1 = 1` on the boot row), so the
misaligned subterm is multiplied out. This is the same soundness
argument captured by `pc_handshake_to_next_pc` in
`ZiskFv/Airs/Main/Main.lean:224-239`.

See `ZiskFv/Airs/Main/Main.lean:168-198` for the original definition
and full extractor-notes commentary.

## Trust note

No axioms. `pc_handshake_at` is a caller-supplied hypothesis that the
downstream opcode-level proof discharges via the v1 record's
`pc_handshake` constraint (which is definitionally this predicate).
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **PC handshake adjacency at row `row`** (`main.pil:410`). Closed
    form of the PIL constraint relating `pc row` to the previous
    row's witness cells via the `set_pc` / `jmp_offset1` /
    `jmp_offset2` multiplexer:

    `(1 - segment_l1 row) * (pc row - expected_current_pc(row - 1)) = 0`

    where `expected_current_pc` evaluates against the previous row's
    witness cells:

    `expected_current_pc = 'set_pc * ('c[0] + 'jmp_offset1)
                         + (1 - 'set_pc) * ('pc + 'jmp_offset2)
                         + 'flag * ('jmp_offset1 - 'jmp_offset2)`.

    At `row = 0`, the `(1 - segment_l1)` gate makes the constraint
    vacuous — `SEGMENT_L1 = 1` there by definition — so the `ℕ.sub`
    saturation `0 - 1 = 0` in the previous-row accessors is multiplied
    out. See `ZiskFv/Airs/Main/Main.lean:181-186` for the extractor-
    notes argument.

    **Identity to v1.** `pc_handshake_at v r ≡ ZiskFv.Airs.Main.pc_handshake v r`
    (same closed-form expression). The downstream opcode-level proof
    consumes the v1 record's `pc_handshake` constraint, which is
    definitionally this predicate at row `r`. -/
def pc_handshake_at (v : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ) : Prop :=
  (1 - v.segment_l1 row) *
    (v.pc row -
      (v.set_pc (row - 1) * (v.c_0 (row - 1) + v.jmp_offset1 (row - 1))
        + (1 - v.set_pc (row - 1)) * (v.pc (row - 1) + v.jmp_offset2 (row - 1))
        + v.flag (row - 1) * (v.jmp_offset1 (row - 1) - v.jmp_offset2 (row - 1)))) = 0

/-- Definitional identity with the v1 named-column predicate
    `ZiskFv.Airs.Main.pc_handshake`. Holds by `rfl` once both sides
    unfold (both `@[simp]`/`def` open to the same expression).

    Consumers downstream of Phase D (after the v1 `Valid_Main` record
    is retired) will rephrase against `pc_handshake_at`. Until then,
    this lemma lets Bridge.spec_of_valid-style theorems hand a v1
    hypothesis through unchanged. -/
theorem pc_handshake_at_iff_v1
    (v : ZiskFv.Airs.Main.Valid_Main C FGL FGL) (row : ℕ) :
    pc_handshake_at v row ↔ ZiskFv.Airs.Main.pc_handshake v row := by
  unfold pc_handshake_at ZiskFv.Airs.Main.pc_handshake
  rfl

end ZiskFv.AirsClean.Main
