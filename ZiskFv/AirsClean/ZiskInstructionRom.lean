import Clean.Circuit.Lookup
import ZiskFv.Channels.ZiskRomBus
import ZiskFv.Field.Goldilocks

/-!
# ZiskInstructionRom — Clean `StaticTable` provider side (Phase T4.0)

ZisK's instruction ROM (`zisk/state-machines/rom/pil/rom.pil`) holds the
transpiled program: each row stores the 11-column instruction tuple at
`line = pc`. Unlike the BinaryTable / BinaryExtensionTable / ArithTable
static providers (whose row content is a deterministic function of the
row index), the ZisK ROM is **program-parameterised**: a different
program produces a different table.

This module exposes the ROM as a Clean `StaticTable` parameterised by
an abstract program (`Program := Fin n → ZiskRomMessage FGL`). The
verification target — `zisk_riscv_compliant_program_bus` — is universal
over the program, so the `Program` parameter flows through unchanged.

The `Spec` is exact decoded-row membership and `contains_iff` is
definitional, matching the large-ROM pattern from
`AirsClean/BinaryTable.lean`.

## Trust note

No axioms. The membership predicate is exact decoded-row membership;
the program-specific *contents* of the ROM flow through as an opaque
parameter rather than being asserted at the table level.

## Phase T4.0 status

This is the provider-side `StaticTable` only. The Main consumer-side
lookup (`mainWithRom` in `AirsClean/Main/Constraints.lean`) and the
extended `MainRow` carrying the 5 ROM-derived offset/store columns plus
the 15 boolean flags are separate T4.0 deliverables. No axiom retires
from this commit alone.
-/

namespace ZiskFv.AirsClean.ZiskInstructionRom

open Goldilocks
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

/-- A ZisK transpiled program: a finite-length sequence of instructions,
    each as a `ZiskRomMessage FGL`. The instruction at position `i` is
    the row Main looks up when `pc = i`.

    The verification quantifies over `Program length` for any
    `length : ℕ`, so this captures "any compiled ZisK program". -/
@[reducible]
def Program (length : ℕ) : Type := Fin length → ZiskRomMessage FGL

/-- ZisK's instruction ROM as a Clean `StaticTable`, parameterised by
    the program. `row i := program i`; `Spec` is exact membership in
    the decoded row set; `contains_iff` is definitional. -/
def romStaticTable (length : ℕ) (program : Program length) :
    StaticTable FGL ZiskRomMessage where
  name := "ZiskInstructionRom"
  length := length
  row i := program i
  -- Index is the line column's `.val` as a Nat — Main's `pc` cell.
  index msg := msg.line.val
  Spec msg := ∃ i, msg = program i
  contains_iff := by
    intro msg
    rfl

end ZiskFv.AirsClean.ZiskInstructionRom
