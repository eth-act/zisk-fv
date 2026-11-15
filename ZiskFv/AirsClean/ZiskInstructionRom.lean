import Clean.Circuit.Lookup
import ZiskFv.Channels.ZiskRomBus
import ZiskFv.Field.Goldilocks

/-!
# ZiskInstructionRom — Clean `StaticTable` provider side (Phase T4.0)

ZisK's instruction ROM (`zisk/state-machines/rom/pil/rom.pil`) holds the
lowered program: each row stores the 11-column instruction tuple at
`line = pc`. Unlike the BinaryTable / BinaryExtensionTable / ArithTable
static providers (whose row content is a deterministic function of the
row index), the ZisK ROM is **program-parameterised**: a different
program produces a different table.

This module exposes an abstract decoded-row sequence as a Clean `StaticTable`
(`Program := Fin n → ZiskRomMessage FGL`). Membership does not establish that
the sequence is the producer's final image, opens public `rom_root`, or comes
from the intended binary. The parameter remains abstract.

The `Spec` is exact decoded-row membership and `contains_iff` is
definitional, matching the large-ROM pattern from
`AirsClean/BinaryTable.lean`.

## Trust note

No axioms. The membership predicate is exact decoded-row membership;
the program-specific *contents* of the ROM flow through as an opaque
parameter rather than being asserted at the table level.

`ZiskInstructionRomImage`, `ZiskInstructionRomProvider`, and
`ZiskInstructionRomSource` give a separate bounded physical-image construction
and source-polynomial correspondence. They do not turn arbitrary decoded rows
into authenticated producer output, or finish a live ROM channel. Main's
current `mainWithRom` consumer remains an internal static-table lookup.
-/

namespace ZiskFv.AirsClean.ZiskInstructionRom

open Goldilocks
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

/-- An abstract finite sequence of decoded ROM rows. A sequence index is NOT
    the instruction's PC: `line` holds that address. The actual producer sorts
    original u64 map keys before field encoding and pads its final image.
    This type carries neither those original keys nor a source-history or
    public-root authentication proof. -/
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
