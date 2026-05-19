import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# BinaryAdd row type (Clean ProvableStruct)

The 13-slot witness layout for ZisK's BinaryAdd AIR, expressed as a
`ProvableStruct` for consumption by a Clean `GeneralFormalCircuit`.

Slot semantics (from `zisk/state-machines/binary/binary_add.pil`):

* `a_0`, `a_1`         — operand a, low/high 32-bit halves
* `b_0`, `b_1`         — operand b
* `c_chunks_0..3`      — result c, four 16-bit chunks
* `cout_0`, `cout_1`   — carries between 32-bit halves
* `gsum`               — extension-field accumulator (stage-2; ignored by the channel-balance model)
* `im_0`, `im_1`       — intermediate selectors

`gsum`, `im_0`, `im_1` are stage-2 columns; Clean's channel-balance
machinery subsumes them so we don't carry them on the typed row used
for the Component. The row defined here is the *witness-only* slice
that the Clean Component constrains directly.

## Trust note

No axiom added — this is a pure data definition. Soundness proofs
follow in `Soundness.lean` (next PR in the BinaryAdd series), which
will then back the existing `Valid_BinaryAdd` interface and let us
retire the `op_bus_perm_sound_BinaryAdd`-derived axiom edge from the
trust ledger.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks

/-- The 10-column witness row for BinaryAdd (gsum + im_0/1 omitted —
    stage-2 / channel-implicit). -/
structure BinaryAddRow (F : Type) where
  a_0 : F
  a_1 : F
  b_0 : F
  b_1 : F
  c_chunks_0 : F
  c_chunks_1 : F
  c_chunks_2 : F
  c_chunks_3 : F
  cout_0 : F
  cout_1 : F
deriving ProvableStruct

/-- The 32-bit packed value of a two-half lane. -/
@[reducible]
def packed32 (lo hi : FGL) : ℕ := lo.val + hi.val * 2 ^ 32

/-- The 64-bit packed value reconstructed from four 16-bit chunks. -/
@[reducible]
def cPacked (row : BinaryAddRow FGL) : ℕ :=
  (row.c_chunks_0.val + row.c_chunks_1.val * 2 ^ 16) +
  (row.c_chunks_2.val + row.c_chunks_3.val * 2 ^ 16) * 2 ^ 32

end ZiskFv.AirsClean.BinaryAdd
