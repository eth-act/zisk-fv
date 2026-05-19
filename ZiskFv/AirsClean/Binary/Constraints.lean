import ZiskFv.AirsClean.Binary.Spec
import Clean.Circuit.Basic

/-!
# Binary circuit operations

The 7 F-typed per-row constraints of ZisK's Binary AIR. Lookup
interactions against `BinaryTable` are NOT in `main` (they live in
the channel-balance layer).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var BinaryRow FGL) : Circuit FGL Unit := do
  assertZero (row.mode.mode32 * (1 - row.mode.mode32))
  assertZero (row.chain.carry_7 * (1 - row.chain.carry_7))
  assertZero (row.mode.result_is_a * (1 - row.mode.result_is_a))
  assertZero (row.mode.use_first_byte * (1 - row.mode.use_first_byte))
  assertZero (row.mode.c_is_signed * (1 - row.mode.c_is_signed))
  assertZero (row.chain.b_op_or_sext
    - (row.mode.mode32 * (row.mode.c_is_signed + 512 - row.chain.b_op)
       + row.chain.b_op))
  assertZero (row.mode.mode32_and_c_is_signed
    - row.mode.mode32 * row.mode.c_is_signed)

end ZiskFv.AirsClean.Binary
