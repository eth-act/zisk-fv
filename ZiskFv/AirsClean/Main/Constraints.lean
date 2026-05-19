import ZiskFv.AirsClean.Main.Spec
import Clean.Circuit.Basic

/-!
# Main circuit operations

The 9 F-typed per-row constraints of ZisK's Main AIR. Cross-row
pc_handshake stays in Bridge as a separate adjacency theorem.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Circuit (assertZero)

@[circuit_norm]
def main (row : Var MainRow FGL) : Circuit FGL Unit := do
  assertZero (row.flag * (1 - row.flag))
  assertZero (row.is_external_op * (1 - row.is_external_op))
  assertZero ((1 - row.is_external_op) * (1 - row.op) * row.c_0)
  assertZero ((1 - row.is_external_op) * (1 - row.op) * row.c_1)
  assertZero ((1 - row.is_external_op) * row.op * (row.b_0 - row.c_0))
  assertZero ((1 - row.is_external_op) * row.op * (row.b_1 - row.c_1))
  assertZero ((1 - row.is_external_op) * (1 - row.op) * (1 - row.flag))
  assertZero ((1 - row.is_external_op) * row.op * row.flag)
  assertZero (row.flag * row.set_pc)

end ZiskFv.AirsClean.Main
