import ZiskFv.AirsClean.Binary.Spec
import Clean.Circuit.Basic
import ZiskFv.Channels.OperationBus

/-!
# Binary circuit operations

The 7 F-typed per-row constraints of ZisK's Binary AIR, plus its
operation-bus push. Lookup interactions against `BinaryTable` are NOT in
`main` (they live in the channel-balance layer).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Circuit (assertZero)
open ZiskFv.Channels.OperationBus (OpBusChannel)

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
  OpBusChannel.push
    { op := row.chain.b_op + 16 * row.mode.mode32
      a_lo := row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
        + 65536 * row.aBytes.free_in_a_2 + 16777216 * row.aBytes.free_in_a_3
      a_hi := row.aBytes.free_in_a_4 + 256 * row.aBytes.free_in_a_5
        + 65536 * row.aBytes.free_in_a_6 + 16777216 * row.aBytes.free_in_a_7
      b_lo := row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
        + 65536 * row.bBytes.free_in_b_2 + 16777216 * row.bBytes.free_in_b_3
      b_hi := row.bBytes.free_in_b_4 + 256 * row.bBytes.free_in_b_5
        + 65536 * row.bBytes.free_in_b_6 + 16777216 * row.bBytes.free_in_b_7
      c_lo := row.cBytes.free_in_c_0 + 256 * row.cBytes.free_in_c_1
        + 65536 * row.cBytes.free_in_c_2 + 16777216 * row.cBytes.free_in_c_3
        + row.chain.carry_7
      c_hi := row.cBytes.free_in_c_4 + 256 * row.cBytes.free_in_c_5
        + 65536 * row.cBytes.free_in_c_6 + 16777216 * row.cBytes.free_in_c_7
      flag := row.chain.carry_7
      main_step := 0
      extended_arg := 0
      extra_args_0 := 0 }

@[reducible] def binaryElaborated :
    ElaboratedCircuit FGL BinaryRow unit where
  name := "Binary"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]

end ZiskFv.AirsClean.Binary
