import ZiskFv.AirsClean.MemAlignWriteByte.Spec
import ZiskFv.AirsClean.RangeTables
import Clean.Circuit.Basic
import ZiskFv.Channels.MemoryBus
import ZiskFv.Channels.DualByte

namespace ZiskFv.AirsClean.MemAlignWriteByte

open Goldilocks
open Circuit (assertZero lookup)
open ZiskFv.AirsClean.RangeTables
open ZiskFv.AirsClean.MemAlignByte (byte_value_factor value_8b_factor value_16b_factor)
open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)
open ZiskFv.Channels.DualByte (DualByteChannel DualByteMessage)

@[reducible]
def dualByteMessageExpr (row : Var MemAlignWriteByteRow FGL) :
    DualByteMessage (Expression FGL) :=
  ⟨row.byte_value, row.value_8b⟩

@[reducible]
def memReadMessageExpr (row : Var MemAlignWriteByteRow FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := 1
    ptr := row.addr_w * 8
    timestamp := row.step
    width := 8
    value_0 := row.sel_high_4b * (row.direct_value - row.composed_value) + row.composed_value
    value_1 := row.sel_high_4b * (row.composed_value - row.direct_value) + row.direct_value }

@[reducible]
def memWriteMessageExpr (row : Var MemAlignWriteByteRow FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := 2
    ptr := row.addr_w * 8
    timestamp := row.step + 1
    width := 8
    value_0 := row.mem_write_values_0
    value_1 := row.mem_write_values_1 }

@[reducible]
def memBusMessageExpr (row : Var MemAlignWriteByteRow FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := 2
    ptr := row.addr_w * 8 + (row.sel_high_4b * 4 + row.sel_high_2b * 2 + row.sel_high_b)
    timestamp := row.step
    width := 1
    value_0 := row.written_byte_value
    value_1 := 0 }

/-- All actual row interactions. Range lookups are exact static membership
models; weighted virtual-provider and segment Direct provenance are separate
obligations, not extra caller assumptions hidden in this circuit. -/
@[circuit_norm]
def main (row : Var MemAlignWriteByteRow FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable8) row.written_byte_value
  lookup (Table.fromStatic rangeTable16) row.value_16b
  lookup (Table.fromStatic dualByteTable) #v[row.byte_value, row.value_8b]
  assertZero (row.sel_high_4b * (1 - row.sel_high_4b))
  assertZero (row.sel_high_2b * (1 - row.sel_high_2b))
  assertZero (row.sel_high_b * (1 - row.sel_high_b))
  assertZero (row.composed_value -
    (row.byte_value * (16777216 * row.sel_high_2b * row.sel_high_b +
      65536 * row.sel_high_2b * (1 - row.sel_high_b) +
      256 * (1 - row.sel_high_2b) * row.sel_high_b +
      (1 - row.sel_high_2b) * (1 - row.sel_high_b)) +
    row.value_8b * (16777216 * row.sel_high_2b * (1 - row.sel_high_b) +
      65536 * row.sel_high_2b * row.sel_high_b +
      256 * (1 - row.sel_high_2b) * (1 - row.sel_high_b) +
      (1 - row.sel_high_2b) * row.sel_high_b) +
    row.value_16b * (65536 * (1 - row.sel_high_2b) + row.sel_high_2b)))
  assertZero (row.written_composed_value -
    (row.written_byte_value * (16777216 * row.sel_high_2b * row.sel_high_b +
      65536 * row.sel_high_2b * (1 - row.sel_high_b) +
      256 * (1 - row.sel_high_2b) * row.sel_high_b +
      (1 - row.sel_high_2b) * (1 - row.sel_high_b)) +
    row.value_8b * (16777216 * row.sel_high_2b * (1 - row.sel_high_b) +
      65536 * row.sel_high_2b * row.sel_high_b +
      256 * (1 - row.sel_high_2b) * (1 - row.sel_high_b) +
      (1 - row.sel_high_2b) * row.sel_high_b) +
    row.value_16b * (65536 * (1 - row.sel_high_2b) + row.sel_high_2b)))
  assertZero (row.mem_write_values_0 -
    (row.sel_high_4b * (row.direct_value - row.written_composed_value) + row.written_composed_value))
  assertZero (row.mem_write_values_1 -
    (row.sel_high_4b * (row.written_composed_value - row.direct_value) + row.direct_value))
  MemBusChannel.pull (memReadMessageExpr row)
  MemBusChannel.pull (memWriteMessageExpr row)
  MemBusChannel.push (memBusMessageExpr row)
  DualByteChannel.pull (dualByteMessageExpr row)

end ZiskFv.AirsClean.MemAlignWriteByte
