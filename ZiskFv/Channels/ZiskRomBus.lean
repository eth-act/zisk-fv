import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# ZiskRomBus typed channel (Phase T4.0)

ZisK's instruction ROM bus (`bus_id = ROM_BUS_ID`,
`zisk/state-machines/rom/pil/rom.pil:6`). Main consumes the bus per row
to look up the transpiled instruction at the current `pc`; the ROM AIR
(a `StaticTable` parameterized by the user's compiled program) provides
the 11-slot tuple.

PIL citations:
* `rom.pil:24-25` — provider-side
  `lookup_proves(rom_bus_id, [line, a_offset_imm0, a_imm1, b_offset_imm0,
   b_imm1, ind_width, op, store_offset, jmp_offset1, jmp_offset2, flags],
   mul: multiplicity)`
* `main.pil:490-491` — consumer-side
  `lookup_assumes(ROM_BUS_ID, [pc, a_offset_imm0, a_imm1, b_offset_imm0,
   b_imm1, ind_width, op, store_offset, jmp_offset1, jmp_offset2, rom_flags])`

The 11 slots:
1. `line` — the row identifier (= `pc` on Main's side).
2. `a_offset_imm0` — operand `a` offset / `a_imm[0]`.
3. `a_imm1` — operand `a` high immediate.
4. `b_offset_imm0` — operand `b` offset / `b_imm[0]`.
5. `b_imm1` — operand `b` high immediate.
6. `ind_width` — indirect access width.
7. `op` — operation code.
8. `store_offset` — destination register/offset.
9. `jmp_offset1`, `jmp_offset2` — branch / jump offsets.
10. `flags` — packed 15-boolean instruction flags
    (per `main.pil:483-486`: `1 + 2*a_src_imm + 4*a_src_mem + 8*is_precompiled
    + 16*b_src_imm + 32*b_src_mem + 64*is_external_op + 128*store_pc
    + 256*store_mem + 512*store_ind + 1024*set_pc + 2048*m32
    + 4096*b_src_ind + 8192*a_src_reg + 16384*b_src_reg + 32768*store_reg`).

## Trust note

No axioms. The channel's `Guarantees` is `True` — a structural pipe.
Cross-AIR consistency (ROM lookup soundness) is `Clean.Air.Balance`'s
output (a theorem once the ensemble closes); per-row instruction
semantics flow through the canonical wrappers, not through the channel
guarantee. Mirrors the no-axiom contract of the other channels in
`ZiskFv/Channels/`.
-/

namespace ZiskFv.Channels.ZiskRomBus

open Goldilocks

/-- The 11-slot ZisK instruction-ROM lookup tuple. Mirrors PIL's
    `lookup_assumes(ROM_BUS_ID, [...])` shape exactly. Per-row Main
    pushes one of these; the program's static ROM provides the
    corresponding rows. -/
structure ZiskRomMessage (F : Type) where
  /-- Row identifier — `pc` on the Main consumer side, `line` on the
      ROM provider side. -/
  line : F
  /-- `a_imm[0]` operand offset. -/
  a_offset_imm0 : F
  /-- `a_imm[1]` operand high immediate. -/
  a_imm1 : F
  /-- `b_imm[0]` operand offset. -/
  b_offset_imm0 : F
  /-- `b_imm[1]` operand high immediate. -/
  b_imm1 : F
  /-- Indirect access width (1/2/4/8 for memory ops, 0 for non-memory). -/
  ind_width : F
  /-- Operation code (ZisK's per-opcode literal). -/
  op : F
  /-- Destination register or memory offset. -/
  store_offset : F
  /-- Branch-taken offset (jump target — pc + jmp_offset1 when `flag=1`). -/
  jmp_offset1 : F
  /-- Branch-not-taken / unconditional jump offset. -/
  jmp_offset2 : F
  /-- Packed 15-boolean flags (see file docstring for bit layout). -/
  flags : F
deriving ProvableStruct

/-- The ZisK instruction-ROM bus channel. As with the other channels in
    `ZiskFv/Channels/`, the guarantee is `True`: cross-AIR consistency
    is enforced by `Air.Balance`, and per-row instruction semantics are
    layered in via the canonical wrappers. -/
instance ZiskRomBusChannel : Channel FGL ZiskRomMessage where
  name := "ZiskInstructionRom"
  Guarantees _msg _data := True

end ZiskFv.Channels.ZiskRomBus
