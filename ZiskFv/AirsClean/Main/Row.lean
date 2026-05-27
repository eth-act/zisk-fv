import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# Main row type (Clean ProvableStruct)

The 18-slot witness layout for ZisK's Main AIR. Mirrors
`Valid_Main`'s named columns.

PIL: `zisk/state-machines/main/pil/main.pil`.

## T4.0 ROM-row split

The 16 ROM-derived columns required by `mainWithRom` (5 data columns +
11 boolean flags) live in the companion struct `MainRomRow` below
rather than being added to `MainRow` directly. Clean's
`ProvableStruct` deriving hits a recursion depth limit at ~30 fields,
so the witness layout is split. The combined view is `MainRowWithRom`
(also below), which `mainWithRom` operates on.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks

structure MainRow (F : Type) where
  a_0 : F
  a_1 : F
  b_0 : F
  b_1 : F
  c_0 : F
  c_1 : F
  flag : F
  pc : F
  is_external_op : F
  op : F
  m32 : F
  ind_width : F
  set_pc : F
  jmp_offset1 : F
  jmp_offset2 : F
  store_pc : F
  im_high_degree_2 : F
  segment_l1 : F
deriving ProvableStruct

/-- **T4.0 ROM-row companion.** The 16 ROM-derived columns required by
    `mainWithRom`: 5 data columns (`a_offset_imm0`, `a_imm1`,
    `b_offset_imm0`, `b_imm1`, `store_offset`) + 11 boolean flags
    (the entries in `rom_flags` at `main.pil:483-486` not already in
    `MainRow`).

    Split from `MainRow` to keep both structures below Clean's
    `ProvableStruct` deriving recursion-depth limit. -/
structure MainRomRow (F : Type) where
  /-- `a_imm[0]` operand offset. -/
  a_offset_imm0 : F
  /-- `a_imm[1]` operand high immediate. -/
  a_imm1 : F
  /-- `b_imm[0]` operand offset. -/
  b_offset_imm0 : F
  /-- `b_imm[1]` operand high immediate. -/
  b_imm1 : F
  /-- Destination register or memory offset. -/
  store_offset : F
  /-- a-source-immediate flag (`main.pil:483`, bit 1 of rom_flags). -/
  a_src_imm : F
  /-- a-source-memory flag (bit 2). -/
  a_src_mem : F
  /-- is-precompiled flag (bit 3). -/
  is_precompiled : F
  /-- b-source-immediate flag (bit 4). -/
  b_src_imm : F
  /-- b-source-memory flag (bit 5). -/
  b_src_mem : F
  /-- store-memory flag (bit 8). -/
  store_mem : F
  /-- store-indirect flag (bit 9). -/
  store_ind : F
  /-- b-source-indirect flag (bit 12). -/
  b_src_ind : F
  /-- a-source-register flag (bit 13). -/
  a_src_reg : F
  /-- b-source-register flag (bit 14). -/
  b_src_reg : F
  /-- store-register flag (bit 15). -/
  store_reg : F
deriving ProvableStruct

/-- The combined Main + ROM witness layout, used by `mainWithRom`. -/
structure MainRowWithRom (F : Type) where
  core : MainRow F
  rom : MainRomRow F
deriving ProvableStruct

end ZiskFv.AirsClean.Main
