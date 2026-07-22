import Clean.Circuit.Lookup
import Extraction.MemAlignRom
import ZiskFv.Channels.MemAlignRom

/-!
# MemAlignRom — exact extracted static-table provider

The virtual MemAlign ROM is absent from pilout's AIR list. Its 256 physical
rows are extracted from the fixed `OFFSET`/`WIDTH` columns and row builder in
`zisk/state-machines/mem/pil/mem_align_rom.pil:6-313`, with table id/size and
padding-row index checked against
`zisk/state-machines/mem/src/mem_align_rom_sm.rs::MemAlignRomSM`.

All physical rows are preserved. In particular, the 68 reset-padding rows are
the exact tuple `[0, 0, 0, 0, 0, 512]`, not an all-zero row.

## Trust note

No axioms. `Spec` is exact membership in the 256 extracted rows and
`contains_iff` is definitional.
-/

namespace ZiskFv.AirsClean.MemAlignRomTable

open Goldilocks
open ZiskFv.Channels.MemAlignRom

def tableSize : ℕ := Extraction.MemAlignRom.tableSize

/-- The extracted fixed row at a valid physical MemAlign ROM index. -/
def rowOfIndex (i : Fin tableSize) : MemAlignRomMessage FGL :=
  let row := Extraction.MemAlignRom.rows[i]
  { pc := row.pc
    deltaPc := row.deltaPc
    deltaAddr := row.deltaAddr
    offset := row.offset
    width := row.width
    flags := row.flags }

/-- Exact membership in the extracted 256-row virtual table. -/
def memAlignRomTable : StaticTable FGL MemAlignRomMessage where
  name := "mem_align_rom"
  length := tableSize
  row i := rowOfIndex i
  index t := t.pc.val
  Spec t := ∃ i : Fin tableSize, t = rowOfIndex i
  contains_iff := by intro t; rfl

theorem spec_iff (t : MemAlignRomMessage FGL) :
    memAlignRomTable.Spec t ↔ ∃ i : Fin tableSize, t = rowOfIndex i := Iff.rfl

end ZiskFv.AirsClean.MemAlignRomTable
