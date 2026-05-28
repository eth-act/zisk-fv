import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Compliance.SharedBundles
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.SailSpec.ld
import ZiskFv.SailSpec.sd
import ZiskFv.SailSpec.sb
import ZiskFv.SailSpec.sh
import ZiskFv.SailSpec.sw

/-!
# Clean memory-bus bridge adapters

Composes the Clean Main/Mem memory-bus message adapters with the existing
legacy load proof shapes. This file is intentionally separate from
`Bridge.Mem`: the old module still exposes the axiom-backed entry points,
while this one is the lookup-free migration target for T4.

No new axioms.
-/

namespace ZiskFv.EquivCore.Bridge.MemClean

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBus
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf byteOf_val_eq byteOf_val_lt_256)

private theorem byteOf_lane_lo_extract_0 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_lo v) 0 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 7 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 7 0).toNat =
        (v.toNat / 2 ^ 0) % 2 ^ (7 - 0 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_lo]
  norm_num

private theorem byteOf_lane_lo_extract_1 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_lo v) 1 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 15 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 15 8).toNat =
        (v.toNat / 2 ^ 8) % 2 ^ (15 - 8 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_lo]
  norm_num
  omega

private theorem byteOf_lane_lo_extract_2 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_lo v) 2 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 23 16 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 23 16).toNat =
        (v.toNat / 2 ^ 16) % 2 ^ (23 - 16 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_lo]
  norm_num
  omega

private theorem byteOf_lane_lo_extract_3 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_lo v) 3 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 31 24 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 31 24).toNat =
        (v.toNat / 2 ^ 24) % 2 ^ (31 - 24 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_lo]
  norm_num
  omega

private theorem byteOf_lane_hi_extract_0 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_hi v) 0 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 39 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 39 32).toNat =
        (v.toNat / 2 ^ 32) % 2 ^ (39 - 32 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_hi]
  norm_num

private theorem byteOf_lane_hi_extract_1 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_hi v) 1 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 47 40 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 47 40).toNat =
        (v.toNat / 2 ^ 40) % 2 ^ (47 - 40 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_hi]
  have h_div_lt : v.toNat / 4294967296 < 4294967296 := by
    have hv := v.isLt
    omega
  rw [Nat.mod_eq_of_lt h_div_lt]
  rw [Nat.div_div_eq_div_mul]
  norm_num

private theorem byteOf_lane_hi_extract_2 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_hi v) 2 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 55 48 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 55 48).toNat =
        (v.toNat / 2 ^ 48) % 2 ^ (55 - 48 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_hi]
  have h_div_lt : v.toNat / 4294967296 < 4294967296 := by
    have hv := v.isLt
    omega
  rw [Nat.mod_eq_of_lt h_div_lt]
  rw [Nat.div_div_eq_div_mul]
  norm_num

private theorem byteOf_lane_hi_extract_3 (v : BitVec 64) :
    ((byteOf (ZiskFv.Trusted.lane_hi v) 3 : FGL) : BitVec 8)
      = Sail.BitVec.extractLsb v 63 56 := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.fgl_byte_coe_toBV8_toNat (byteOf_val_lt_256 _ _)]
  rw [byteOf_val_eq]
  have hrhs :
      (Sail.BitVec.extractLsb v 63 56).toNat =
        (v.toNat / 2 ^ 56) % 2 ^ (63 - 56 + 1) := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    rw [Nat.shiftRight_eq_div_pow]
  rw [hrhs]
  simp only [ZiskFv.Trusted.lane_hi]
  have h_div_lt : v.toNat / 4294967296 < 4294967296 := by
    have hv := v.isLt
    omega
  rw [Nat.mod_eq_of_lt h_div_lt]
  rw [Nat.div_div_eq_div_mul]
  norm_num

/-- Structural Clean witness for LD's Main consumer + Mem provider memory
bus path.

This is the binder shape intended for the eventual canonical structural
unpacking step: one explicit object collects the selected Clean Main row,
the selected Clean Mem provider row, row-equality pins to the existing
validators, ROM/transpile address and rd-routing pins, and legacy adapter
matches. It deliberately contains no axiom and no universal promise. -/
structure LdCleanWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (ld_input : PureSpec.LdInput) where
  r_mem : ℕ
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  memRow : ZiskFv.AirsClean.Mem.MemRow FGL
  main_row : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  mem_row : memRow = ZiskFv.AirsClean.Mem.rowAt mem r_mem
  main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core
  store_pc : mainRow.core.store_pc = 0
  main_b_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.bMemMessage mainRow) (-1) 2)
  main_c_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 1)
  mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage memRow) 1 2)
  addr1 :
    mainRow.rom.addr1.toNat =
      ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat
  addr2_zero_iff :
    Transpiler.wrap_to_regidx mainRow.rom.addr2 = 0 ↔ ld_input.rd = 0
  addr2_idx :
    ld_input.rd.toNat = (Transpiler.wrap_to_regidx mainRow.rom.addr2).val
  mem_sel : mem.sel r_mem = 1
  mem_legacy_addr : mem.addr r_mem = bus.e1.ptr
  mem_wr : mem.wr r_mem = 0

/-- Generic structural Clean witness for load-shaped Main consumer + Mem
provider paths.

This is the same unpacked memory witness shape as `LdCleanWitness`, but
parameterized by the Sail load address/register fields so sub-doubleword
loads can share it without pretending their PIL interaction is a legacy
architectural row. -/
structure LoadCleanWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5) where
  r_mem : ℕ
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  memRow : ZiskFv.AirsClean.Mem.MemRow FGL
  main_row : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  mem_row : memRow = ZiskFv.AirsClean.Mem.rowAt mem r_mem
  main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core
  store_pc : mainRow.core.store_pc = 0
  main_b_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.bMemMessage mainRow) (-1) 2)
  main_c_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 1)
  mem_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage memRow) 1 2)
  addr1 :
    mainRow.rom.addr1.toNat =
      r1_val.toNat + (BitVec.signExtend 64 imm).toNat
  addr2_zero_iff :
    Transpiler.wrap_to_regidx mainRow.rom.addr2 = 0 ↔ rd = 0
  addr2_idx :
    rd.toNat = (Transpiler.wrap_to_regidx mainRow.rom.addr2).val
  mem_sel : mem.sel r_mem = 1
  mem_legacy_addr : mem.addr r_mem = bus.e1.ptr
  mem_wr : mem.wr r_mem = 0

/-- Clean-backed LD-shaped discharge.

This packages the two pieces needed to replace the old LD path:

* Main-side load/rd-write emission facts, derived from a concrete Clean
  Main row and legacy `matches_memory_entry` adapters.
* Sail-memory byte facts, derived from an explicit Clean Mem provider row
  via `mem_load_correct_of_provider_row`, avoiding
  `lookup_consumer_matches_provider_load`.

The structural pins are deliberately explicit. In the final T4 migration
they must come from the memory-family witness, balance proof, row equality,
and ROM/transpile facts, not from new canonical promise hypotheses. -/
theorem ld_discharge_full_clean_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (r_main r_mem : ℕ)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (memRow : ZiskFv.AirsClean.Mem.MemRow FGL)
    (e1 e2 : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1_val : BitVec 64) (imm : BitVec 12) (rd : BitVec 5)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      memRow = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e1
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage mainRow) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e2
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 1))
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e1
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage memRow) 1 2))
    (h_addr1 :
      mainRow.rom.addr1.toNat =
        r1_val.toNat + (BitVec.signExtend 64 imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx mainRow.rom.addr2 = 0 ↔ rd = 0)
    (h_addr2_idx :
      rd.toNat = (Transpiler.wrap_to_regidx mainRow.rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_legacy_addr : mem.addr r_mem = e1.ptr)
    (h_mem_wr : mem.wr r_mem = 0) :
    ((main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e1
      ∧ e1.as = 2
      ∧ e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e2)
    ∧ e1.ptr.toNat = r1_val.toNat + (BitVec.signExtend 64 imm).toNat
    ∧ (Transpiler.wrap_to_regidx e2.ptr = 0 ↔ rd = 0)
    ∧ rd.toNat = (Transpiler.wrap_to_regidx e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main)
    ∧ (state.mem[e1.ptr.toNat]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 0)
      ∧ state.mem[e1.ptr.toNat + 1]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 1)
      ∧ state.mem[e1.ptr.toNat + 2]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 2)
      ∧ state.mem[e1.ptr.toNat + 3]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 3)
      ∧ state.mem[e1.ptr.toNat + 4]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 4)
      ∧ state.mem[e1.ptr.toNat + 5]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 5)
      ∧ state.mem[e1.ptr.toNat + 6]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 6)
      ∧ state.mem[e1.ptr.toNat + 7]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt e1 7)) := by
  have h_main :=
    ZiskFv.AirsClean.Main.load_emission_bundle_of_message_matches_valid
      main r_main mainRow e1 e2 r1_val imm rd
      h_main_row h_main_spec h_store_pc h_main_b_match h_main_c_match
      h_addr1 h_addr2_zero_iff h_addr2_idx
  have h_provider :
      ZiskFv.Airs.MemoryBus.MemBridge.mem_row_matches_entry mem r_mem e1 :=
    ZiskFv.AirsClean.Mem.mem_row_matches_entry_of_message_match_valid
      mem r_mem memRow e1 h_mem_row h_mem_sel h_mem_legacy_addr h_mem_match
  have h_mem :=
    ZiskFv.ZiskCircuit.MemModel.mem_load_correct_of_provider_row
      mem r_mem e1 state h_provider h_mem_wr
  obtain ⟨hb0, hb1, h_as, h_mult, hc0, hc1, h_ptr, h_rd0, h_rdidx,
    h_copy0, h_copy1⟩ := h_main
  exact ⟨⟨⟨hb0, hb1, h_as, h_mult⟩, ⟨hc0, hc1⟩, h_ptr, h_rd0,
    h_rdidx, h_copy0, h_copy1⟩, h_mem⟩

/-- Bundle-shaped form of `ld_discharge_full_clean_provider`. -/
theorem ld_discharge_full_clean_provider_of_witness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (w : LdCleanWitness main mem r_main bus ld_input) :
    ((main.b_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo bus.e1
      ∧ main.b_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi bus.e1
      ∧ bus.e1.as = 2
      ∧ bus.e1.multiplicity = -1)
    ∧ (main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo bus.e2
       ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi bus.e2)
    ∧ bus.e1.ptr.toNat =
        ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat
    ∧ (Transpiler.wrap_to_regidx bus.e2.ptr = 0 ↔ ld_input.rd = 0)
    ∧ ld_input.rd.toNat = (Transpiler.wrap_to_regidx bus.e2.ptr).val
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main
    ∧ ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main)
    ∧ (state.mem[bus.e1.ptr.toNat]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 0)
      ∧ state.mem[bus.e1.ptr.toNat + 1]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 1)
      ∧ state.mem[bus.e1.ptr.toNat + 2]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 2)
      ∧ state.mem[bus.e1.ptr.toNat + 3]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 3)
      ∧ state.mem[bus.e1.ptr.toNat + 4]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 4)
      ∧ state.mem[bus.e1.ptr.toNat + 5]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 5)
      ∧ state.mem[bus.e1.ptr.toNat + 6]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 6)
      ∧ state.mem[bus.e1.ptr.toNat + 7]? = .some
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e1 7)) := by
  exact ld_discharge_full_clean_provider
    main mem r_main w.r_mem w.mainRow w.memRow bus.e1 bus.e2 state
    ld_input.r1_val ld_input.imm ld_input.rd
    w.main_row w.mem_row w.main_spec w.store_pc
    w.main_b_match w.main_c_match w.mem_match
    w.addr1 w.addr2_zero_iff w.addr2_idx
    w.mem_sel w.mem_legacy_addr w.mem_wr

/-! ## Store-side Clean adapters -/

/-- Structural Clean witness for SD's Main store-side memory-bus path.

The full-width store only needs the selected Clean Main c/store row: the
byte payload comes from Main's copyb row plus the transpiler register-read
bridge, and no MemAlign RMW provider is involved. -/
structure SdCleanWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (sd_input : PureSpec.SdInput) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  main_row : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core
  store_pc : mainRow.core.store_pc = 0
  main_c_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2)
  addr2 :
    mainRow.rom.addr2.toNat =
      (sd_input.r1_val + BitVec.signExtend 64 sd_input.imm).toNat

structure SbCleanWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sb_input : PureSpec.SbInput) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  main_row : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core
  store_pc : mainRow.core.store_pc = 0
  main_c_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2)
  addr2 :
    mainRow.rom.addr2.toNat =
      (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat
  m1 : state.mem[bus.e2.ptr.toNat + 1]? = some (byteAt bus.e2 1 : BitVec 8)
  m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (byteAt bus.e2 2 : BitVec 8)
  m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (byteAt bus.e2 3 : BitVec 8)
  m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8)
  m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8)
  m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8)
  m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)

structure ShCleanWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sh_input : PureSpec.ShInput) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  main_row : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core
  store_pc : mainRow.core.store_pc = 0
  main_c_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2)
  addr2 :
    mainRow.rom.addr2.toNat =
      (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat
  m2 : state.mem[bus.e2.ptr.toNat + 2]? = some (byteAt bus.e2 2 : BitVec 8)
  m3 : state.mem[bus.e2.ptr.toNat + 3]? = some (byteAt bus.e2 3 : BitVec 8)
  m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8)
  m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8)
  m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8)
  m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)

structure SwCleanWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sw_input : PureSpec.SwInput) where
  mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  main_row : mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main
  main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core
  store_pc : mainRow.core.store_pc = 0
  main_c_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
      (MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2)
  addr2 :
    mainRow.rom.addr2.toNat =
      (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat
  m4 : state.mem[bus.e2.ptr.toNat + 4]? = some (byteAt bus.e2 4 : BitVec 8)
  m5 : state.mem[bus.e2.ptr.toNat + 5]? = some (byteAt bus.e2 5 : BitVec 8)
  m6 : state.mem[bus.e2.ptr.toNat + 6]? = some (byteAt bus.e2 6 : BitVec 8)
  m7 : state.mem[bus.e2.ptr.toNat + 7]? = some (byteAt bus.e2 7 : BitVec 8)

/-- Clean-backed SD store discharge.

This is the store-side analogue of `ld_discharge_full_clean_provider` for
the Main c/store message. The Clean row and message match provide the
legacy lane and pointer facts; `Spec` provides the copyb constraints; the
transpile/read-xreg bridge pins `b` to `rs2`; the private byte lemmas above
turn the two 32-bit lanes into the byte equalities consumed by `equiv_SD`.

This theorem has no new axioms and does not use
`main_store_emission_bundle_sd`. -/
theorem sd_discharge_full_clean_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32)
    (r1_val r2_val : BitVec 64) (imm : BitVec 12)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e_st
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2))
    (h_addr2 :
      mainRow.rom.addr2.toNat =
        (r1_val + BitVec.signExtend 64 imm).toNat)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (_h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    e_st.ptr.toNat = (r1_val + BitVec.signExtend 64 imm).toNat
    ∧ (byteAt e_st 0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val
    ∧ (byteAt e_st 1 : BitVec 8) = BitVec.extractLsb 15 8 r2_val
    ∧ (byteAt e_st 2 : BitVec 8) = BitVec.extractLsb 23 16 r2_val
    ∧ (byteAt e_st 3 : BitVec 8) = BitVec.extractLsb 31 24 r2_val
    ∧ (byteAt e_st 4 : BitVec 8) = BitVec.extractLsb 39 32 r2_val
    ∧ (byteAt e_st 5 : BitVec 8) = BitVec.extractLsb 47 40 r2_val
    ∧ (byteAt e_st 6 : BitVec 8) = BitVec.extractLsb 55 48 r2_val
    ∧ (byteAt e_st 7 : BitVec 8) = BitVec.extractLsb 63 56 r2_val := by
  obtain ⟨h_lanes, _h_as, _h_mult, h_ptr⟩ :=
    ZiskFv.AirsClean.Main.store_emission_lane_ptr_bundle_of_message_match_valid
      main r_main mainRow e_st r1_val imm
      h_main_row h_store_pc h_main_c_match h_addr2
  have h_copy0 : ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main := by
    have h0 :=
      ZiskFv.AirsClean.Main.internal_op1_copies_b0_of_spec_validOfRow
        mainRow.core h_main_spec
    rw [h_main_row] at h0
    simpa [ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt,
      ZiskFv.Airs.Main.internal_op1_copies_b0] using h0
  have h_copy1 : ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main := by
    have h1 :=
      ZiskFv.AirsClean.Main.internal_op1_copies_b1_of_spec_validOfRow
        mainRow.core h_main_spec
    rw [h_main_row] at h1
    simpa [ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt,
      ZiskFv.Airs.Main.internal_op1_copies_b1] using h1
  have h_tr := ZiskFv.Trusted.transpile_SD
    main r_main rs1 rs2 (0 : FGL)
    (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, h_a_lo_state, h_a_hi_state, h_b_lo_state, h_b_hi_state⟩ :=
    h_tr
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state rs2 r2_val h_read_r2] at h_b_lo_state h_b_hi_state
  simp only [ZiskFv.Airs.Main.internal_op1_copies_b0] at h_copy0
  simp only [ZiskFv.Airs.Main.internal_op1_copies_b1] at h_copy1
  rw [h_active, h_op_main] at h_copy0 h_copy1
  simp only [ZiskFv.Trusted.OP_COPYB] at h_copy0 h_copy1
  have h_bc0 : main.b_0 r_main = main.c_0 r_main := by
    linear_combination h_copy0
  have h_bc1 : main.b_1 r_main = main.c_1 r_main := by
    linear_combination h_copy1
  obtain ⟨h_c0, h_c1⟩ := h_lanes
  have h_c0' : main.c_0 r_main = e_st.value_0 := by
    simpa [ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_c0
  have h_c1' : main.c_1 r_main = e_st.value_1 := by
    simpa [ZiskFv.Airs.MemoryBus.memory_entry_hi] using h_c1
  have h_v0 : e_st.value_0 = ZiskFv.Trusted.lane_lo r2_val := by
    calc
      e_st.value_0 = main.c_0 r_main := h_c0'.symm
      _ = main.b_0 r_main := h_bc0.symm
      _ = ZiskFv.Trusted.lane_lo r2_val := h_b_lo_state
  have h_v1 : e_st.value_1 = ZiskFv.Trusted.lane_hi r2_val := by
    calc
      e_st.value_1 = main.c_1 r_main := h_c1'.symm
      _ = main.b_1 r_main := h_bc1.symm
      _ = ZiskFv.Trusted.lane_hi r2_val := h_b_hi_state
  have hb0 : (byteAt e_st 0 : BitVec 8) = BitVec.extractLsb 7 0 r2_val := by
    change ((byteOf e_st.value_0 0 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_0 r2_val
  have hb1 : (byteAt e_st 1 : BitVec 8) = BitVec.extractLsb 15 8 r2_val := by
    change ((byteOf e_st.value_0 1 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_1 r2_val
  have hb2 : (byteAt e_st 2 : BitVec 8) = BitVec.extractLsb 23 16 r2_val := by
    change ((byteOf e_st.value_0 2 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_2 r2_val
  have hb3 : (byteAt e_st 3 : BitVec 8) = BitVec.extractLsb 31 24 r2_val := by
    change ((byteOf e_st.value_0 3 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_3 r2_val
  have hb4 : (byteAt e_st 4 : BitVec 8) = BitVec.extractLsb 39 32 r2_val := by
    change ((byteOf e_st.value_1 (4 - 4) : FGL) : BitVec 8) = _
    rw [h_v1]
    exact byteOf_lane_hi_extract_0 r2_val
  have hb5 : (byteAt e_st 5 : BitVec 8) = BitVec.extractLsb 47 40 r2_val := by
    change ((byteOf e_st.value_1 (5 - 4) : FGL) : BitVec 8) = _
    rw [h_v1]
    exact byteOf_lane_hi_extract_1 r2_val
  have hb6 : (byteAt e_st 6 : BitVec 8) = BitVec.extractLsb 55 48 r2_val := by
    change ((byteOf e_st.value_1 (6 - 4) : FGL) : BitVec 8) = _
    rw [h_v1]
    exact byteOf_lane_hi_extract_2 r2_val
  have hb7 : (byteAt e_st 7 : BitVec 8) = BitVec.extractLsb 63 56 r2_val := by
    change ((byteOf e_st.value_1 (7 - 4) : FGL) : BitVec 8) = _
    rw [h_v1]
    exact byteOf_lane_hi_extract_3 r2_val
  exact ⟨h_ptr, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩

/-- Clean-backed SB store discharge, with the remaining high-byte RMW
preservation facts kept explicit.

The pointer and low stored byte are derived from the Clean Main c/store
message, `Spec`, and `transpile_SB`. The seven high-byte no-op facts are
still the MemAlign RMW obligation; this theorem intentionally exposes them
instead of hiding them behind `main_store_emission_bundle_subword`. -/
theorem sb_discharge_full_clean_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32)
    (sb_input : PureSpec.SbInput)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e_st
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2))
    (h_addr2 :
      mainRow.rom.addr2.toNat =
        (sb_input.r1_val + BitVec.signExtend 64 sb_input.imm).toNat)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (_h_ind_width : main.ind_width r_main = 1)
    (_h_read_r1 : read_xreg rs1 state = EStateM.Result.ok sb_input.r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok sb_input.r2_val state)
    (h_m1 : state.mem[e_st.ptr.toNat + 1]? = some (byteAt e_st 1 : BitVec 8))
    (h_m2 : state.mem[e_st.ptr.toNat + 2]? = some (byteAt e_st 2 : BitVec 8))
    (h_m3 : state.mem[e_st.ptr.toNat + 3]? = some (byteAt e_st 3 : BitVec 8))
    (h_m4 : state.mem[e_st.ptr.toNat + 4]? = some (byteAt e_st 4 : BitVec 8))
    (h_m5 : state.mem[e_st.ptr.toNat + 5]? = some (byteAt e_st 5 : BitVec 8))
    (h_m6 : state.mem[e_st.ptr.toNat + 6]? = some (byteAt e_st 6 : BitVec 8))
    (h_m7 : state.mem[e_st.ptr.toNat + 7]? = some (byteAt e_st 7 : BitVec 8)) :
    (((((((state.mem.insert e_st.ptr.toNat (byteAt e_st 0 : BitVec 8)
        ).insert (e_st.ptr.toNat + 1) (byteAt e_st 1 : BitVec 8)
        ).insert (e_st.ptr.toNat + 2) (byteAt e_st 2 : BitVec 8)
        ).insert (e_st.ptr.toNat + 3) (byteAt e_st 3 : BitVec 8)
        ).insert (e_st.ptr.toNat + 4) (byteAt e_st 4 : BitVec 8)
        ).insert (e_st.ptr.toNat + 5) (byteAt e_st 5 : BitVec 8)
        ).insert (e_st.ptr.toNat + 6) (byteAt e_st 6 : BitVec 8)
        ).insert (e_st.ptr.toNat + 7) (byteAt e_st 7 : BitVec 8)
      = state.mem.insert
          (PureSpec.execute_STOREB_pure sb_input).data0.1
          (PureSpec.execute_STOREB_pure sb_input).data0.2 := by
  obtain ⟨h_lanes, _h_as, _h_mult, h_ptr⟩ :=
    ZiskFv.AirsClean.Main.store_emission_lane_ptr_bundle_of_message_match_valid
      main r_main mainRow e_st sb_input.r1_val sb_input.imm
      h_main_row h_store_pc h_main_c_match h_addr2
  have h_copy0 : ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main := by
    have h0 :=
      ZiskFv.AirsClean.Main.internal_op1_copies_b0_of_spec_validOfRow
        mainRow.core h_main_spec
    rw [h_main_row] at h0
    simpa [ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt,
      ZiskFv.Airs.Main.internal_op1_copies_b0] using h0
  have h_tr := ZiskFv.Trusted.transpile_SB
    main r_main rs1 rs2 (0 : FGL)
    (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, _, _, h_b_lo_state, _⟩ := h_tr
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state rs2 sb_input.r2_val h_read_r2] at h_b_lo_state
  simp only [ZiskFv.Airs.Main.internal_op1_copies_b0] at h_copy0
  rw [h_active, h_op_main] at h_copy0
  simp only [ZiskFv.Trusted.OP_COPYB] at h_copy0
  have h_bc0 : main.b_0 r_main = main.c_0 r_main := by
    linear_combination h_copy0
  obtain ⟨h_c0, _h_c1⟩ := h_lanes
  have h_c0' : main.c_0 r_main = e_st.value_0 := by
    simpa [ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_c0
  have h_v0 : e_st.value_0 = ZiskFv.Trusted.lane_lo sb_input.r2_val := by
    calc
      e_st.value_0 = main.c_0 r_main := h_c0'.symm
      _ = main.b_0 r_main := h_bc0.symm
      _ = ZiskFv.Trusted.lane_lo sb_input.r2_val := h_b_lo_state
  have h_b0 : (byteAt e_st 0 : BitVec 8) =
      BitVec.extractLsb 7 0 sb_input.r2_val := by
    change ((byteOf e_st.value_0 0 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_0 sb_input.r2_val
  simp only [PureSpec.execute_STOREB_pure]
  rw [h_ptr]
  conv_lhs =>
    rw [show (byteAt e_st 0 : BitVec 8) =
      BitVec.extractLsb 7 0 sb_input.r2_val from h_b0]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  set_option synthInstance.maxHeartbeats 400000 in grind

/-- Clean-backed SH store discharge, with the remaining high-byte RMW
preservation facts kept explicit. -/
theorem sh_discharge_full_clean_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32)
    (sh_input : PureSpec.ShInput)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e_st
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2))
    (h_addr2 :
      mainRow.rom.addr2.toNat =
        (sh_input.r1_val + BitVec.signExtend 64 sh_input.imm).toNat)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (_h_ind_width : main.ind_width r_main = 2)
    (_h_read_r1 : read_xreg rs1 state = EStateM.Result.ok sh_input.r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok sh_input.r2_val state)
    (h_m2 : state.mem[e_st.ptr.toNat + 2]? = some (byteAt e_st 2 : BitVec 8))
    (h_m3 : state.mem[e_st.ptr.toNat + 3]? = some (byteAt e_st 3 : BitVec 8))
    (h_m4 : state.mem[e_st.ptr.toNat + 4]? = some (byteAt e_st 4 : BitVec 8))
    (h_m5 : state.mem[e_st.ptr.toNat + 5]? = some (byteAt e_st 5 : BitVec 8))
    (h_m6 : state.mem[e_st.ptr.toNat + 6]? = some (byteAt e_st 6 : BitVec 8))
    (h_m7 : state.mem[e_st.ptr.toNat + 7]? = some (byteAt e_st 7 : BitVec 8)) :
    (((((((state.mem.insert e_st.ptr.toNat (byteAt e_st 0 : BitVec 8)
        ).insert (e_st.ptr.toNat + 1) (byteAt e_st 1 : BitVec 8)
        ).insert (e_st.ptr.toNat + 2) (byteAt e_st 2 : BitVec 8)
        ).insert (e_st.ptr.toNat + 3) (byteAt e_st 3 : BitVec 8)
        ).insert (e_st.ptr.toNat + 4) (byteAt e_st 4 : BitVec 8)
        ).insert (e_st.ptr.toNat + 5) (byteAt e_st 5 : BitVec 8)
        ).insert (e_st.ptr.toNat + 6) (byteAt e_st 6 : BitVec 8)
        ).insert (e_st.ptr.toNat + 7) (byteAt e_st 7 : BitVec 8)
      = (state.mem.insert
            (PureSpec.execute_STOREH_pure sh_input).data0.1
            (PureSpec.execute_STOREH_pure sh_input).data0.2
          ).insert
            (PureSpec.execute_STOREH_pure sh_input).data1.1
            (PureSpec.execute_STOREH_pure sh_input).data1.2 := by
  obtain ⟨h_lanes, _h_as, _h_mult, h_ptr⟩ :=
    ZiskFv.AirsClean.Main.store_emission_lane_ptr_bundle_of_message_match_valid
      main r_main mainRow e_st sh_input.r1_val sh_input.imm
      h_main_row h_store_pc h_main_c_match h_addr2
  have h_copy0 : ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main := by
    have h0 :=
      ZiskFv.AirsClean.Main.internal_op1_copies_b0_of_spec_validOfRow
        mainRow.core h_main_spec
    rw [h_main_row] at h0
    simpa [ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt,
      ZiskFv.Airs.Main.internal_op1_copies_b0] using h0
  have h_tr := ZiskFv.Trusted.transpile_SH
    main r_main rs1 rs2 (0 : FGL)
    (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, _, _, h_b_lo_state, _⟩ := h_tr
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state rs2 sh_input.r2_val h_read_r2] at h_b_lo_state
  simp only [ZiskFv.Airs.Main.internal_op1_copies_b0] at h_copy0
  rw [h_active, h_op_main] at h_copy0
  simp only [ZiskFv.Trusted.OP_COPYB] at h_copy0
  have h_bc0 : main.b_0 r_main = main.c_0 r_main := by
    linear_combination h_copy0
  obtain ⟨h_c0, _h_c1⟩ := h_lanes
  have h_c0' : main.c_0 r_main = e_st.value_0 := by
    simpa [ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_c0
  have h_v0 : e_st.value_0 = ZiskFv.Trusted.lane_lo sh_input.r2_val := by
    calc
      e_st.value_0 = main.c_0 r_main := h_c0'.symm
      _ = main.b_0 r_main := h_bc0.symm
      _ = ZiskFv.Trusted.lane_lo sh_input.r2_val := h_b_lo_state
  have h_b0 : (byteAt e_st 0 : BitVec 8) =
      BitVec.extractLsb 7 0 sh_input.r2_val := by
    change ((byteOf e_st.value_0 0 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_0 sh_input.r2_val
  have h_b1 : (byteAt e_st 1 : BitVec 8) =
      BitVec.extractLsb 15 8 sh_input.r2_val := by
    change ((byteOf e_st.value_0 1 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_1 sh_input.r2_val
  simp only [PureSpec.execute_STOREH_pure]
  rw [h_ptr]
  conv_lhs =>
    rw [show (byteAt e_st 0 : BitVec 8) =
      BitVec.extractLsb 7 0 sh_input.r2_val from h_b0]
  conv_lhs =>
    rw [show (byteAt e_st 1 : BitVec 8) =
      BitVec.extractLsb 15 8 sh_input.r2_val from h_b1]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  set_option synthInstance.maxHeartbeats 400000 in grind

/-- Clean-backed SW store discharge, with the remaining high-byte RMW
preservation facts kept explicit. -/
theorem sw_discharge_full_clean_provider
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (e_st : MemoryBusEntry FGL)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32)
    (sw_input : PureSpec.SwInput)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry e_st
        (MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 2))
    (h_addr2 :
      mainRow.rom.addr2.toNat =
        (sw_input.r1_val + BitVec.signExtend 64 sw_input.imm).toNat)
    (h_active : main.is_external_op r_main = 0)
    (h_op_main : main.op r_main = ZiskFv.Trusted.OP_COPYB)
    (_h_ind_width : main.ind_width r_main = 4)
    (_h_read_r1 : read_xreg rs1 state = EStateM.Result.ok sw_input.r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok sw_input.r2_val state)
    (h_m4 : state.mem[e_st.ptr.toNat + 4]? = some (byteAt e_st 4 : BitVec 8))
    (h_m5 : state.mem[e_st.ptr.toNat + 5]? = some (byteAt e_st 5 : BitVec 8))
    (h_m6 : state.mem[e_st.ptr.toNat + 6]? = some (byteAt e_st 6 : BitVec 8))
    (h_m7 : state.mem[e_st.ptr.toNat + 7]? = some (byteAt e_st 7 : BitVec 8)) :
    (((((((state.mem.insert e_st.ptr.toNat (byteAt e_st 0 : BitVec 8)
        ).insert (e_st.ptr.toNat + 1) (byteAt e_st 1 : BitVec 8)
        ).insert (e_st.ptr.toNat + 2) (byteAt e_st 2 : BitVec 8)
        ).insert (e_st.ptr.toNat + 3) (byteAt e_st 3 : BitVec 8)
        ).insert (e_st.ptr.toNat + 4) (byteAt e_st 4 : BitVec 8)
        ).insert (e_st.ptr.toNat + 5) (byteAt e_st 5 : BitVec 8)
        ).insert (e_st.ptr.toNat + 6) (byteAt e_st 6 : BitVec 8)
        ).insert (e_st.ptr.toNat + 7) (byteAt e_st 7 : BitVec 8)
      = (((state.mem.insert
            (PureSpec.execute_STOREW_pure sw_input).data0.1
            (PureSpec.execute_STOREW_pure sw_input).data0.2
          ).insert
            (PureSpec.execute_STOREW_pure sw_input).data1.1
            (PureSpec.execute_STOREW_pure sw_input).data1.2
          ).insert
            (PureSpec.execute_STOREW_pure sw_input).data2.1
            (PureSpec.execute_STOREW_pure sw_input).data2.2
          ).insert
            (PureSpec.execute_STOREW_pure sw_input).data3.1
            (PureSpec.execute_STOREW_pure sw_input).data3.2 := by
  obtain ⟨h_lanes, _h_as, _h_mult, h_ptr⟩ :=
    ZiskFv.AirsClean.Main.store_emission_lane_ptr_bundle_of_message_match_valid
      main r_main mainRow e_st sw_input.r1_val sw_input.imm
      h_main_row h_store_pc h_main_c_match h_addr2
  have h_copy0 : ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main := by
    have h0 :=
      ZiskFv.AirsClean.Main.internal_op1_copies_b0_of_spec_validOfRow
        mainRow.core h_main_spec
    rw [h_main_row] at h0
    simpa [ZiskFv.AirsClean.Main.validOfRow, ZiskFv.AirsClean.Main.rowAt,
      ZiskFv.Airs.Main.internal_op1_copies_b0] using h0
  have h_tr := ZiskFv.Trusted.transpile_SW
    main r_main rs1 rs2 (0 : FGL)
    (ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state)
    h_active h_op_main
  obtain ⟨_, _, _, _, _, _, _, h_b_lo_state, _⟩ := h_tr
  rw [ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64_xreg_eq_of_read_xreg
        state rs2 sw_input.r2_val h_read_r2] at h_b_lo_state
  simp only [ZiskFv.Airs.Main.internal_op1_copies_b0] at h_copy0
  rw [h_active, h_op_main] at h_copy0
  simp only [ZiskFv.Trusted.OP_COPYB] at h_copy0
  have h_bc0 : main.b_0 r_main = main.c_0 r_main := by
    linear_combination h_copy0
  obtain ⟨h_c0, _h_c1⟩ := h_lanes
  have h_c0' : main.c_0 r_main = e_st.value_0 := by
    simpa [ZiskFv.Airs.MemoryBus.memory_entry_lo] using h_c0
  have h_v0 : e_st.value_0 = ZiskFv.Trusted.lane_lo sw_input.r2_val := by
    calc
      e_st.value_0 = main.c_0 r_main := h_c0'.symm
      _ = main.b_0 r_main := h_bc0.symm
      _ = ZiskFv.Trusted.lane_lo sw_input.r2_val := h_b_lo_state
  have h_b0 : (byteAt e_st 0 : BitVec 8) =
      BitVec.extractLsb 7 0 sw_input.r2_val := by
    change ((byteOf e_st.value_0 0 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_0 sw_input.r2_val
  have h_b1 : (byteAt e_st 1 : BitVec 8) =
      BitVec.extractLsb 15 8 sw_input.r2_val := by
    change ((byteOf e_st.value_0 1 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_1 sw_input.r2_val
  have h_b2 : (byteAt e_st 2 : BitVec 8) =
      BitVec.extractLsb 23 16 sw_input.r2_val := by
    change ((byteOf e_st.value_0 2 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_2 sw_input.r2_val
  have h_b3 : (byteAt e_st 3 : BitVec 8) =
      BitVec.extractLsb 31 24 sw_input.r2_val := by
    change ((byteOf e_st.value_0 3 : FGL) : BitVec 8) = _
    rw [h_v0]
    exact byteOf_lane_lo_extract_3 sw_input.r2_val
  simp only [PureSpec.execute_STOREW_pure]
  rw [h_ptr]
  conv_lhs =>
    rw [show (byteAt e_st 0 : BitVec 8) =
      BitVec.extractLsb 7 0 sw_input.r2_val from h_b0]
  conv_lhs =>
    rw [show (byteAt e_st 1 : BitVec 8) =
      BitVec.extractLsb 15 8 sw_input.r2_val from h_b1]
  conv_lhs =>
    rw [show (byteAt e_st 2 : BitVec 8) =
      BitVec.extractLsb 23 16 sw_input.r2_val from h_b2]
  conv_lhs =>
    rw [show (byteAt e_st 3 : BitVec 8) =
      BitVec.extractLsb 31 24 sw_input.r2_val from h_b3]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  set_option synthInstance.maxHeartbeats 400000 in grind

end ZiskFv.EquivCore.Bridge.MemClean
