import ProductionM2
import ProductionM2.RomFlags
import ZiskFv.AirsClean.Main.Circuit

/-!
# Actual Rust instruction flags and the ROM flag word

`ProductionM2.RomFlags` is a separate extraction rooted at the existing
`ZiskInst::get_flags` function in zisk@9ca88b5, not a replica Rust wrapper.
The original `ProductionM2` module and its extraction roots are unchanged.
Both extracted instruction types use that exact source file and the
`aeneas_extract` profile; `fromProduction` explicitly preserves every field.
No equivalence with the independently pinned PIL source is assumed here.

The proof relates the actual fallible scalar program to the arithmetic
`Main.packFlags` word. The intermediate bit fold is proved by disjoint-bit
addition, without native evaluation or a trusted bitvector solver. This does
not yet claim correspondence of the separate `compute_trace_rom` serializer.
-/

namespace ZiskFv.Compliance.RomProducerFlags

open Aeneas Aeneas.Std Result
open Goldilocks
open ZiskFv.AirsClean.Main (RomFlagBits)

private def operationType
    (op : zisk_core.zisk_inst.ZiskOperationType) : zisk_rom_flags.zisk_inst.ZiskOperationType :=
  match op with
  | .None => .None
  | .Internal => .Internal
  | .Arith => .Arith
  | .Binary => .Binary
  | .BinaryE => .BinaryE
  | .Keccak => .Keccak
  | .Sha256 => .Sha256
  | .Poseidon2 => .Poseidon2
  | .Blake2 => .Blake2
  | .PubOut => .PubOut
  | .ArithEq => .ArithEq
  | .ArithEq384 => .ArithEq384
  | .BigInt => .BigInt
  | .Dma => .Dma
  | .FcallParam => .FcallParam
  | .Fcall => .Fcall
  | .FcallGet => .FcallGet
  | .Profile => .Profile

/-- Explicit transport between two extractions of the same pinned Rust type.
In particular, all fifteen flag inputs are copied, not supplied as promises. -/
def fromProduction (i : zisk_core.zisk_inst.ZiskInst) : zisk_rom_flags.zisk_inst.ZiskInst where
  paddr := i.paddr
  store_pc := i.store_pc
  store_use_sp := i.store_use_sp
  store := i.store
  store_offset := i.store_offset
  set_pc := i.set_pc
  is_precompiled := i.is_precompiled
  ind_width := i.ind_width
  «end» := i.end
  a_src := i.a_src
  a_use_sp_imm1 := i.a_use_sp_imm1
  a_offset_imm0 := i.a_offset_imm0
  b_src := i.b_src
  b_use_sp_imm1 := i.b_use_sp_imm1
  b_offset_imm0 := i.b_offset_imm0
  jmp_offset1 := i.jmp_offset1
  jmp_offset2 := i.jmp_offset2
  is_external_op := i.is_external_op
  op := i.op
  op_type := operationType i.op_type
  m32 := i.m32
  input_size := i.input_size
  sorted_pc_list_index := i.sorted_pc_list_index

/-- The flag inputs dictated by the Rust source constants, independently of
its OR/shift program. The unused source variants simply produce false bits. -/
def sourceBits (i : zisk_rom_flags.zisk_inst.ZiskInst) : RomFlagBits where
  a_src_imm := decide (i.a_src = 2#u64)
  a_src_mem := decide (i.a_src = 1#u64)
  is_precompiled := i.is_precompiled
  b_src_imm := decide (i.b_src = 2#u64)
  b_src_mem := decide (i.b_src = 1#u64)
  is_external_op := i.is_external_op
  store_pc := i.store_pc
  store_mem := decide (i.store = 1#u64)
  store_ind := decide (i.store = 2#u64)
  set_pc := i.set_pc
  m32 := i.m32
  b_src_ind := decide (i.b_src = 5#u64)
  a_src_reg := decide (i.a_src = 6#u64)
  b_src_reg := decide (i.b_src = 6#u64)
  store_reg := decide (i.store = 3#u64)

def flagBits (i : zisk_core.zisk_inst.ZiskInst) : RomFlagBits := sourceBits (fromProduction i)

private def bitList (b : RomFlagBits) : List Bool :=
  [b.a_src_imm, b.a_src_mem, b.is_precompiled, b.b_src_imm, b.b_src_mem,
   b.is_external_op, b.store_pc, b.store_mem, b.store_ind, b.set_pc, b.m32,
   b.b_src_ind, b.a_src_reg, b.b_src_reg, b.store_reg]

private def shiftedBool (b : Bool) (index : Nat) : Std.U64 :=
  ⟨(UScalar.cast_fromBool .U64 b).bv <<< index⟩

private def wordFrom : List Bool → Nat → Std.U64 → Std.U64
  | [], _, acc => acc
  | bit :: bits, index, acc => wordFrom bits (index + 1) (acc ||| shiftedBool bit index)

private def natFrom : List Bool → Nat → Nat → Nat
  | [], _, acc => acc
  | bit :: bits, index, acc => natFrom bits (index + 1) (acc + 2 ^ index * bit.toNat)

/-- A source-independent arithmetic word for the sixteen flag positions. -/
def flagNat (bits : RomFlagBits) : Nat := natFrom (bitList bits) 1 1

private theorem shiftedBool_val (b : Bool) (index : Nat) (h_index : index < 64) :
    (shiftedBool b index).val = 2 ^ index * b.toNat := by
  change ((UScalar.cast_fromBool .U64 b).bv <<< index).toNat = _
  rw [BitVec.toNat_shiftLeft]
  change ((UScalar.cast_fromBool .U64 b).val <<< index) % 2 ^ 64 = _
  rw [UScalar.cast_fromBool_val_eq, Nat.shiftLeft_eq]
  have h_bound : b.toNat * 2 ^ index < 2 ^ 64 := by
    cases b
    · simp
    · simpa using (Nat.pow_lt_pow_of_lt (by decide : 1 < (2 : Nat)) h_index)
  rw [Nat.mod_eq_of_lt h_bound, Nat.mul_comm]

private theorem append_bit (acc index : Nat) (h_acc : acc < 2 ^ index) (b : Bool) :
    acc ||| (2 ^ index * b.toNat) = acc + 2 ^ index * b.toNat := by
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt h_acc, Nat.add_comm]

private theorem wordFrom_val (bits : List Bool) (index : Nat) (acc : Std.U64)
    (h_acc : acc.val < 2 ^ index) (h_width : index + bits.length ≤ 64) :
    (wordFrom bits index acc).val = natFrom bits index acc.val := by
  induction bits generalizing index acc with
  | nil => rfl
  | cons bit bits ih =>
    have h_index : index < 64 := by simp only [List.length_cons] at h_width; omega
    have h_next : (acc ||| shiftedBool bit index).val < 2 ^ (index + 1) := by
      rw [UScalar.val_or, shiftedBool_val bit index h_index, append_bit _ _ h_acc]
      cases bit <;> simp only [Bool.toNat, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;>
        rw [Nat.pow_succ] <;> omega
    simp only [wordFrom, natFrom]
    rw [ih (index + 1) _ h_next (by simp only [List.length_cons] at h_width; omega)]
    rw [UScalar.val_or, shiftedBool_val bit index h_index, append_bit _ _ h_acc]

private theorem flagNat_cast (bits : RomFlagBits) :
    (flagNat bits : FGL) = ZiskFv.AirsClean.Main.packFlags bits := by
  have bool_cast (b : Bool) : ((b.toNat : Nat) : FGL) = ZiskFv.AirsClean.boolF b := by
    cases b <;> rfl
  simp only [flagNat, bitList, natFrom, ZiskFv.AirsClean.Main.packFlags,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, bool_cast]
  norm_num

/-- The actual source function is total and returns the ordered bit fold.
Every fallible shift uses a literal position below 64. -/
private theorem get_flags_word (i : zisk_rom_flags.zisk_inst.ZiskInst) :
    i.get_flags = ok (wordFrom (bitList (sourceBits i)) 1 1#u64) := by
  simp [zisk_rom_flags.zisk_inst.ZiskInst.get_flags,
    zisk_rom_flags.zisk_inst.SRC_IMM, zisk_rom_flags.zisk_inst.SRC_MEM,
    zisk_rom_flags.zisk_inst.SRC_IND, zisk_rom_flags.zisk_inst.SRC_REG,
    zisk_rom_flags.zisk_inst.STORE_MEM, zisk_rom_flags.zisk_inst.STORE_IND,
    zisk_rom_flags.zisk_inst.STORE_REG, sourceBits, bitList, wordFrom, shiftedBool,
    HShiftLeft.hShiftLeft, UScalar.shiftLeft_IScalar, UScalar.shiftLeft,
    IScalar.toNat, IScalar.val, UScalarTy.numBits, lift, Bind.bind, bind_ok]

/-- Genuine producer correspondence: the returned Rust `u64`, embedded in
Goldilocks, is exactly the existing Main ROM flag packing. This theorem uses
neither a replica serializer nor a new condition on the instruction. -/
theorem get_flags_eq_packFlags (i : zisk_core.zisk_inst.ZiskInst) :
    ∃ word : Std.U64,
      (fromProduction i).get_flags = ok word ∧
      (word.val : FGL) = ZiskFv.AirsClean.Main.packFlags (flagBits i) := by
  refine ⟨wordFrom (bitList (sourceBits (fromProduction i))) 1 1#u64,
    get_flags_word (fromProduction i), ?_⟩
  have h_val := wordFrom_val (bitList (sourceBits (fromProduction i))) 1 1#u64
    (by decide) (by simp [bitList])
  rw [h_val]
  exact flagNat_cast (flagBits i)

#print axioms get_flags_eq_packFlags

end ZiskFv.Compliance.RomProducerFlags
