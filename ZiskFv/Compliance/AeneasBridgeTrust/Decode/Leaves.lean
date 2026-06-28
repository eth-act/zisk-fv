/-
ZiskFv/Compliance/AeneasBridgeTrust/Decode/Leaves.lean  (eth-act/zisk-fv#162)

Leaf-decoder totality + the `toU32` bridge, on the REAL extracted decoder
(`trust/aeneas/ProductionM2.lean`). Kernel-sound (no native_decide / bv_decide).
-/
import ProductionM2
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Masks

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Completeness

namespace ZiskFv.Compliance.Decode

/-- Inject a raw 32-bit word into the extracted decoder's `Std.U32` input type. -/
def toU32 (raw : BitVec 32) : Std.U32 := ⟨raw⟩

@[simp] theorem toU32_bv (raw : BitVec 32) : (toU32 raw).bv = raw := rfl

/-! ## U32-level bridge lemmas (all `rfl`: the U32 ops reduce definitionally). -/

@[simp] theorem toU32_and127 (X : BitVec 32) : toU32 X &&& 127#u32 = toU32 (X &&& 127#32) := rfl
@[simp] theorem toU32_and7 (X : BitVec 32) : toU32 X &&& 7#u32 = toU32 (X &&& 7#32) := rfl
@[simp] theorem toU32_and63 (X : BitVec 32) : toU32 X &&& 63#u32 = toU32 (X &&& 63#32) := rfl
@[simp] theorem toU32_and15 (X : BitVec 32) : toU32 X &&& 15#u32 = toU32 (X &&& 15#32) := rfl

@[simp] theorem toU32_shr12 (X : BitVec 32) : toU32 X >>> 12#i32 = ok (toU32 (X >>> 12)) := rfl
@[simp] theorem toU32_shr25 (X : BitVec 32) : toU32 X >>> 25#i32 = ok (toU32 (X >>> 25)) := rfl
@[simp] theorem toU32_shr26 (X : BitVec 32) : toU32 X >>> 26#i32 = ok (toU32 (X >>> 26)) := rfl

/-- `decode_r` is total and pins the opcode: every word decodes (the constant
shifts always succeed) to a record carrying the passed opcode. -/
theorem decode_r_ok (inst : Std.U32) (op : RiscvOpcode) :
    ∃ d, decode_r inst op = ok d ∧ d.opcode = op := by
  refine ⟨_, rfl, rfl⟩

theorem add_accepts (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    aeneas_extract.extract_rv64im_opcode_supported
      (toU32 (Rv64imShapes.rawRType 0 rs2 rs1 0 rd 0x33)) = ok true := by
  simp only [aeneas_extract.extract_rv64im_opcode_supported,
    aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
    toU32_and127, toU32_and7, toU32_shr12, toU32_shr25,
    rawRType_opcode _ _ _ _ _ _ (show (0x33:Nat) < 128 by norm_num),
    rawRType_funct3 0 rs2 rs1 0 rd 0x33 (by norm_num) hrd (by norm_num),
    rawRType_funct7 0 rs2 rs1 0 rd 0x33 (by norm_num) hrs2 hrs1 (by norm_num) hrd (by norm_num)]
  rfl

end ZiskFv.Compliance.Decode
