/-
ZiskFv/Compliance/AeneasBridgeTrust/Decode/Classify.lean  (eth-act/zisk-fv#162)

Opcode-CLASSIFICATION layer for the real extracted RV64IM decoder
(`decode_32_core`, `trust/aeneas/ProductionM2.lean`).  Where `Decode/Leaves.lean`
proves *acceptance* (the supported-opcode check returns `ok true`), this layer
proves the strictly stronger *classification* fact: every raw word in a supported
decode shape decodes to a record whose `.opcode` is the SPECIFIC `RiscvOpcode`
that the RISC-V encoding assigns to that shape.  These per-family `*_classifies`
lemmas are the "opcode-classification theorem" that completes #162's bytes→opcode
chain (the leaf `decode_*_spec` lemmas pin the opcode; `bind_supported` discarded
it before the acceptance theorem — here we keep it).

Kernel-sound: NO `native_decide` / `bv_decide` / `sorry`.  These are pure
reductions of the extracted `decode_32_core`, exactly like the `*_accepts`
lemmas but keeping the opcode instead of collapsing it through `is_supported`.
-/
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open ZiskFv.Completeness ZiskFv.Completeness.Rv64imShapes

namespace ZiskFv.Compliance.Decode

/-- A leaf-decoder spec that pins `.opcode = op` yields the existential
classification witness (`m = ok d ∧ d.opcode = op`).  The classification
analogue of `bind_supported`. -/
theorem classify_of_decode {m : Result DecodedRv64im} {op : RiscvOpcode}
    (hm : m ⦃ d => d.opcode = op ⦄) : ∃ d, m = ok d ∧ d.opcode = op :=
  WP.spec_imp_exists hm

/-! ## Per-family opcode lookups (mirrored from `decode_32_core`, pinned by `rfl`). -/

/-- The `RiscvOpcode` the RV64IM encoding assigns to an R-type `(funct7, funct3,
opcode)` shape — mirrored from `decode_32_core`'s R-type arms. -/
def rtypeOpcode (funct7 funct3 opcode : Nat) : RiscvOpcode :=
  match opcode, funct7, funct3 with
  | 0x33, 0, 0 => .Add
  | 0x33, 32, 0 => .Sub
  | 0x33, 0, 1 => .Sll
  | 0x33, 0, 2 => .Slt
  | 0x33, 0, 3 => .Sltu
  | 0x33, 0, 4 => .Xor
  | 0x33, 0, 5 => .Srl
  | 0x33, 32, 5 => .Sra
  | 0x33, 0, 6 => .Or
  | 0x33, 0, 7 => .And
  | 0x3b, 0, 0 => .Addw
  | 0x3b, 32, 0 => .Subw
  | 0x3b, 0, 1 => .Sllw
  | 0x3b, 0, 5 => .Srlw
  | 0x3b, 32, 5 => .Sraw
  | 0x33, 1, 0 => .Mul
  | 0x33, 1, 1 => .Mulh
  | 0x33, 1, 2 => .Mulhsu
  | 0x33, 1, 3 => .Mulhu
  | 0x3b, 1, 0 => .Mulw
  | 0x33, 1, 4 => .Div
  | 0x33, 1, 5 => .Divu
  | 0x3b, 1, 4 => .Divw
  | 0x3b, 1, 5 => .Divuw
  | 0x33, 1, 6 => .Rem
  | 0x33, 1, 7 => .Remu
  | 0x3b, 1, 6 => .Remw
  | 0x3b, 1, 7 => .Remuw
  | _, _, _ => .Reserved

/-- I-type (incl. JALR, immediate ALU, ADDIW, loads) opcode by `(funct3, opcode)`. -/
def itypeOpcode (funct3 opcode : Nat) : RiscvOpcode :=
  match opcode, funct3 with
  | 0x67, 0 => .Jalr
  | 0x13, 0 => .Addi
  | 0x13, 2 => .Slti
  | 0x13, 3 => .Sltiu
  | 0x13, 4 => .Xori
  | 0x13, 6 => .Ori
  | 0x13, 7 => .Andi
  | 0x1b, 0 => .Addiw
  | 0x03, 0 => .Lb
  | 0x03, 1 => .Lh
  | 0x03, 2 => .Lw
  | 0x03, 3 => .Ld
  | 0x03, 4 => .Lbu
  | 0x03, 5 => .Lhu
  | 0x03, 6 => .Lwu
  | _, _ => .Reserved

/-- S-type (stores) opcode by `funct3`. -/
def stypeOpcode (funct3 : Nat) : RiscvOpcode :=
  match funct3 with
  | 0 => .Sb | 1 => .Sh | 2 => .Sw | 3 => .Sd | _ => .Reserved

/-- B-type (branches) opcode by `funct3`. -/
def btypeOpcode (funct3 : Nat) : RiscvOpcode :=
  match funct3 with
  | 0 => .Beq | 1 => .Bne | 4 => .Blt | 5 => .Bge | 6 => .Bltu | 7 => .Bgeu | _ => .Reserved

/-- U-type opcode by `opcode`. -/
def utypeOpcode (opcode : Nat) : RiscvOpcode :=
  match opcode with
  | 0x37 => .Lui | 0x17 => .Auipc | _ => .Reserved

/-- Shift-immediate (64-bit, opcode 0x13) opcode by `(funct3, upper)`. -/
def shift64Opcode (funct3 upper : Nat) : RiscvOpcode :=
  match funct3, upper with
  | 1, 0 => .Slli | 5, 0 => .Srli | 5, 0x400 => .Srai | _, _ => .Reserved

/-- Shift-immediate (32-bit word, opcode 0x1b) opcode by `(funct3, upper)`. -/
def shift32Opcode (funct3 upper : Nat) : RiscvOpcode :=
  match funct3, upper with
  | 1, 0 => .Slliw | 5, 0 => .Srliw | 5, 0x400 => .Sraiw | _, _ => .Reserved

/-! ## Per-family classification theorems. -/

set_option maxHeartbeats 1000000 in
/-- **R-type classification.** -/
theorem rtype_family_classifies (funct7 funct3 opcode rd rs1 rs2 : Nat)
    (hmem : (funct7, funct3, opcode) ∈ allRTypeOpcodeShapes)
    (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
    ∃ d, decode_32_core (toU32 (rawRType funct7 rs2 rs1 funct3 rd opcode)) = ok d ∧
         d.opcode = rtypeOpcode funct7 funct3 opcode := by
  fin_cases hmem <;>
    exact ⟨_, by
      simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
        toU32_and127, toU32_and7, toU32_shr12, toU32_shr25,
        rawRType_opcode, rawRType_funct3, rawRType_funct7]
      rfl, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **I-type classification** (JALR, immediate ALU, ADDIW, loads). -/
theorem itype_family_classifies (rd rs1 imm funct3 opcode : Nat)
    (hrd : rd < 32) (_hrs1 : rs1 < 32) (_himm : imm < 4096)
    (hmem : (funct3, opcode) ∈ [
      (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
      (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)]) :
    ∃ d, decode_32_core (toU32 (rawIType imm rs1 funct3 rd opcode)) = ok d ∧
         d.opcode = itypeOpcode funct3 opcode := by
  fin_cases hmem <;>
    (simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_ofNat, rawIType_opcode, rawIType_funct3]
     exact classify_of_decode (decode_i_false_spec _ _))

set_option maxHeartbeats 1000000 in
/-- **S-type classification** (stores). -/
theorem stype_family_classifies (rs1 rs2 imm funct3 : Nat)
    (_hrs1 : rs1 < 32) (_hrs2 : rs2 < 32) (_himm : imm < 4096)
    (hmem : funct3 ∈ [0, 1, 2, 3]) :
    ∃ d, decode_32_core (toU32 (rawSType imm rs2 rs1 funct3)) = ok d ∧
         d.opcode = stypeOpcode funct3 := by
  fin_cases hmem <;>
    (simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_ofNat, rawSType_opcode, rawSType_funct3]
     exact classify_of_decode (decode_s_spec _ _))

set_option maxHeartbeats 1000000 in
/-- **B-type classification** (branches). -/
theorem btype_family_classifies (rs1 rs2 imm funct3 : Nat)
    (_hrs1 : rs1 < 32) (_hrs2 : rs2 < 32) (_himm : imm < 8192)
    (hmem : funct3 ∈ [0, 1, 4, 5, 6, 7]) :
    ∃ d, decode_32_core (toU32 (rawBType imm rs2 rs1 funct3)) = ok d ∧
         d.opcode = btypeOpcode funct3 := by
  fin_cases hmem <;>
    (simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_ofNat, rawBType_opcode, rawBType_funct3]
     exact classify_of_decode (decode_b_spec _ _))

set_option maxHeartbeats 1000000 in
/-- **U-type classification** (LUI / AUIPC). -/
theorem utype_family_classifies (rd imm opcode : Nat)
    (_hrd : rd < 32) (hmem : opcode ∈ [0x37, 0x17]) :
    ∃ d, decode_32_core (toU32 (rawUType imm rd opcode)) = ok d ∧
         d.opcode = utypeOpcode opcode := by
  fin_cases hmem <;>
    exact ⟨_, by
      simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
        toU32_and127, rawUType_opcode]
      rfl, rfl⟩

/-- **J-type classification** (JAL). -/
theorem jtype_family_classifies (rd imm : Nat) :
    ∃ d, decode_32_core (toU32 (rawJType imm rd)) = ok d ∧
         d.opcode = RiscvOpcode.Jal := by
  simp only [decode_32_core, lift, Bind.bind, bind_ok,
    toU32_and127, toU32_ofNat, rawJType_opcode]
  exact classify_of_decode (decode_j_spec _ _)

set_option maxHeartbeats 1000000 in
/-- **Shift-immediate (64-bit) classification** (SLLI / SRLI / SRAI). -/
theorem shift64_family_classifies (rd rs1 shamt funct3 upper : Nat)
    (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 64)
    (hfu : (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)]) :
    ∃ d, decode_32_core (toU32 (rawIType (upper ||| shamt) rs1 funct3 rd 0x13)) = ok d ∧
         d.opcode = shift64Opcode funct3 upper := by
  fin_cases hfu <;>
    (simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_and63, toU32_shr12, toU32_shr26, toU32_ofNat,
      rawIType_opcode, rawIType_funct3, rawIType_funct6_zero, rawIType_funct6_sixteen]
     exact classify_of_decode (decode_i_true_spec _ _))

set_option maxHeartbeats 1000000 in
/-- **Shift-immediate (32-bit word) classification** (SLLIW / SRLIW / SRAIW). -/
theorem shift32_family_classifies (rd rs1 shamt funct3 upper : Nat)
    (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 32)
    (hfu : (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)]) :
    ∃ d, decode_32_core (toU32 (rawIType (upper ||| shamt) rs1 funct3 rd 0x1b)) = ok d ∧
         d.opcode = shift32Opcode funct3 upper := by
  fin_cases hfu <;>
    (simp (disch := omega) only [decode_32_core, lift, Bind.bind, bind_ok,
      toU32_and127, toU32_and7, toU32_shr12, toU32_shr25, toU32_ofNat,
      rawIType_opcode, rawIType_funct3, rawIType_funct7_zero, rawIType_funct7_thirtytwo]
     exact classify_of_decode (decode_i_true_spec _ _))

set_option maxHeartbeats 1000000 in
/-- **FENCE classification.** -/
theorem fence_family_classifies (pred succ : Nat) (hp : pred < 16) (hs : succ < 16) :
    ∃ d, decode_32_core (toU32 (rawSupportedFence pred succ)) = ok d ∧
         d.opcode = RiscvOpcode.Fence := by
  exact ⟨_, by
    simp (disch := omega) only [decode_32_core, decode_fence, DecodedRv64im.new,
      lift, Bind.bind, bind_ok,
      toU32_and127, toU32_and28672, toU32_and3968, toU32_and1015808, toU32_and4027551616,
      toU32_and15, toU32_shr12, toU32_shr7, toU32_shr15, toU32_shr20, toU32_shr24, toU32_ofNat,
      rawSupportedFence_opcode, rawSupportedFence_funct3, rawSupportedFence_zeros]
    rfl, rfl⟩

end ZiskFv.Compliance.Decode
