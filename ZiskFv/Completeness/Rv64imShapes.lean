import Mathlib
import ZiskFv.Completeness.Rv

/-!
# RV64IM raw shape families

This module records the raw-instruction families used by the generated Aeneas
RV-completeness harness. It deliberately contains no Aeneas-generated code:
`scripts/aeneas-production-extract.sh` regenerates and checks the production
decoder/lowering predicates in a separate Lean workspace.

The purpose here is to keep the family names and raw encoders stable in the
normal repository build, so broad completeness claims can be stated against
the same shapes that the generated harness exercises.
-/

namespace ZiskFv.Completeness.Rv64imShapes

abbrev RawInstruction := Rv.RawInstruction

def rawOfNat32 (n : Nat) : RawInstruction :=
  BitVec.ofNat 32 n

def rawOpcode (raw : RawInstruction) : Nat :=
  raw.toNat % 128

def rawFunct3 (raw : RawInstruction) : Nat :=
  (raw.toNat / 4096) % 8

def rawRd (raw : RawInstruction) : Nat :=
  (raw.toNat / 128) % 32

def rawRs1 (raw : RawInstruction) : Nat :=
  (raw.toNat / 32768) % 32

def rawFm (raw : RawInstruction) : Nat :=
  (raw.toNat / 268435456) % 16

def rawRType (funct7 rs2 rs1 funct3 rd opcode : Nat) : RawInstruction :=
  rawOfNat32
    ((funct7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| (rd <<< 7) ||| opcode)

def rawIType (imm rs1 funct3 rd opcode : Nat) : RawInstruction :=
  rawOfNat32
    (((imm % 4096) <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| (rd <<< 7) ||| opcode)

def rawSType (imm rs2 rs1 funct3 : Nat) : RawInstruction :=
  let imm12 := imm % 4096
  rawOfNat32
    (((imm12 >>> 5) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) |||
      (funct3 <<< 12) ||| ((imm12 &&& 0x1f) <<< 7) ||| 0x23)

def rawBType (imm rs2 rs1 funct3 : Nat) : RawInstruction :=
  let imm13 := imm % 8192
  rawOfNat32
    ((((imm13 >>> 12) &&& 1) <<< 31) |||
      (((imm13 >>> 5) &&& 0x3f) <<< 25) |||
      (rs2 <<< 20) ||| (rs1 <<< 15) ||| (funct3 <<< 12) |||
      (((imm13 >>> 1) &&& 0xf) <<< 8) |||
      (((imm13 >>> 11) &&& 1) <<< 7) ||| 0x63)

def rawUType (imm rd opcode : Nat) : RawInstruction :=
  rawOfNat32 ((imm &&& 0xfffff000) ||| (rd <<< 7) ||| opcode)

def rawJType (imm rd : Nat) : RawInstruction :=
  let imm21 := imm % 2097152
  rawOfNat32
    ((((imm21 >>> 20) &&& 1) <<< 31) |||
      (((imm21 >>> 1) &&& 0x3ff) <<< 21) |||
      (((imm21 >>> 11) &&& 1) <<< 20) |||
      (((imm21 >>> 12) &&& 0xff) <<< 12) ||| (rd <<< 7) ||| 0x6f)

def rawSupportedFence (pred succ : Nat) : RawInstruction :=
  rawOfNat32 ((pred <<< 24) ||| (succ <<< 20) ||| 0x0f)

def allRvRegs : List Nat :=
  List.range 32

def allRTypeOpcodeShapes : List (Nat × Nat × Nat) := [
  (0, 0, 0x33),  (32, 0, 0x33), (0, 1, 0x33),  (0, 2, 0x33),
  (0, 3, 0x33),  (0, 4, 0x33),  (0, 5, 0x33),  (32, 5, 0x33),
  (0, 6, 0x33),  (0, 7, 0x33),  (0, 0, 0x3b),  (32, 0, 0x3b),
  (0, 1, 0x3b),  (0, 5, 0x3b),  (32, 5, 0x3b), (1, 0, 0x33),
  (1, 1, 0x33),  (1, 2, 0x33),  (1, 3, 0x33),  (1, 0, 0x3b),
  (1, 4, 0x33),  (1, 5, 0x33),  (1, 4, 0x3b),  (1, 5, 0x3b),
  (1, 6, 0x33),  (1, 7, 0x33),  (1, 6, 0x3b),  (1, 7, 0x3b)
]

def edgeIImmediates : List Nat := [
  2048, -- -2048 sign-extended through the 12-bit immediate field
  4095, -- -1
  0,
  1,
  2047
]

def shift64Amounts : List Nat :=
  List.range 64

def shift32Amounts : List Nat :=
  List.range 32

def edgeSImmediates : List Nat := [
  2048, -- -2048 sign-extended through the 12-bit immediate field
  4088, -- -8
  0,
  7,
  2047
]

def edgeBImmediates : List Nat := [
  4096, -- -4096 sign-extended through the 13-bit immediate field
  8188, -- -4
  0,
  4,
  4094
]

def edgeUImmediates : List Nat := [
  0,
  0x1000,
  0x7ffff000,
  0x80000000,
  0xfffff000
]

def edgeJImmediates : List Nat := [
  1048576, -- -1048576 sign-extended through the 21-bit immediate field
  2097148, -- -4
  0,
  4,
  1048574
]

/-- All register combinations for the R/RW/M opcode shapes. This family is
exhaustive for those opcode encodings because they have no immediate field. -/
def RTypeRegisterShape (raw : RawInstruction) : Prop :=
  ∃ funct7 funct3 opcode rd rs1 rs2,
    (funct7, funct3, opcode) ∈ allRTypeOpcodeShapes ∧
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ rs2 ∈ allRvRegs ∧
    raw = rawRType funct7 rs2 rs1 funct3 rd opcode

/-- Exact raw ADD shape: funct7 = 0, funct3 = 0, opcode = 0x33, with all
register triples. -/
def AddRawShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 rs2,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ rs2 ∈ allRvRegs ∧
    raw = rawRType 0 rs2 rs1 0 rd 0x33

theorem add_raw_shape_subset_r_type_register_shape
    {raw : RawInstruction} (h : AddRawShape raw) :
    RTypeRegisterShape raw := by
  rcases h with ⟨rd, rs1, rs2, h_rd, h_rs1, h_rs2, h_raw⟩
  exact
    ⟨0, 0, 0x33, rd, rs1, rs2,
      by simp [allRTypeOpcodeShapes],
      h_rd, h_rs1, h_rs2, h_raw⟩

def ITypeRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm funct3 opcode,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm ∈ edgeIImmediates ∧
    (funct3, opcode) ∈ [
      (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
      (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)
    ] ∧
    raw = rawIType imm rs1 funct3 rd opcode

def JalrRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm ∈ edgeIImmediates ∧
    raw = rawIType imm rs1 0 rd 0x67

def ImmediateAluRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm funct3 opcode,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm ∈ edgeIImmediates ∧
    (funct3, opcode) ∈ [
      (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b)
    ] ∧
    raw = rawIType imm rs1 funct3 rd opcode

def LoadRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm funct3,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm ∈ edgeIImmediates ∧
    funct3 ∈ [0, 1, 2, 3, 4, 5, 6] ∧
    raw = rawIType imm rs1 funct3 rd 0x03

/-- Full I-format single-row decode surface, excluding shift-immediate opcodes
which have their own bounded-shamt family. This is the Sail-facing shape:
all 12-bit immediate encodings are included. -/
def ITypeRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm funct3 opcode,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm < 4096 ∧
    (funct3, opcode) ∈ [
      (0, 0x67), (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b), (0, 0x03), (1, 0x03),
      (2, 0x03), (3, 0x03), (4, 0x03), (5, 0x03), (6, 0x03)
    ] ∧
    raw = rawIType imm rs1 funct3 rd opcode

/-- JALR's I-format decode surface. This is split from
`ITypeRegisterImmediateShape` because it is a control-flow helper rather than
an arithmetic or memory row builder. -/
def JalrRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm < 4096 ∧
    raw = rawIType imm rs1 0 rd 0x67

/-- I-format arithmetic/logical immediate opcodes, excluding shift-immediate
encodings whose legal surface is bounded by XLEN-specific shamt fields. -/
def ImmediateAluRegisterShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm funct3 opcode,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm < 4096 ∧
    (funct3, opcode) ∈ [
      (0, 0x13), (2, 0x13), (3, 0x13), (4, 0x13),
      (6, 0x13), (7, 0x13), (0, 0x1b)
    ] ∧
    raw = rawIType imm rs1 funct3 rd opcode

/-- Full I-format load decode surface. This is split out from
`ITypeRegisterImmediateShape` because the generated Aeneas harness now proves
the production load helper materializes rows for every register pair and every
extracted signed immediate. The remaining raw-load obligation is the
encoder/decode/lowering-dispatch bridge from this shape into that helper. -/
def LoadRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd rs1 imm funct3,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ imm < 4096 ∧
    funct3 ∈ [0, 1, 2, 3, 4, 5, 6] ∧
    raw = rawIType imm rs1 funct3 rd 0x03

def ShiftRegisterShape (raw : RawInstruction) : Prop :=
  (∃ rd rs1 shamt funct3 upper,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ shamt ∈ shift64Amounts ∧
    (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)] ∧
    raw = rawIType (upper ||| shamt) rs1 funct3 rd 0x13) ∨
  (∃ rd rs1 shamt funct3 upper,
    rd ∈ allRvRegs ∧ rs1 ∈ allRvRegs ∧ shamt ∈ shift32Amounts ∧
    (funct3, upper) ∈ [(1, 0), (5, 0), (5, 0x400)] ∧
    raw = rawIType (upper ||| shamt) rs1 funct3 rd 0x1b)

def StoreRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rs1 rs2 imm funct3,
    rs1 ∈ allRvRegs ∧ rs2 ∈ allRvRegs ∧ imm ∈ edgeSImmediates ∧
    funct3 ∈ [0, 1, 2, 3] ∧
    raw = rawSType imm rs2 rs1 funct3

/-- Full store decode surface: all 12-bit S-immediate encodings. -/
def StoreRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rs1 rs2 imm funct3,
    rs1 ∈ allRvRegs ∧ rs2 ∈ allRvRegs ∧ imm < 4096 ∧
    funct3 ∈ [0, 1, 2, 3] ∧
    raw = rawSType imm rs2 rs1 funct3

/-- Full memory-immediate decode surface whose row builders are covered by
symbolic-immediate extracted helper-total milestones. -/
def MemoryRegisterImmediateShape (raw : RawInstruction) : Prop :=
  LoadRegisterImmediateShape raw ∨ StoreRegisterImmediateShape raw

def BranchRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rs1 rs2 imm funct3,
    rs1 ∈ allRvRegs ∧ rs2 ∈ allRvRegs ∧ imm ∈ edgeBImmediates ∧
    funct3 ∈ [0, 1, 4, 5, 6, 7] ∧
    raw = rawBType imm rs2 rs1 funct3

/-- Full branch decode surface: all aligned 13-bit B-immediate encodings. -/
def BranchRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rs1 rs2 imm funct3,
    rs1 ∈ allRvRegs ∧ rs2 ∈ allRvRegs ∧ imm < 8192 ∧ imm % 2 = 0 ∧
    funct3 ∈ [0, 1, 4, 5, 6, 7] ∧
    raw = rawBType imm rs2 rs1 funct3

def UpperAndJumpEdgeImmediateShape (raw : RawInstruction) : Prop :=
  (∃ rd imm opcode,
    rd ∈ allRvRegs ∧ imm ∈ edgeUImmediates ∧ opcode ∈ [0x37, 0x17] ∧
    raw = rawUType imm rd opcode) ∨
  (∃ rd imm,
    rd ∈ allRvRegs ∧ imm ∈ edgeJImmediates ∧ raw = rawJType imm rd)

def UpperRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd imm opcode,
    rd ∈ allRvRegs ∧ imm ∈ edgeUImmediates ∧ opcode ∈ [0x37, 0x17] ∧
    raw = rawUType imm rd opcode

def JumpRegisterEdgeImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd imm,
    rd ∈ allRvRegs ∧ imm ∈ edgeJImmediates ∧ raw = rawJType imm rd

/-- Full U-format LUI/AUIPC decode surface. -/
def UpperRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd imm opcode,
    rd ∈ allRvRegs ∧ imm < 2 ^ 32 ∧ imm % 4096 = 0 ∧
    opcode ∈ [0x37, 0x17] ∧
    raw = rawUType imm rd opcode

/-- Full JAL decode surface. -/
def JumpRegisterImmediateShape (raw : RawInstruction) : Prop :=
  ∃ rd imm,
    rd ∈ allRvRegs ∧ imm < 2097152 ∧ imm % 2 = 0 ∧
    raw = rawJType imm rd

/-- Full U/J decode surface. U-immediates are represented as their raw
upper-20-bit value, while J-immediates are aligned 21-bit encodings. -/
def UpperAndJumpImmediateShape (raw : RawInstruction) : Prop :=
  UpperRegisterImmediateShape raw ∨ JumpRegisterImmediateShape raw

def SupportedFencePredSuccShape (raw : RawInstruction) : Prop :=
  ∃ pred succ,
    pred ∈ List.range 16 ∧ succ ∈ List.range 16 ∧
    raw = rawSupportedFence pred succ

def supportedFencePredSuccFieldsOk : Bool :=
  (List.range 16).all fun pred =>
    (List.range 16).all fun succ =>
      let raw := rawSupportedFence pred succ
      rawOpcode raw == 0x0f &&
      rawFunct3 raw == 0 &&
      rawFm raw == 0 &&
      rawRd raw == 0 &&
      rawRs1 raw == 0

theorem supportedFencePredSuccFieldsOk_eq_true :
    supportedFencePredSuccFieldsOk = true := by
  native_decide

theorem supportedFencePredSuccShape_fields_ok
    {raw : RawInstruction} (h : SupportedFencePredSuccShape raw) :
    rawOpcode raw = 0x0f ∧ rawFunct3 raw = 0 ∧ rawFm raw = 0 ∧
      rawRd raw = 0 ∧ rawRs1 raw = 0 := by
  rcases h with ⟨pred, succ, h_pred, h_succ, rfl⟩
  have h_pred_lt : pred < 16 := by
    simpa using List.mem_range.mp h_pred
  have h_succ_lt : succ < 16 := by
    simpa using List.mem_range.mp h_succ
  interval_cases pred <;> interval_cases succ <;>
    native_decide

/-- Shape families whose current grids are exhaustive for their supported
encoding surface:

* R/RW/M register-register opcodes have no immediate field, so all register
  combinations cover the whole family.
* Shift-immediate opcodes use bounded shamt fields, so all register/shamt
  combinations cover the whole family.
* Supported FENCE has only pred/succ bits varying once ZisK's current
  `fm = 0`, `rs1 = x0`, and `rd = x0` restriction is imposed. -/
def ExhaustiveCheckedShape (raw : RawInstruction) : Prop :=
  RTypeRegisterShape raw ∨
  ShiftRegisterShape raw ∨
  SupportedFencePredSuccShape raw

/-- Shape families currently checked on edge immediates. These are broad
production-backed regression checks, but they are not yet exhaustive over every
legal immediate encoding. Universal closure for these families needs either
symbolic row-materialization proofs or a much larger finite strategy. -/
def EdgeCheckedShape (raw : RawInstruction) : Prop :=
  ITypeRegisterEdgeImmediateShape raw ∨
  StoreRegisterEdgeImmediateShape raw ∨
  BranchRegisterEdgeImmediateShape raw ∨
  UpperAndJumpEdgeImmediateShape raw

/-- The finite edge grid split along the same helper families used by the
full supported-decode theorem surface. This is definitionally equivalent to
`EdgeCheckedShape` up to the decomposition lemmas below, but it produces more
diagnostic obligations. -/
def RefinedEdgeCheckedShape (raw : RawInstruction) : Prop :=
  JalrRegisterEdgeImmediateShape raw ∨
  ImmediateAluRegisterEdgeImmediateShape raw ∨
  LoadRegisterEdgeImmediateShape raw ∨
  StoreRegisterEdgeImmediateShape raw ∨
  BranchRegisterEdgeImmediateShape raw ∨
  UpperRegisterEdgeImmediateShape raw ∨
  JumpRegisterEdgeImmediateShape raw

/-- Full raw RV64IM single-row decode surface currently represented in the
extracted production decoder, after applying ZisK's known FENCE restriction.

This is broader than `WideCheckedShape`: the latter is the finite row
materialization grid we can close today, while this shape is the target domain
for the eventual Sail-to-ZisK RV completeness theorem. -/
def SupportedDecodeShape (raw : RawInstruction) : Prop :=
  RTypeRegisterShape raw ∨
  ITypeRegisterImmediateShape raw ∨
  ShiftRegisterShape raw ∨
  StoreRegisterImmediateShape raw ∨
  BranchRegisterImmediateShape raw ∨
  UpperAndJumpImmediateShape raw ∨
  SupportedFencePredSuccShape raw

/-- The same full supported-decode surface as `SupportedDecodeShape`, but
split along the helper families used by the current completeness plan. In
particular, loads and stores are grouped into `MemoryRegisterImmediateShape`
to line up with the extracted memory-helper materialization milestone. -/
def MemoryRefinedSupportedDecodeShape (raw : RawInstruction) : Prop :=
  RTypeRegisterShape raw ∨
  JalrRegisterImmediateShape raw ∨
  ImmediateAluRegisterShape raw ∨
  MemoryRegisterImmediateShape raw ∨
  ShiftRegisterShape raw ∨
  BranchRegisterImmediateShape raw ∨
  UpperRegisterImmediateShape raw ∨
  JumpRegisterImmediateShape raw ∨
  SupportedFencePredSuccShape raw

/-- The broad finite shape grid checked by
`AENEAS_CHECK_RV_COMPLETENESS=1 AENEAS_CHECK_RV_WIDE_SHAPES=1
nix run .#aeneas-production-extract`. -/
def WideCheckedShape (raw : RawInstruction) : Prop :=
  ExhaustiveCheckedShape raw ∨ EdgeCheckedShape raw

/-- The same finite grid as `WideCheckedShape`, with edge checks split into
the helper-level families used by the supported-decode theorem surface. -/
def WideRefinedCheckedShape (raw : RawInstruction) : Prop :=
  ExhaustiveCheckedShape raw ∨ RefinedEdgeCheckedShape raw

theorem edge_i_immediate_lt_4096 {imm : Nat}
    (h : imm ∈ edgeIImmediates) : imm < 4096 := by
  simp [edgeIImmediates] at h
  omega

theorem edge_s_immediate_lt_4096 {imm : Nat}
    (h : imm ∈ edgeSImmediates) : imm < 4096 := by
  simp [edgeSImmediates] at h
  omega

theorem edge_b_immediate_lt_8192 {imm : Nat}
    (h : imm ∈ edgeBImmediates) : imm < 8192 := by
  simp [edgeBImmediates] at h
  omega

theorem edge_b_immediate_aligned {imm : Nat}
    (h : imm ∈ edgeBImmediates) : imm % 2 = 0 := by
  simp [edgeBImmediates] at h
  omega

theorem edge_u_immediate_lt_2_pow_32 {imm : Nat}
    (h : imm ∈ edgeUImmediates) : imm < 2 ^ 32 := by
  simp [edgeUImmediates] at h
  omega

theorem edge_u_immediate_aligned {imm : Nat}
    (h : imm ∈ edgeUImmediates) : imm % 4096 = 0 := by
  simp [edgeUImmediates] at h
  omega

theorem edge_j_immediate_lt_2097152 {imm : Nat}
    (h : imm ∈ edgeJImmediates) : imm < 2097152 := by
  simp [edgeJImmediates] at h
  omega

theorem edge_j_immediate_aligned {imm : Nat}
    (h : imm ∈ edgeJImmediates) : imm % 2 = 0 := by
  simp [edgeJImmediates] at h
  omega

theorem i_type_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : ITypeRegisterEdgeImmediateShape raw) :
    ITypeRegisterImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, h_op, h_raw⟩
  exact
    ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1,
      edge_i_immediate_lt_4096 h_imm, h_op, h_raw⟩

theorem jalr_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : JalrRegisterEdgeImmediateShape raw) :
    JalrRegisterImmediateShape raw := by
  rcases h with ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, h_raw⟩
  exact ⟨rd, rs1, imm, h_rd, h_rs1, edge_i_immediate_lt_4096 h_imm, h_raw⟩

theorem immediate_alu_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : ImmediateAluRegisterEdgeImmediateShape raw) :
    ImmediateAluRegisterShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, h_op, h_raw⟩
  exact
    ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1,
      edge_i_immediate_lt_4096 h_imm, h_op, h_raw⟩

theorem load_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : LoadRegisterEdgeImmediateShape raw) :
    LoadRegisterImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, h_rd, h_rs1, h_imm, h_funct3, h_raw⟩
  exact
    ⟨rd, rs1, imm, funct3, h_rd, h_rs1,
      edge_i_immediate_lt_4096 h_imm, h_funct3, h_raw⟩

theorem jalr_register_edge_immediate_shape_subset_i_type_edge
    {raw : RawInstruction}
    (h : JalrRegisterEdgeImmediateShape raw) :
    ITypeRegisterEdgeImmediateShape raw := by
  rcases h with ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, h_raw⟩
  refine ⟨rd, rs1, imm, 0, 0x67, h_rd, h_rs1, h_imm, ?_, h_raw⟩
  simp

theorem immediate_alu_register_edge_immediate_shape_subset_i_type_edge
    {raw : RawInstruction}
    (h : ImmediateAluRegisterEdgeImmediateShape raw) :
    ITypeRegisterEdgeImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, h_op, h_raw⟩
  refine ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, ?_, h_raw⟩
  simp at h_op ⊢
  rcases h_op with
    h_op | h_op | h_op | h_op | h_op | h_op | h_op <;>
    rcases h_op with ⟨rfl, rfl⟩ <;>
    simp

theorem load_register_edge_immediate_shape_subset_i_type_edge
    {raw : RawInstruction}
    (h : LoadRegisterEdgeImmediateShape raw) :
    ITypeRegisterEdgeImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, h_rd, h_rs1, h_imm, h_funct3, h_raw⟩
  refine ⟨rd, rs1, imm, funct3, 0x03, h_rd, h_rs1, h_imm, ?_, h_raw⟩
  simp at h_funct3 ⊢
  rcases h_funct3 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem i_type_register_edge_immediate_shape_cases
    {raw : RawInstruction}
    (h : ITypeRegisterEdgeImmediateShape raw) :
    JalrRegisterEdgeImmediateShape raw ∨
      ImmediateAluRegisterEdgeImmediateShape raw ∨
      LoadRegisterEdgeImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, opcode,
      h_rd, h_rs1, h_imm, h_op, h_raw⟩
  simp at h_op
  rcases h_op with
    h_op | h_op | h_op | h_op | h_op | h_op | h_op | h_op |
    h_op | h_op | h_op | h_op | h_op | h_op | h_op
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inl ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, h_raw⟩
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 0, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 2, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 3, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 4, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 6, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 7, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 0, 0x1b, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 0, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 1, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 2, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 3, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 4, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 5, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 6, h_rd, h_rs1, h_imm, by simp, h_raw⟩)

theorem jalr_register_immediate_shape_subset
    {raw : RawInstruction}
    (h : JalrRegisterImmediateShape raw) :
    ITypeRegisterImmediateShape raw := by
  rcases h with ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, h_raw⟩
  refine ⟨rd, rs1, imm, 0, 0x67, h_rd, h_rs1, h_imm, ?_, h_raw⟩
  simp

theorem immediate_alu_register_shape_subset
    {raw : RawInstruction}
    (h : ImmediateAluRegisterShape raw) :
    ITypeRegisterImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, h_op, h_raw⟩
  refine ⟨rd, rs1, imm, funct3, opcode, h_rd, h_rs1, h_imm, ?_, h_raw⟩
  simp at h_op ⊢
  rcases h_op with
    h_op | h_op | h_op | h_op | h_op | h_op | h_op <;>
    rcases h_op with ⟨rfl, rfl⟩ <;>
    simp

theorem load_register_immediate_shape_subset
    {raw : RawInstruction}
    (h : LoadRegisterImmediateShape raw) :
    ITypeRegisterImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, h_rd, h_rs1, h_imm, h_funct3, h_raw⟩
  refine ⟨rd, rs1, imm, funct3, 0x03, h_rd, h_rs1, h_imm, ?_, h_raw⟩
  simp at h_funct3 ⊢
  rcases h_funct3 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp

theorem i_type_register_immediate_shape_cases
    {raw : RawInstruction}
    (h : ITypeRegisterImmediateShape raw) :
    JalrRegisterImmediateShape raw ∨
      ImmediateAluRegisterShape raw ∨
      LoadRegisterImmediateShape raw := by
  rcases h with
    ⟨rd, rs1, imm, funct3, opcode,
      h_rd, h_rs1, h_imm, h_op, h_raw⟩
  simp at h_op
  rcases h_op with
    h_op | h_op | h_op | h_op | h_op | h_op | h_op | h_op |
    h_op | h_op | h_op | h_op | h_op | h_op | h_op
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inl ⟨rd, rs1, imm, h_rd, h_rs1, h_imm, h_raw⟩
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 0, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 2, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 3, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 4, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 6, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 7, 0x13, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inl
      ⟨rd, rs1, imm, 0, 0x1b, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 0, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 1, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 2, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 3, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 4, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 5, h_rd, h_rs1, h_imm, by simp, h_raw⟩)
  · rcases h_op with ⟨rfl, rfl⟩
    exact .inr (.inr
      ⟨rd, rs1, imm, 6, h_rd, h_rs1, h_imm, by simp, h_raw⟩)

theorem store_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : StoreRegisterEdgeImmediateShape raw) :
    StoreRegisterImmediateShape raw := by
  rcases h with
    ⟨rs1, rs2, imm, funct3, h_rs1, h_rs2, h_imm, h_funct3, h_raw⟩
  exact
    ⟨rs1, rs2, imm, funct3, h_rs1, h_rs2,
      edge_s_immediate_lt_4096 h_imm, h_funct3, h_raw⟩

theorem branch_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : BranchRegisterEdgeImmediateShape raw) :
    BranchRegisterImmediateShape raw := by
  rcases h with
    ⟨rs1, rs2, imm, funct3, h_rs1, h_rs2, h_imm, h_funct3, h_raw⟩
  exact
    ⟨rs1, rs2, imm, funct3, h_rs1, h_rs2,
      edge_b_immediate_lt_8192 h_imm,
      edge_b_immediate_aligned h_imm, h_funct3, h_raw⟩

theorem upper_and_jump_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : UpperAndJumpEdgeImmediateShape raw) :
    UpperAndJumpImmediateShape raw := by
  rcases h with h_upper | h_jump
  · rcases h_upper with ⟨rd, imm, opcode, h_rd, h_imm, h_opcode, h_raw⟩
    exact .inl
      ⟨rd, imm, opcode, h_rd,
        edge_u_immediate_lt_2_pow_32 h_imm,
        edge_u_immediate_aligned h_imm, h_opcode, h_raw⟩
  · rcases h_jump with ⟨rd, imm, h_rd, h_imm, h_raw⟩
    exact .inr
      ⟨rd, imm, h_rd,
        edge_j_immediate_lt_2097152 h_imm,
        edge_j_immediate_aligned h_imm, h_raw⟩

theorem upper_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : UpperRegisterEdgeImmediateShape raw) :
    UpperRegisterImmediateShape raw := by
  rcases h with ⟨rd, imm, opcode, h_rd, h_imm, h_opcode, h_raw⟩
  exact
    ⟨rd, imm, opcode, h_rd,
      edge_u_immediate_lt_2_pow_32 h_imm,
      edge_u_immediate_aligned h_imm, h_opcode, h_raw⟩

theorem jump_register_edge_immediate_shape_subset
    {raw : RawInstruction}
    (h : JumpRegisterEdgeImmediateShape raw) :
    JumpRegisterImmediateShape raw := by
  rcases h with ⟨rd, imm, h_rd, h_imm, h_raw⟩
  exact
    ⟨rd, imm, h_rd,
      edge_j_immediate_lt_2097152 h_imm,
      edge_j_immediate_aligned h_imm, h_raw⟩

theorem upper_register_edge_immediate_shape_subset_upper_and_jump_edge
    {raw : RawInstruction}
    (h : UpperRegisterEdgeImmediateShape raw) :
    UpperAndJumpEdgeImmediateShape raw :=
  .inl h

theorem jump_register_edge_immediate_shape_subset_upper_and_jump_edge
    {raw : RawInstruction}
    (h : JumpRegisterEdgeImmediateShape raw) :
    UpperAndJumpEdgeImmediateShape raw :=
  .inr h

theorem upper_and_jump_edge_immediate_shape_cases
    {raw : RawInstruction}
    (h : UpperAndJumpEdgeImmediateShape raw) :
    UpperRegisterEdgeImmediateShape raw ∨
      JumpRegisterEdgeImmediateShape raw := by
  exact h

theorem refined_edge_checked_shape_subset_edge_checked
    {raw : RawInstruction}
    (h : RefinedEdgeCheckedShape raw) :
    EdgeCheckedShape raw := by
  rcases h with
    h_jalr | h_alu | h_load | h_store | h_branch | h_upper | h_jump
  · exact .inl (jalr_register_edge_immediate_shape_subset_i_type_edge h_jalr)
  · exact .inl (immediate_alu_register_edge_immediate_shape_subset_i_type_edge h_alu)
  · exact .inl (load_register_edge_immediate_shape_subset_i_type_edge h_load)
  · exact .inr (.inl h_store)
  · exact .inr (.inr (.inl h_branch))
  · exact .inr (.inr (.inr
      (upper_register_edge_immediate_shape_subset_upper_and_jump_edge h_upper)))
  · exact .inr (.inr (.inr
      (jump_register_edge_immediate_shape_subset_upper_and_jump_edge h_jump)))

theorem edge_checked_shape_subset_refined_edge_checked
    {raw : RawInstruction}
    (h : EdgeCheckedShape raw) :
    RefinedEdgeCheckedShape raw := by
  rcases h with h_i | h_store | h_branch | h_upper_jump
  · rcases i_type_register_edge_immediate_shape_cases h_i with
      h_jalr | h_alu | h_load
    · exact .inl h_jalr
    · exact .inr (.inl h_alu)
    · exact .inr (.inr (.inl h_load))
  · exact .inr (.inr (.inr (.inl h_store)))
  · exact .inr (.inr (.inr (.inr (.inl h_branch))))
  · rcases upper_and_jump_edge_immediate_shape_cases h_upper_jump with
      h_upper | h_jump
    · exact .inr (.inr (.inr (.inr (.inr (.inl h_upper)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr h_jump)))))

theorem wide_refined_checked_shape_subset_wide_checked
    {raw : RawInstruction}
    (h : WideRefinedCheckedShape raw) :
    WideCheckedShape raw := by
  rcases h with h_exhaustive | h_refined
  · exact .inl h_exhaustive
  · exact .inr (refined_edge_checked_shape_subset_edge_checked h_refined)

theorem wide_checked_shape_subset_wide_refined_checked
    {raw : RawInstruction}
    (h : WideCheckedShape raw) :
    WideRefinedCheckedShape raw := by
  rcases h with h_exhaustive | h_edge
  · exact .inl h_exhaustive
  · exact .inr (edge_checked_shape_subset_refined_edge_checked h_edge)

theorem upper_register_immediate_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : UpperRegisterImmediateShape raw) :
    SupportedDecodeShape raw :=
  .inr (.inr (.inr (.inr (.inr (.inl (.inl h))))))

theorem jump_register_immediate_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : JumpRegisterImmediateShape raw) :
    SupportedDecodeShape raw :=
  .inr (.inr (.inr (.inr (.inr (.inl (.inr h))))))

theorem jalr_register_immediate_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : JalrRegisterImmediateShape raw) :
    SupportedDecodeShape raw :=
  .inr (.inl (jalr_register_immediate_shape_subset h))

theorem immediate_alu_register_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : ImmediateAluRegisterShape raw) :
    SupportedDecodeShape raw :=
  .inr (.inl (immediate_alu_register_shape_subset h))

theorem memory_register_immediate_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : MemoryRegisterImmediateShape raw) :
    SupportedDecodeShape raw := by
  rcases h with h_load | h_store
  · exact .inr (.inl (load_register_immediate_shape_subset h_load))
  · exact .inr (.inr (.inr (.inl h_store)))

theorem memory_refined_supported_decode_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : MemoryRefinedSupportedDecodeShape raw) :
    SupportedDecodeShape raw := by
  rcases h with
    h_r | h_jalr | h_alu | h_memory | h_shift | h_branch |
    h_upper | h_jump | h_fence
  · exact .inl h_r
  · exact .inr (.inl (jalr_register_immediate_shape_subset h_jalr))
  · exact .inr (.inl (immediate_alu_register_shape_subset h_alu))
  · exact memory_register_immediate_shape_subset_supported_decode h_memory
  · exact .inr (.inr (.inl h_shift))
  · exact .inr (.inr (.inr (.inr (.inl h_branch))))
  · exact upper_register_immediate_shape_subset_supported_decode h_upper
  · exact jump_register_immediate_shape_subset_supported_decode h_jump
  · exact .inr (.inr (.inr (.inr (.inr (.inr h_fence)))))

theorem supported_decode_shape_subset_memory_refined_supported_decode_shape
    {raw : RawInstruction}
    (h : SupportedDecodeShape raw) :
    MemoryRefinedSupportedDecodeShape raw := by
  rcases h with
    h_r | h_i | h_shift | h_store | h_branch | h_upper_jump | h_fence
  · exact .inl h_r
  · rcases i_type_register_immediate_shape_cases h_i with
      h_jalr | h_alu | h_load
    · exact .inr (.inl h_jalr)
    · exact .inr (.inr (.inl h_alu))
    · exact .inr (.inr (.inr (.inl (.inl h_load))))
  · exact .inr (.inr (.inr (.inr (.inl h_shift))))
  · exact .inr (.inr (.inr (.inl (.inr h_store))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h_branch)))))
  · rcases h_upper_jump with h_upper | h_jump
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h_upper))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h_jump)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h_fence)))))))

theorem exhaustive_checked_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : ExhaustiveCheckedShape raw) :
    SupportedDecodeShape raw := by
  rcases h with h_r | h_shift | h_fence
  · exact .inl h_r
  · exact .inr (.inr (.inl h_shift))
  · exact .inr (.inr (.inr (.inr (.inr (.inr h_fence)))))

theorem edge_checked_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : EdgeCheckedShape raw) :
    SupportedDecodeShape raw := by
  rcases h with h_i | h_store | h_branch | h_upper_jump
  · exact .inr (.inl (i_type_register_edge_immediate_shape_subset h_i))
  · exact .inr (.inr (.inr
      (.inl (store_register_edge_immediate_shape_subset h_store))))
  · exact .inr (.inr (.inr (.inr
      (.inl (branch_register_edge_immediate_shape_subset h_branch)))))
  · exact .inr (.inr (.inr (.inr (.inr
      (.inl (upper_and_jump_edge_immediate_shape_subset h_upper_jump))))))

theorem wide_checked_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : WideCheckedShape raw) :
    SupportedDecodeShape raw := by
  rcases h with h_exhaustive | h_edge
  · exact exhaustive_checked_shape_subset_supported_decode h_exhaustive
  · exact edge_checked_shape_subset_supported_decode h_edge

theorem wide_refined_checked_shape_subset_supported_decode
    {raw : RawInstruction}
    (h : WideRefinedCheckedShape raw) :
    SupportedDecodeShape raw :=
  wide_checked_shape_subset_supported_decode
    (wide_refined_checked_shape_subset_wide_checked h)

theorem exhaustive_checked_shape_subset_memory_refined_supported_decode
    {raw : RawInstruction}
    (h : ExhaustiveCheckedShape raw) :
    MemoryRefinedSupportedDecodeShape raw :=
  supported_decode_shape_subset_memory_refined_supported_decode_shape
    (exhaustive_checked_shape_subset_supported_decode h)

theorem edge_checked_shape_subset_memory_refined_supported_decode
    {raw : RawInstruction}
    (h : EdgeCheckedShape raw) :
    MemoryRefinedSupportedDecodeShape raw :=
  supported_decode_shape_subset_memory_refined_supported_decode_shape
    (edge_checked_shape_subset_supported_decode h)

theorem refined_edge_checked_shape_subset_memory_refined_supported_decode
    {raw : RawInstruction}
    (h : RefinedEdgeCheckedShape raw) :
    MemoryRefinedSupportedDecodeShape raw :=
  edge_checked_shape_subset_memory_refined_supported_decode
    (refined_edge_checked_shape_subset_edge_checked h)

theorem wide_checked_shape_subset_memory_refined_supported_decode
    {raw : RawInstruction}
    (h : WideCheckedShape raw) :
    MemoryRefinedSupportedDecodeShape raw :=
  supported_decode_shape_subset_memory_refined_supported_decode_shape
    (wide_checked_shape_subset_supported_decode h)

theorem wide_refined_checked_shape_subset_memory_refined_supported_decode
    {raw : RawInstruction}
    (h : WideRefinedCheckedShape raw) :
    MemoryRefinedSupportedDecodeShape raw :=
  supported_decode_shape_subset_memory_refined_supported_decode_shape
    (wide_refined_checked_shape_subset_supported_decode h)

end ZiskFv.Completeness.Rv64imShapes
