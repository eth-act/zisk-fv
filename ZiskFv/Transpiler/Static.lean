import Mathlib.Data.Int.ModEq

/-!
Non-trusted static model of the RV64IM slice of ZisK's Rust transpiler.

This file intentionally models only instruction-static fields populated by
`Riscv2ZiskContext::convert` and `ZiskInstBuilder`. It does not model runtime
register contents, memory values, Main witness columns, or Sail state bridges.
-/

namespace ZiskFv.Transpiler.Static

inductive Rv64Op where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  | addw | subw | sllw | srlw | sraw
  | addi | slli | slti | sltiu | xori | srli | srai | ori | andi
  | addiw | slliw | srliw | sraiw
  | beq | bne | blt | bge | bltu | bgeu
  | lb | lbu | lh | lhu | lw | lwu | ld
  | sb | sh | sw | sd
  | lui | auipc | jal | jalr | fence
  | mul | mulh | mulhsu | mulhu | mulw
  | div | divu | divw | divuw | rem | remu | remw | remuw
  deriving Repr, BEq, DecidableEq

structure Rv64Inst where
  paddr : Nat := 0
  op : Rv64Op
  rd : Nat := 0
  rs1 : Nat := 0
  rs2 : Nat := 0
  imm : Int := 0
  instSize : Nat := 4
  deriving Repr, BEq, DecidableEq

structure ZiskStaticRow where
  paddr : Nat
  op : Nat
  aSrc : Nat
  aUseSpImm1 : Nat
  aOffsetImm0 : Nat
  bSrc : Nat
  bUseSpImm1 : Nat
  bOffsetImm0 : Nat
  store : Nat
  storeOffset : Int
  storePc : Bool
  setPc : Bool
  indWidth : Nat
  jmpOffset1 : Int
  jmpOffset2 : Int
  isExternalOp : Bool
  m32 : Bool
  deriving Repr, BEq, DecidableEq

namespace Const

def srcC : Nat := 0
def srcMem : Nat := 1
def srcImm : Nat := 2
def srcInd : Nat := 5
def srcReg : Nat := 6

def storeNone : Nat := 0
def storeMem : Nat := 1
def storeInd : Nat := 2
def storeReg : Nat := 3

def regFirst : Nat := 0xa0000000

def opFlag : Nat := 0x00
def opCopyB : Nat := 0x01
def opLtu : Nat := 0x06
def opLt : Nat := 0x07
def opEq : Nat := 0x09
def opAdd : Nat := 0x0a
def opSub : Nat := 0x0b
def opAnd : Nat := 0x0e
def opOr : Nat := 0x0f
def opXor : Nat := 0x10
def opAddW : Nat := 0x1a
def opSubW : Nat := 0x1b
def opSll : Nat := 0x21
def opSrl : Nat := 0x22
def opSra : Nat := 0x23
def opSllW : Nat := 0x24
def opSrlW : Nat := 0x25
def opSraW : Nat := 0x26
def opSignExtendB : Nat := 0x27
def opSignExtendH : Nat := 0x28
def opSignExtendW : Nat := 0x29
def opMulhu : Nat := 0xb1
def opMulhsu : Nat := 0xb3
def opMul : Nat := 0xb4
def opMulh : Nat := 0xb5
def opMulW : Nat := 0xb6
def opDivu : Nat := 0xb8
def opRemu : Nat := 0xb9
def opDiv : Nat := 0xba
def opRem : Nat := 0xbb
def opDivuW : Nat := 0xbc
def opRemuW : Nat := 0xbd
def opDivW : Nat := 0xbe
def opRemW : Nat := 0xbf

end Const

def pow2_64 : Int := 18446744073709551616
def pow2_32 : Nat := 4294967296

def u64OfInt (x : Int) : Nat :=
  Int.toNat (x % pow2_64)

def lo32OfInt (x : Int) : Nat :=
  u64OfInt x % pow2_32

def hi32OfInt (x : Int) : Nat :=
  u64OfInt x / pow2_32

def regAddr (r : Nat) : Nat :=
  Const.regFirst + r * 8

def sourceReg (r : Nat) : Nat × Nat × Nat :=
  if r = 0 then
    (Const.srcImm, 0, 0)
  else
    (Const.srcReg, 0, r)

def sourceImm (x : Int) : Nat × Nat × Nat :=
  (Const.srcImm, hi32OfInt x, lo32OfInt x)

def sourceInd (offset : Int) : Nat × Nat × Nat :=
  (Const.srcInd, 0, u64OfInt offset)

def storeReg (r : Nat) (storePc : Bool := false) : Nat × Int × Bool :=
  if r = 0 then
    (Const.storeNone, 0, false)
  else
    (Const.storeReg, Int.ofNat r, storePc)

def externalOp (op : Nat) : Bool :=
  op ≠ Const.opFlag && op ≠ Const.opCopyB

def row
    (paddr op : Nat)
    (a b : Nat × Nat × Nat)
    (store : Nat × Int × Bool)
    (setPc : Bool)
    (indWidth : Nat)
    (jmpOffset1 jmpOffset2 : Int)
    (m32 : Bool) : ZiskStaticRow :=
  { paddr := paddr
    op := op
    aSrc := a.1
    aUseSpImm1 := a.2.1
    aOffsetImm0 := a.2.2
    bSrc := b.1
    bUseSpImm1 := b.2.1
    bOffsetImm0 := b.2.2
    store := store.1
    storeOffset := store.2.1
    storePc := store.2.2
    setPc := setPc
    indWidth := indWidth
    jmpOffset1 := jmpOffset1
    jmpOffset2 := jmpOffset2
    isExternalOp := externalOp op
    m32 := m32 }

def opCode : Rv64Op → Nat
  | .add | .addi => Const.opAdd
  | .sub => Const.opSub
  | .slt | .slti | .blt | .bge => Const.opLt
  | .sltu | .sltiu | .bltu | .bgeu => Const.opLtu
  | .xor | .xori => Const.opXor
  | .or | .ori => Const.opOr
  | .and | .andi | .jalr => Const.opAnd
  | .addw | .addiw => Const.opAddW
  | .subw => Const.opSubW
  | .sll | .slli => Const.opSll
  | .srl | .srli => Const.opSrl
  | .sra | .srai => Const.opSra
  | .sllw | .slliw => Const.opSllW
  | .srlw | .srliw => Const.opSrlW
  | .sraw | .sraiw => Const.opSraW
  | .beq | .bne => Const.opEq
  | .lb => Const.opSignExtendB
  | .lh => Const.opSignExtendH
  | .lw => Const.opSignExtendW
  | .lbu | .lhu | .lwu | .ld | .sb | .sh | .sw | .sd | .lui => Const.opCopyB
  | .auipc | .jal | .fence => Const.opFlag
  | .mul => Const.opMul
  | .mulh => Const.opMulh
  | .mulhsu => Const.opMulhsu
  | .mulhu => Const.opMulhu
  | .mulw => Const.opMulW
  | .div => Const.opDiv
  | .divu => Const.opDivu
  | .divw => Const.opDivW
  | .divuw => Const.opDivuW
  | .rem => Const.opRem
  | .remu => Const.opRemu
  | .remw => Const.opRemW
  | .remuw => Const.opRemuW

def isWOp : Rv64Op → Bool
  | .addw | .subw | .sllw | .srlw | .sraw
  | .addiw | .slliw | .srliw | .sraiw
  | .mulw | .divw | .divuw | .remw | .remuw => true
  | _ => false

def registerOp (i : Rv64Inst) (op : Nat) : List ZiskStaticRow :=
  [row i.paddr op (sourceReg i.rs1) (sourceReg i.rs2) (storeReg i.rd)
    false 0 (Int.ofNat i.instSize) (Int.ofNat i.instSize) (isWOp i.op)]

def immediateOp (i : Rv64Inst) (op : Nat) : List ZiskStaticRow :=
  [row i.paddr op (sourceReg i.rs1) (sourceImm i.imm) (storeReg i.rd)
    false 0 (Int.ofNat i.instSize) (Int.ofNat i.instSize) (isWOp i.op)]

def branchOp (i : Rv64Inst) (op : Nat) (negated : Bool) : List ZiskStaticRow :=
  let j1 := if negated then Int.ofNat i.instSize else i.imm
  let j2 := if negated then i.imm else Int.ofNat i.instSize
  [row i.paddr op (sourceReg i.rs1) (sourceReg i.rs2) (Const.storeNone, 0, false)
    false 0 j1 j2 false]

def loadWidth : Rv64Op → Nat
  | .lb | .lbu => 1
  | .lh | .lhu => 2
  | .lw | .lwu => 4
  | .ld => 8
  | _ => 0

def storeWidth : Rv64Op → Nat
  | .sb => 1
  | .sh => 2
  | .sw => 4
  | .sd => 8
  | _ => 0

def transpile (i : Rv64Inst) : List ZiskStaticRow :=
  match i.op with
  | .add =>
      if i.rs1 = 0 || i.rs2 = 0 then
        let rs := if i.rs1 = 0 then i.rs2 else i.rs1
        [row i.paddr Const.opCopyB (sourceImm 0) (sourceReg rs) (storeReg i.rd)
          false 0 i.instSize i.instSize false]
      else registerOp i Const.opAdd
  | .or =>
      if i.rs1 = 0 || i.rs2 = 0 then
        let rs := if i.rs1 = 0 then i.rs2 else i.rs1
        [row i.paddr Const.opCopyB (sourceImm 0) (sourceReg rs) (storeReg i.rd)
          false 0 i.instSize i.instSize false]
      else registerOp i Const.opOr
  | .sub | .sll | .slt | .sltu | .xor | .srl | .sra | .and
  | .addw | .subw | .sllw | .srlw | .sraw
  | .mul | .mulh | .mulhsu | .mulhu | .mulw
  | .div | .divu | .divw | .divuw | .rem | .remu | .remw | .remuw =>
      registerOp i (opCode i.op)
  | .addi =>
      if i.rd = 0 then
        let a := if i.rs1 = 0 then sourceImm 0 else sourceReg i.rs1
        let b := if i.rs1 = 0 then sourceImm 0 else sourceImm i.imm
        [row i.paddr Const.opFlag a b (Const.storeNone, 0, false)
          false 0 (Int.ofNat i.instSize) (Int.ofNat i.instSize) false]
      else if i.imm = 0 && i.rs1 ≠ 0 then
        [row i.paddr Const.opCopyB (sourceImm 0) (sourceReg i.rs1) (storeReg i.rd)
          false 0 i.instSize i.instSize false]
      else if i.rs1 = 0 then
        [row i.paddr Const.opCopyB (sourceReg i.rs1) (sourceImm i.imm) (storeReg i.rd)
          false 0 i.instSize i.instSize false]
      else immediateOp i Const.opAdd
  | .xori | .ori =>
      let op := if i.op = .xori then Const.opXor else Const.opOr
      let op := if i.rs1 = 0 then Const.opCopyB else op
      immediateOp i op
  | .addiw =>
      if i.rd = 0 && i.rs1 = 0 && i.imm = 0 then
        [row i.paddr Const.opFlag (sourceImm 0) (sourceImm 0) (Const.storeNone, 0, false)
          false 0 (Int.ofNat i.instSize) (Int.ofNat i.instSize) false]
      else immediateOp i Const.opAddW
  | .slli | .slti | .sltiu | .srli | .srai | .andi
  | .slliw | .srliw | .sraiw =>
      immediateOp i (opCode i.op)
  | .beq => branchOp i Const.opEq false
  | .bne => branchOp i Const.opEq true
  | .blt => branchOp i Const.opLt false
  | .bge => branchOp i Const.opLt true
  | .bltu => branchOp i Const.opLtu false
  | .bgeu => branchOp i Const.opLtu true
  | .lb | .lbu | .lh | .lhu | .lw | .lwu | .ld =>
      [row i.paddr (opCode i.op) (sourceReg i.rs1) (sourceInd i.imm) (storeReg i.rd)
        false (loadWidth i.op) (Int.ofNat i.instSize) (Int.ofNat i.instSize) (i.op = .lw)]
  | .sb | .sh | .sw | .sd =>
      [row i.paddr Const.opCopyB (sourceReg i.rs1) (sourceReg i.rs2)
        (Const.storeInd, i.imm, false) false (storeWidth i.op) i.instSize i.instSize false]
  | .lui =>
      [row i.paddr Const.opCopyB (sourceImm 0) (sourceImm i.imm) (storeReg i.rd)
        false 0 i.instSize i.instSize false]
  | .auipc =>
      [row i.paddr Const.opFlag (sourceImm 0) (sourceImm 0) (storeReg i.rd true)
        false 0 4 i.imm false]
  | .jal =>
      [row i.paddr Const.opFlag (sourceImm 0) (sourceImm 0) (storeReg i.rd true)
        false 0 i.imm i.instSize false]
  | .jalr =>
      let mask : Int := 0xfffffffffffffffe
      if i.imm % 4 = 0 then
        [row i.paddr Const.opAnd (sourceImm mask) (sourceReg i.rs1) (storeReg i.rd true)
          true 0 i.imm i.instSize false]
      else
        [ row i.paddr Const.opAdd (sourceImm i.imm) (sourceReg i.rs1)
            (Const.storeNone, 0, false) false 0 1 1 false
        , row (i.paddr + 1) Const.opAnd (sourceImm mask) (Const.srcC, 0, 0)
            (storeReg i.rd true) true 0 0 (i.instSize - 1) false ]
  | .fence =>
      [row i.paddr Const.opFlag (sourceImm 0) (sourceImm 0) (Const.storeNone, 0, false)
        false 0 i.instSize i.instSize false]

def rowCount (i : Rv64Inst) : Nat :=
  (transpile i).length

example : rowCount { op := .add, rd := 3, rs1 := 1, rs2 := 2 } = 1 := by
  rfl

example :
    transpile { op := .addi, rd := 5, rs1 := 0, imm := -1 } =
      [row 0 Const.opCopyB (sourceReg 0) (sourceImm (-1)) (storeReg 5)
        false 0 4 4 false] := by
  rfl

example : rowCount { op := .jalr, rd := 1, rs1 := 2, imm := 6 } = 2 := by
  rfl

end ZiskFv.Transpiler.Static
