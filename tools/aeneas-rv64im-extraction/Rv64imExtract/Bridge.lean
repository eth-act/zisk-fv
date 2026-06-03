import Rv64imExtract.Generated

open Aeneas Aeneas.Std Result

namespace Rv64imExtract.Bridge

abbrev StaticRow := zisk_core.rv64im_transpiler.StaticRow
abbrev StaticRows := zisk_core.rv64im_transpiler.StaticRows

structure RowView where
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
def srcImm : Nat := 2
def srcInd : Nat := 5
def srcReg : Nat := 6

def storeNone : Nat := 0
def storeInd : Nat := 2
def storeReg : Nat := 3

def opFlag : Nat := 0x00
def opCopyB : Nat := 0x01
def opAdd : Nat := 0x0a
def opAnd : Nat := 0x0e

end Const

def rowView (r : StaticRow) : RowView :=
  { paddr := r.paddr.val
    op := r.op.val
    aSrc := r.a_src.val
    aUseSpImm1 := r.a_use_sp_imm1.val
    aOffsetImm0 := r.a_offset_imm0.val
    bSrc := r.b_src.val
    bUseSpImm1 := r.b_use_sp_imm1.val
    bOffsetImm0 := r.b_offset_imm0.val
    store := r.store.val
    storeOffset := r.store_offset.val
    storePc := r.store_pc
    setPc := r.set_pc
    indWidth := r.ind_width.val
    jmpOffset1 := r.jmp_offset1.val
    jmpOffset2 := r.jmp_offset2.val
    isExternalOp := r.is_external_op
    m32 := r.m32 }

def rowsView (rs : StaticRows) : List RowView :=
  match rs.len.val, rs.rows.val with
  | 0, _ => []
  | 1, first :: _ => [rowView first]
  | _, first :: second :: _ => [rowView first, rowView second]
  | _, _ => []

def decodeLowerViews (word : U32) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.decode_and_lower_rv64im32 word 0#u64 with
  | ok (some rows) => some (rowsView rows)
  | ok none => none
  | fail _ => none
  | div => none

def addiExpected : List RowView :=
  [ { paddr := 0
      op := Const.opCopyB
      aSrc := Const.srcImm
      aUseSpImm1 := 0
      aOffsetImm0 := 0
      bSrc := Const.srcImm
      bUseSpImm1 := 0xffffffff
      bOffsetImm0 := 0xffffffff
      store := Const.storeReg
      storeOffset := 5
      storePc := false
      setPc := false
      indWidth := 0
      jmpOffset1 := 4
      jmpOffset2 := 4
      isExternalOp := false
      m32 := false } ]

def jalrExpected : List RowView :=
  [ { paddr := 0
      op := Const.opAdd
      aSrc := Const.srcImm
      aUseSpImm1 := 0
      aOffsetImm0 := 6
      bSrc := Const.srcReg
      bUseSpImm1 := 0
      bOffsetImm0 := 2
      store := Const.storeNone
      storeOffset := 0
      storePc := false
      setPc := false
      indWidth := 0
      jmpOffset1 := 1
      jmpOffset2 := 1
      isExternalOp := true
      m32 := false },
    { paddr := 1
      op := Const.opAnd
      aSrc := Const.srcImm
      aUseSpImm1 := 0xffffffff
      aOffsetImm0 := 0xfffffffe
      bSrc := Const.srcC
      bUseSpImm1 := 0
      bOffsetImm0 := 0
      store := Const.storeReg
      storeOffset := 1
      storePc := true
      setPc := true
      indWidth := 0
      jmpOffset1 := 0
      jmpOffset2 := 3
      isExternalOp := true
      m32 := false } ]

def sdExpected : List RowView :=
  [ { paddr := 0
      op := Const.opCopyB
      aSrc := Const.srcReg
      aUseSpImm1 := 0
      aOffsetImm0 := 4
      bSrc := Const.srcReg
      bUseSpImm1 := 0
      bOffsetImm0 := 3
      store := Const.storeInd
      storeOffset := 8
      storePc := false
      setPc := false
      indWidth := 8
      jmpOffset1 := 4
      jmpOffset2 := 4
      isExternalOp := false
      m32 := false } ]

theorem decode_lower_addi_x5_x0_neg1 :
    decodeLowerViews 0xfff00293#u32 = some addiExpected := by
  native_decide

theorem decode_lower_jalr_x1_6_x2 :
    decodeLowerViews 0x006100e7#u32 = some jalrExpected := by
  native_decide

theorem decode_lower_sd_x3_8_x4 :
    decodeLowerViews 0x00323423#u32 = some sdExpected := by
  native_decide

#print axioms decode_lower_addi_x5_x0_neg1
#print axioms decode_lower_jalr_x1_6_x2
#print axioms decode_lower_sd_x3_8_x4

end Rv64imExtract.Bridge
