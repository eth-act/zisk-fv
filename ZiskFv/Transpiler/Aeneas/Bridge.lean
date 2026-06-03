import ZiskFv.Transpiler.Aeneas.Generated

open Aeneas Aeneas.Std Result

namespace ZiskFv.Transpiler.Aeneas

abbrev Rv64imInst := zisk_core.rv64im_transpiler.Rv64imInst
abbrev Rv64imOp := zisk_core.rv64im_transpiler.Rv64imOp
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
def srcMem : Nat := 3
def srcInd : Nat := 5
def srcReg : Nat := 6

def storeNone : Nat := 0
def storeMem : Nat := 1
def storeInd : Nat := 2
def storeReg : Nat := 3

def opFlag : Nat := 0x00
def opCopyB : Nat := 0x01
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

def lowerViews (inst : Rv64imInst) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.lower_rv64im32 inst with
  | ok rows => some (rowsView rows)
  | fail _ => none
  | div => none

def luiViews (inst : Rv64imInst) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.lui inst with
  | ok rows => some (rowsView rows)
  | fail _ => none
  | div => none

def auipcViews (inst : Rv64imInst) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.auipc inst with
  | ok rows => some (rowsView rows)
  | fail _ => none
  | div => none

def jalViews (inst : Rv64imInst) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.jal inst with
  | ok rows => some (rowsView rows)
  | fail _ => none
  | div => none

def jalrViews (inst : Rv64imInst) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.jalr inst with
  | ok rows => some (rowsView rows)
  | fail _ => none
  | div => none

def fenceViews (inst : Rv64imInst) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.nop inst with
  | ok rows => some (rowsView rows)
  | fail _ => none
  | div => none

private def copybBase (sr : StaticRow) (paddr : U64) : StaticRow :=
  { { { { sr with paddr := paddr } with op := zisk_core.rv64im_transpiler.OP_COPYB } with
      is_external_op := false } with m32 := false }

private def flagBase (sr : StaticRow) (paddr : U64) : StaticRow :=
  { { { { sr with paddr := paddr } with op := zisk_core.rv64im_transpiler.OP_FLAG } with
      is_external_op := false } with m32 := false }

private theorem row_copyb (paddr : U64) :
    zisk_core.rv64im_transpiler.row paddr zisk_core.rv64im_transpiler.OP_COPYB =
      (do
        let sr ← zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default
        ok (copybBase sr paddr)) := by
  unfold zisk_core.rv64im_transpiler.row copybBase
  unfold zisk_core.rv64im_transpiler.OP_COPYB zisk_core.rv64im_transpiler.OP_FLAG
  rfl

private theorem row_flag (paddr : U64) :
    zisk_core.rv64im_transpiler.row paddr zisk_core.rv64im_transpiler.OP_FLAG =
      (do
        let sr ← zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default
        ok (flagBase sr paddr)) := by
  unfold zisk_core.rv64im_transpiler.row flagBase
  unfold zisk_core.rv64im_transpiler.OP_COPYB zisk_core.rv64im_transpiler.OP_FLAG
  rfl

private theorem staticRowsOne_views (r : StaticRow) :
    (match zisk_core.rv64im_transpiler.StaticRows.one r with
    | ok rows => some (rowsView rows)
    | fail _ => none
    | div => none) = some [rowView r] := by
  unfold zisk_core.rv64im_transpiler.StaticRows.one rowsView Aeneas.Std.Array.make
  unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default
  simp [core.default.DefaultBool.default]

theorem luiViews_static_mode_of_mem
    {inst : Rv64imInst} {row : RowView}
    (h : luiViews inst = some [row]) :
    row.op = Const.opCopyB
  ∧ row.isExternalOp = false
  ∧ row.m32 = false
  ∧ row.setPc = false
  ∧ row.storePc = false := by
  unfold luiViews at h
  unfold zisk_core.rv64im_transpiler.lui at h
  rw [row_copyb] at h
  unfold copybBase at h
  unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default at h
  simp [core.default.DefaultBool.default,
    zisk_core.rv64im_transpiler.source_imm,
    zisk_core.rv64im_transpiler.set_a,
    zisk_core.rv64im_transpiler.set_b,
    zisk_core.rv64im_transpiler.store_reg,
    zisk_core.rv64im_transpiler.set_store,
    zisk_core.rv64im_transpiler.set_j,
    zisk_core.rv64im_transpiler.OP_COPYB,
    zisk_core.zisk_inst.SRC_IMM,
    zisk_core.zisk_inst.STORE_NONE,
    zisk_core.zisk_inst.STORE_REG] at h
  cases h0 : (0#u64 >>> 32#i32) <;> simp [h0] at h
  rename_i x
  cases h1 : lift (x &&& 4294967295#u64) <;> simp [h1] at h
  rename_i x1
  cases h2 : lift (0#u64 &&& 4294967295#u64) <;> simp [h2] at h
  rename_i x2
  cases h3 : lift (IScalar.hcast UScalarTy.U64 inst.imm) <;> simp [h3] at h
  rename_i imm64
  cases h4 : (imm64 >>> 32#i32) <;> simp [h4] at h
  rename_i hi
  cases h5 : lift (hi &&& 4294967295#u64) <;> simp [h5] at h
  rename_i hi32
  cases h6 : lift (imm64 &&& 4294967295#u64) <;> simp [h6] at h
  rename_i lo32
  by_cases hrd : inst.rd = 0#u32
  · simp [hrd, staticRowsOne_views] at h
    cases h
    simp [rowView, Const.opCopyB]
  · simp [hrd] at h
    cases h7 : lift (UScalar.hcast IScalarTy.I64 inst.rd) <;> simp [h7] at h
    rename_i rd64
    unfold zisk_core.rv64im_transpiler.StaticRows.one at h
    unfold rowsView Aeneas.Std.Array.make at h
    unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default at h
    simp [core.default.DefaultBool.default] at h
    cases h
    simp [rowView, Const.opCopyB]

theorem auipcViews_static_mode_of_mem
    {inst : Rv64imInst} {row : RowView}
    (h_rd : inst.rd ≠ 0#u32)
    (h : auipcViews inst = some [row]) :
    row.op = Const.opFlag
  ∧ row.isExternalOp = false
  ∧ row.m32 = false
  ∧ row.setPc = false
  ∧ row.storePc = true := by
  unfold auipcViews at h
  unfold zisk_core.rv64im_transpiler.auipc at h
  rw [row_flag] at h
  unfold flagBase at h
  unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default at h
  simp [core.default.DefaultBool.default,
    zisk_core.rv64im_transpiler.source_imm,
    zisk_core.rv64im_transpiler.set_a,
    zisk_core.rv64im_transpiler.set_b,
    zisk_core.rv64im_transpiler.store_reg,
    zisk_core.rv64im_transpiler.set_store,
    zisk_core.rv64im_transpiler.set_j,
    zisk_core.rv64im_transpiler.OP_FLAG,
    zisk_core.zisk_inst.SRC_IMM,
    zisk_core.zisk_inst.STORE_REG] at h
  cases h0 : (0#u64 >>> 32#i32) <;> simp [h0] at h
  rename_i x
  cases h1 : lift (x &&& 4294967295#u64) <;> simp [h1] at h
  rename_i x1
  cases h2 : lift (0#u64 &&& 4294967295#u64) <;> simp [h2] at h
  rename_i x2
  simp [h_rd] at h
  cases h4 : lift (UScalar.hcast IScalarTy.I64 inst.rd) <;> simp [h4] at h
  rename_i rd64
  cases h3 : lift (IScalar.cast IScalarTy.I64 inst.imm) <;> simp [h3] at h
  rename_i imm64
  unfold zisk_core.rv64im_transpiler.StaticRows.one at h
  unfold rowsView Aeneas.Std.Array.make at h
  unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default at h
  simp [core.default.DefaultBool.default] at h
  cases h
  simp [rowView, Const.opFlag]

theorem jalViews_static_mode_of_mem
    {inst : Rv64imInst} {row : RowView}
    (h_rd : inst.rd ≠ 0#u32)
    (h : jalViews inst = some [row]) :
    row.op = Const.opFlag
  ∧ row.isExternalOp = false
  ∧ row.m32 = false
  ∧ row.setPc = false
  ∧ row.storePc = true := by
  unfold jalViews at h
  unfold zisk_core.rv64im_transpiler.jal at h
  rw [row_flag] at h
  unfold flagBase at h
  unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default at h
  simp [core.default.DefaultBool.default,
    zisk_core.rv64im_transpiler.source_imm,
    zisk_core.rv64im_transpiler.set_a,
    zisk_core.rv64im_transpiler.set_b,
    zisk_core.rv64im_transpiler.store_reg,
    zisk_core.rv64im_transpiler.set_store,
    zisk_core.rv64im_transpiler.set_j,
    zisk_core.rv64im_transpiler.OP_FLAG,
    zisk_core.zisk_inst.SRC_IMM,
    zisk_core.zisk_inst.STORE_REG] at h
  cases h0 : (0#u64 >>> 32#i32) <;> simp [h0] at h
  rename_i x
  cases h1 : lift (x &&& 4294967295#u64) <;> simp [h1] at h
  rename_i x1
  cases h2 : lift (0#u64 &&& 4294967295#u64) <;> simp [h2] at h
  rename_i x2
  simp [h_rd] at h
  cases h4 : lift (UScalar.hcast IScalarTy.I64 inst.rd) <;> simp [h4] at h
  rename_i rd64
  cases h3 : lift (IScalar.cast IScalarTy.I64 inst.imm) <;> simp [h3] at h
  rename_i imm64
  unfold zisk_core.rv64im_transpiler.StaticRows.one at h
  unfold rowsView Aeneas.Std.Array.make at h
  unfold zisk_core.rv64im_transpiler.StaticRow.Insts.CoreDefaultDefault.default at h
  simp [core.default.DefaultBool.default] at h
  cases h
  simp [rowView, Const.opFlag]

def decodeLowerViews (word : U32) : Option (List RowView) :=
  match zisk_core.rv64im_transpiler.decode_and_lower_rv64im32 word 0#u64 with
  | ok (some rows) => some (rowsView rows)
  | ok none => none
  | fail _ => none
  | div => none

end ZiskFv.Transpiler.Aeneas
