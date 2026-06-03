import ZiskFv.Transpiler.Aeneas.Bridge

namespace ZiskFv.Transpiler.Aeneas

/-!
# Aeneas RV64IM decode/lower smoke checks

These are concrete checks over the imported Aeneas-extracted decoder/lowerer.
They are not used to prove the canonical opcode theorem; the theorem consumes
`MainAeneasRowProvenance` directly.
-/

theorem decodeLowerViews_lui_0x123452b7 :
    decodeLowerViews 0x123452b7#u32 =
      some
        [ { paddr := 0
            op := Const.opCopyB
            aSrc := Const.srcImm
            aUseSpImm1 := 0
            aOffsetImm0 := 0
            bSrc := Const.srcImm
            bUseSpImm1 := 0
            bOffsetImm0 := 305418240
            store := Const.storeReg
            storeOffset := 5
            storePc := false
            setPc := false
            indWidth := 0
            jmpOffset1 := 4
            jmpOffset2 := 4
            isExternalOp := false
            m32 := false } ] := by
  native_decide

end ZiskFv.Transpiler.Aeneas
