-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `srlw`: logical shift-right of low 32 bits by low 5 bits of rs2.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SrlwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure SrlwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_RTYPE_srlw_pure (input : SrlwInput) : SrlwOutput := sorry

  lemma execute_RTYPE_srlw_pure_equiv : True := by trivial

end PureSpec
