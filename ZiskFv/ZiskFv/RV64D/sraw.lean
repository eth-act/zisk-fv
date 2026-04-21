-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `sraw`: arithmetic shift-right of low 32 bits by low 5 bits of rs2.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SrawInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure SrawOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_RTYPE_sraw_pure (input : SrawInput) : SrawOutput := sorry

  lemma execute_RTYPE_sraw_pure_equiv : True := by trivial

end PureSpec
