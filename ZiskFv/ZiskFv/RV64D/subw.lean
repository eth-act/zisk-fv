-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `subw`: 32-bit subtract of low halves, sign-extended into rd.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SubwInput where
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    PC : BitVec 64

  structure SubwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_RTYPE_subw_pure (input : SubwInput) : SubwOutput := sorry

  lemma execute_RTYPE_subw_pure_equiv : True := by trivial

end PureSpec
