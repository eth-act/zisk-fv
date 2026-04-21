-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `addiw`: 32-bit add of immediate to low half, sign-extended into rd.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure AddiwInput where
    r1_val : BitVec 64
    imm : BitVec 12
    rd : Fin 32
    PC : BitVec 64

  structure AddiwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_ITYPE_addiw_pure (input : AddiwInput) : AddiwOutput := sorry

  lemma execute_ITYPE_addiw_pure_equiv : True := by trivial

end PureSpec
