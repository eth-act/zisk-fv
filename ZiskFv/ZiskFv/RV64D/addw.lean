-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `addw`: 32-bit add of low halves, sign-extended into rd.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure AddwInput where
    -- operands
    r1_val : BitVec 64
    r2_val : BitVec 64
    rd : Fin 32
    -- registers
    PC : BitVec 64

  structure AddwOutput where
    -- registers
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  /-- Pure spec for `addw`: add the lower 32 bits of `r1` and `r2`, sign-extend
      to 64 bits, write to `rd`. -/
  def execute_RTYPE_addw_pure (input : AddwInput) : AddwOutput := sorry

  lemma execute_RTYPE_addw_pure_equiv : True := by trivial

end PureSpec
