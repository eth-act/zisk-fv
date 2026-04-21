-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `sraiw`: arithmetic shift-right immediate of low 32 bits.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SraiwInput where
    r1_val : BitVec 64
    shamt : BitVec 5
    rd : Fin 32
    PC : BitVec 64

  structure SraiwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_SHIFTIWOP_sraiw_pure (input : SraiwInput) : SraiwOutput := sorry

  lemma execute_SHIFTIWOP_sraiw_pure_equiv : True := by trivial

end PureSpec
