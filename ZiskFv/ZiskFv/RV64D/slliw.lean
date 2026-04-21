-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `slliw`: shift-left immediate of low 32 bits.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SlliwInput where
    r1_val : BitVec 64
    shamt : BitVec 5
    rd : Fin 32
    PC : BitVec 64

  structure SlliwOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_SHIFTIWOP_slliw_pure (input : SlliwInput) : SlliwOutput := sorry

  lemma execute_SHIFTIWOP_slliw_pure_equiv : True := by trivial

end PureSpec
