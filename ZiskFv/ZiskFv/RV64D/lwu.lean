-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `lwu`: load 32-bit word from memory, zero-extended into rd.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure LwuInput where
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    r1_val : BitVec 64
    PC : BitVec 64
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8

  structure LwuOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_LOADWU_pure (input : LwuInput) : LwuOutput := sorry

  lemma execute_LOADWU_pure_equiv : True := by trivial

end PureSpec
