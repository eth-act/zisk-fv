-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `ld`: load 64-bit doubleword from memory.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure LdInput where
    r1 : BitVec 5
    imm : BitVec 12
    rd : BitVec 5
    r1_val : BitVec 64
    PC : BitVec 64
    -- 8 memory bytes for the doubleword
    data0 : BitVec 8
    data1 : BitVec 8
    data2 : BitVec 8
    data3 : BitVec 8
    data4 : BitVec 8
    data5 : BitVec 8
    data6 : BitVec 8
    data7 : BitVec 8

  structure LdOutput where
    nextPC : BitVec 64
    rd : Option (Finset.Icc 1 31 × BitVec 64)

  def execute_LOADD_pure (input : LdInput) : LdOutput := sorry

  lemma execute_LOADD_pure_equiv : True := by trivial

end PureSpec
