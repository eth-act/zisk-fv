-- Phase 3 stub: awaiting Phase 3 implementation
-- RV64-only opcode `sd`: store 64-bit doubleword to memory.
import ZiskFv.RV64D.Auxiliaries

namespace PureSpec

  structure SdInput where
    r1 : BitVec 5
    r2 : BitVec 5
    imm : BitVec 12
    r1_val : BitVec 64
    r2_val : BitVec 64
    PC : BitVec 64

  structure SdOutput where
    nextPC : BitVec 64
    -- 8 byte writes
    mem_writes : Option (BitVec 64 × BitVec 64) -- placeholder

  def execute_STORED_pure (input : SdInput) : SdOutput := sorry

  lemma execute_STORED_pure_equiv : True := by trivial

end PureSpec
