import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `StorePromises` — structural bundle for STORE opcodes

Covers SB, SH, SW, SD. 12 structurally-uniform binders. Bus shape
differs from LOAD by which memory bus entry is consumer vs producer:
e1 is consumer/register (as=1), e2 is producer/memory (as=2).

Opcode-specific extras (ptr-match equation, byte-extract equations,
mode pins) stay inline.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted

/-- 12-field structural bundle for SB, SH, SW, SD. -/
structure StorePromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (opcode_assumptions : Prop)
    (pure_nextPC : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg
  opcode_assumptions_ : opcode_assumptions
  exec_len : exec_row.length = 2
  e0_mult : exec_row[0]!.multiplicity = -1
  e1_mult : exec_row[1]!.multiplicity = 1
  nextPC_matches :
    (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
      = pure_nextPC
  m0_mult : e0.multiplicity = -1
  m0_as : e0.as.val = 1
  m1_mult : e1.multiplicity = -1
  m1_as : e1.as.val = 1
  m2_mult : e2.multiplicity = 1
  m2_as : e2.as.val = 2

end ZiskFv.EquivCore.Promises
