import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.SailSpec.Auxiliaries

/-!
# `ITypePromises` — structural promise bundle for ALU-ITYPE opcodes

Covers six opcodes that share the "one register read + immediate →
one register write through a 3-entry memory bus + Binary AIR" shape:
ADDI, ANDI, ORI, XORI, SLTI, SLTIU.

Bundles fifteen structurally-uniform binders.

Shifts (SLLI, SRLI, SRAI) are in a different shape (SHIFT) and use
the BinaryExtension AIR, so they get their own bundle.

Per `docs/fv/promise-bundles-design.md`.
-/

namespace ZiskFv.Equivalence.Promises

open ZiskFv.Trusted

/-- Structural promise bundle for ALU-ITYPE opcodes
    (ADDI, ANDI, ORI, XORI, SLTI, SLTIU). -/
structure ITypePromises
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (input_r1_val : BitVec 64) (input_imm : BitVec 12)
    (input_rd : Fin 32) (input_pc : BitVec 64)
    (pure_nextPC : BitVec 64)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL) where
  input_r1_eq : read_xreg (regidx_to_fin r1) state
    = EStateM.Result.ok input_r1_val state
  input_imm_eq : input_imm = imm
  input_rd_eq : input_rd = regidx_to_fin rd
  input_pc_eq : state.regs.get? Register.PC = .some input_pc
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
  m2_as : e2.as.val = 1
  rd_idx : input_rd = Transpiler.wrap_to_regidx e2.ptr

end ZiskFv.Equivalence.Promises
