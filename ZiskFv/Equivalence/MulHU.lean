import ZiskFv.Compliance.Wrappers.MulHU
import ZiskFv.Channels.StateEffect

/-!
# `equiv_MULHU` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for MULHU. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_MULHU`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/MulHU.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_MULHU`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithMul (Valid_ArithMul)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Airs.ArithMul (opBus_row_Arith opBus_row_ArithMulSecondary)
open ZiskFv.Trusted (OP_MUL OP_MULH OP_MULU OP_MULUH OP_MULSUH OP_MUL_W)

namespace ZiskFv.Equivalence.MulHU


theorem equiv_MULHU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULUH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulUnsignedCarryRangeWitness v r_a)
    (h_row_constraints : ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_MULHU_of_table state mulhu_input r1 r2 rd bus m r_main v r_a pins h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges

end ZiskFv.Equivalence.MulHU
