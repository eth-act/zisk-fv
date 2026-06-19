import ZiskFv.Compliance.Wrappers.Remu
import ZiskFv.Channels.StateEffect
import ZiskFv.Bits.PackedBitVec.SignedChunkLift

/-!
# `equiv_REMU` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for REMU. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_REMU`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Remu.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_REMU`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithDiv (Valid_ArithDiv opBus_row_ArithDiv opBus_row_ArithDivSecondary)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Trusted (OP_DIV OP_REM OP_REMU OP_DIV_W OP_DIVU_W OP_REM_W OP_REMU_W)
open ZiskFv.PackedBitVec.SignedChunkLift (toIntZ)

namespace ZiskFv.Equivalence.Remu


theorem equiv_REMU
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_REMU_of_table state remu_input r1 r2 rd bus m r_main v r_a
    pins h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_rs1_value h_rs2_value


end ZiskFv.Equivalence.Remu
