import ZiskFv.Compliance.Wrappers.Remuw
import ZiskFv.Channels.StateEffect
import ZiskFv.Channels.MemoryBusBytes

/-!
# `equiv_REMUW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for REMUW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_REMUW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Remuw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_REMUW`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithDiv (Valid_ArithDiv opBus_row_ArithDiv opBus_row_ArithDivSecondary)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Trusted (OP_DIV OP_REM OP_REMU OP_DIV_W OP_DIVU_W OP_REM_W OP_REMU_W)
open ZiskFv.PackedBitVec.SignedChunkLift (toIntZ)
open ZiskFv.Channels.MemoryBusBytes (byteAt)

namespace ZiskFv.Equivalence.Remuw


theorem equiv_REMUW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU_W)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0 ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255 ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536)
    (h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_REMUW state remuw_input r1 r2 rd bus m r_main v r_a pins h_match_secondary promises h_row_constraints h_sext_choice h_rs1_value h_rs2_value h_op2_ne

end ZiskFv.Equivalence.Remuw
