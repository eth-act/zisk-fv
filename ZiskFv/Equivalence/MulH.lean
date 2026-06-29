import ZiskFv.Compliance.Wrappers.MulH
import ZiskFv.Channels.StateEffect

/-!
# `equiv_MULH` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for MULH. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_MULH`.

The real Sail↔circuit proof lives at `ZiskFv/EquivCore/MulH.lean`.

## Trust note

No new axioms.  This theorem is NON-VACUOUS: the former `False` defect binder
is replaced by the NARROWED forge-exclusion `h_not_forge` (honest rows satisfy
it). Operand sign facts are derived from the indexed Arith range-table evidence
carried by `arith_table`.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.ArithMul (Valid_ArithMul)
open ZiskFv.Airs.OperationBus (matches_entry opBus_row_Main)
open ZiskFv.Airs.ArithMul (opBus_row_Arith opBus_row_ArithMulSecondary)
open ZiskFv.Trusted (OP_MUL OP_MULH OP_MULU OP_MULUH OP_MULSUH OP_MUL_W)

namespace ZiskFv.Equivalence.MulH


theorem equiv_MULH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (v : Valid_ArithMul FGL FGL) (r_a : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_MULH)
    (h_match_secondary :
      matches_entry (opBus_row_Main m r_main) (opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints : ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val)
    -- NARROWED forge-exclusion (MULH arm): the row is NOT one of the two
    -- exceptional product-sign shapes the shared ArithTable admits for op 181.
    -- Honest rows (`np = na XOR nb`) satisfy it, so this theorem is NON-VACUOUS.
    (h_not_forge :
      ¬ ((v.na r_a = 1 ∧ v.nb r_a = 0 ∧ v.np r_a = 0)
        ∨ (v.na r_a = 0 ∧ v.nb r_a = 1 ∧ v.np r_a = 0)))
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL (r2, r1, rd, { result_part := VectorHalf.High, signed_rs1 := .Signed, signed_rs2 := .Signed }))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_MULH_of_table state mulh_input r1 r2 rd bus m r_main v r_a
    pins h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value h_not_forge

end ZiskFv.Equivalence.MulH
