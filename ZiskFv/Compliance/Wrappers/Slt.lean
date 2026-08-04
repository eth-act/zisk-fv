import Mathlib

import ZiskFv.EquivCore.Slt
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_SLT` Compliance wrapper — Binary LT-shape (signed compare)

Canonical wrapper delegates to the Clean/static provider core. Trust footprint is tracked by the regenerated caller-burden and axiom-closure ledgers.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


lemma equiv_SLT
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slt_input : PureSpec.SltInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (p : ZiskFv.AirsClean.BinaryFamily.StaticBinaryProvider)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage p.rowInput) 1))
    (h_input_r1_row : slt_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64 p.rowInput)
    (h_input_r2_row : slt_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64 p.rowInput)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state slt_input.r1_val slt_input.r2_val slt_input.rd slt_input.PC
        (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_row_spec, h_core, h_spec_facts, h_facts⟩ := p.facts
  obtain ⟨h_main_active, h_main_op_slt⟩ := pins
  have h_emit : p.rowInput.chain.b_op + 16 * p.rowInput.mode.mode32 =
      (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [matches_entry, opBus_row_Main] at h_match_op
    have h_op_match :
        m.op r_main = p.rowInput.chain.b_op + 16 * p.rowInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using
      h_main_op_slt
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      p.rowInput h_spec_facts ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  exact ZiskFv.EquivCore.Slt.equiv_SLT_of_static_row
    state slt_input r1 r2 rd m p.rowInput r_main bus promises
    ⟨h_main_active, h_main_op_slt⟩
    h_match h_core h_facts h_row_m32 h_bop
    h_input_r1_row h_input_r2_row h_lane_rd

end ZiskFv.Compliance
