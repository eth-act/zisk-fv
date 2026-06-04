import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Bits.Execution
import ZiskFv.ZiskCircuit.Addiw
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.addiw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.RTypeWArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.Arith
import ZiskFv.EquivCore.WriteValueProofs.SailBridge
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Addw
import ZiskFv.Airs.Binary.Binary
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 ADDIW. Sibling of
`Equivalence.Addw` for the immediate-source variant.

Mirrors `Equivalence.ShiftLI` for SLLIW's single-reg-plus-imm shape,
and `Equivalence.Addw` for the RTYPEW Sail triple. The Sail
instruction constructor is `instruction.ADDIW (imm, r1, rd)` (no
`r2` — the shift / imm source is encoded in the immediate). Bus
shape (a) — two-entry execution bus + three-entry memory bus
`[source, source, dst]`.

Routing note. ADDIW and ADDW share `OP_ADD_W` + `m32 = 1` at the
operation-bus layer; they differ only in the row-shape provenance bridge's
`b`-lane shape (reg for ADDW, imm for ADDIW).
-/

namespace ZiskFv.EquivCore.Addiw

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Addiw
open ZiskFv.Tactics.RTypeWArchetype


/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDIW
    reduces to `PureSpec.execute_ITYPE_addiw_pure`. Wraps
    `PureSpec.execute_ITYPE_addiw_pure_equiv`. -/
lemma equiv_ADDIW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addiw_input.r1_val state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addiw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = let addiw_output := PureSpec.execute_ITYPE_addiw_pure addiw_input
        (do
          Sail.writeReg Register.nextPC addiw_output.nextPC
          match addiw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_addiw_pure_equiv
    addiw_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- Static-provider variant of `equiv_ADDIW`. The 4 low-byte chain
    hypotheses carry `consumer_byte_match_chain_wf` (table wf_properties).
    Body mirrors `equiv_ADDIW`, routing through `h_rd_val_arith_addiw_of_wf`. -/
lemma equiv_ADDIW_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r_binary : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    (h_byte_0 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) c0 cin0 fl0 pi0)
    (h_byte_1 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) c1 cin1 fl1 pi1)
    (h_byte_2 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) c2 cin2 fl2 pi2)
    (h_byte_3 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) c3 cin3 fl3 pi3)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val = 1)
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648))
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryValidA32 v r_binary % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_input_imm_extract :
      (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
          + (v.free_in_b_2 r_binary).val * 65536
          + (v.free_in_b_3 r_binary).val * 16777216) % 2^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_addiw⟩ := pins
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3,
          h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.e2_byte_ranges_discharge e2
  have ha0 : (v.free_in_a_0 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_0
    rw [← h_a]; exact h_wf.1.1
  have ha1 : (v.free_in_a_1 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_1
    rw [← h_a]; exact h_wf.1.1
  have ha2 : (v.free_in_a_2 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_2
    rw [← h_a]; exact h_wf.1.1
  have ha3 : (v.free_in_a_3 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_3
    rw [← h_a]; exact h_wf.1.1
  have hb0 : (v.free_in_b_0 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_0
    rw [← h_b]; exact h_wf.1.2.1
  have hb1 : (v.free_in_b_1 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_1
    rw [← h_b]; exact h_wf.1.2.1
  have hb2 : (v.free_in_b_2 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_2
    rw [← h_b]; exact h_wf.1.2.1
  have hb3 : (v.free_in_b_3 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_3
    rw [← h_b]; exact h_wf.1.2.1
  set a32sum : ℕ := (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
                  + (v.free_in_a_2 r_binary).val * 65536
                  + (v.free_in_a_3 r_binary).val * 16777216 with h_a32_def
  set b32sum : ℕ := (v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
                  + (v.free_in_b_2 r_binary).val * 65536
                  + (v.free_in_b_3 r_binary).val * 16777216 with h_b32_def
  have h_discharge :=
    ZiskFv.EquivCore.WriteValueProofs.Arith.h_rd_val_arith_addiw_of_wf
      m r_main e2
      (v.free_in_a_0 r_binary) (v.free_in_a_1 r_binary)
      (v.free_in_a_2 r_binary) (v.free_in_a_3 r_binary)
      (v.free_in_b_0 r_binary) (v.free_in_b_1 r_binary)
      (v.free_in_b_2 r_binary) (v.free_in_b_3 r_binary)
      c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 fl0 fl1 fl2 fl3 pi0 pi1 pi2 pi3
      h_byte_0 h_byte_1 h_byte_2 h_byte_3
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_cin0 h_cin1 h_cin2 h_cin3
      h_pi0 h_pi1 h_pi2 h_pi3 h_sext_choice
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      a32sum b32sum h_a32_def h_b32_def
  have h_bridge :=
    ZiskFv.EquivCore.WriteValueProofs.SailBridge.sail_addiw_bridge
      addiw_input.r1_val imm a32sum b32sum
      (h_input_r1_extract.trans (by
        rw [ZiskFv.EquivCore.Addw.binaryValidA32, h_a32_def]))
      (h_input_imm_extract.trans (by rw [h_b32_def]))
  have h_rd_val : U64.toBV #v[byteAt e2 0, byteAt e2 1, byteAt e2 2, byteAt e2 3,
                              byteAt e2 4, byteAt e2 5, byteAt e2 6, byteAt e2 7]
      = execute_ADDIW_pure addiw_input.imm addiw_input.r1_val := by
    rw [h_discharge, h_input_imm, h_bridge]
  rw [equiv_ADDIW_sail state addiw_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_addiw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- Row-native static-provider route for `equiv_ADDIW`. Mirrors
    `equiv_ADDW_of_static_row` with ITYPE promises and caller-routed
    immediate decomposition. -/
lemma equiv_ADDIW_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD_W)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_one : row.mode.mode32 = 1)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD)
    (h_sext_choice :
      ((row.cBytes.free_in_c_4.val = 0 ∧ row.cBytes.free_in_c_5.val = 0
          ∧ row.cBytes.free_in_c_6.val = 0 ∧ row.cBytes.free_in_c_7.val = 0) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 < 2147483648) ∨
      ((row.cBytes.free_in_c_4.val = 255 ∧ row.cBytes.free_in_c_5.val = 255
          ∧ row.cBytes.free_in_c_6.val = 255 ∧ row.cBytes.free_in_c_7.val = 255) ∧
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216 ≥ 2147483648))
    (h_carry_7_zero : row.chain.carry_7 = 0)
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32 row % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (h_input_imm_extract :
      (Sail.BitVec.extractLsb (BitVec.signExtend 64 imm : BitVec 64) 31 0
        : BitVec (31 - 0 + 1)).toNat
      = (((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_0 0).val
          + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_1 0).val * 256
          + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_2 0).val * 65536
          + ((ZiskFv.AirsClean.Binary.validOfRow row).free_in_b_3 0).val * 16777216)
              % 2^32) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_addiw⟩ := pins
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_W_low4_discharge_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core
      h_mode32_one h_b_op
  have h_lane_eqs := h_match_v
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, _, _, h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_lane_eqs
  have h_carry_7_zero_v : v.carry_7 0 = 0 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_carry_7_zero
  have h_match_clo :
      m.c_0 r_main = v.free_in_c_0 0 + v.free_in_c_1 0 * 256
        + v.free_in_c_2 0 * 65536 + v.free_in_c_3 0 * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero_v]
    ring
  have h_match_chi :
      m.c_1 r_main = v.free_in_c_4 0 + v.free_in_c_5 0 * 256
        + v.free_in_c_6 0 * 65536 + v.free_in_c_7 0 * 16777216 := by
    rw [h_c_hi_m]
    ring
  have hc4 : (v.free_in_c_4 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using
      h_facts.2.2.2.2.1.1.2.2.1
  have hc5 : (v.free_in_c_5 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using
      h_facts.2.2.2.2.2.1.1.2.2.1
  have hc6 : (v.free_in_c_6 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using
      h_facts.2.2.2.2.2.2.1.1.2.2.1
  have hc7 : (v.free_in_c_7 0).val < 256 := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.Channels.BinaryTable.BinaryTableMessage.toEntry,
      ZiskFv.Airs.Tables.BinaryTable.range_conditions] using
      h_facts.2.2.2.2.2.2.2.1.2.2.1
  have h_sext_choice_v :
      (((v.free_in_c_4 0).val = 0 ∧ (v.free_in_c_5 0).val = 0
          ∧ (v.free_in_c_6 0).val = 0 ∧ (v.free_in_c_7 0).val = 0) ∧
        (v.free_in_c_0 0).val + (v.free_in_c_1 0).val * 256
          + (v.free_in_c_2 0).val * 65536
          + (v.free_in_c_3 0).val * 16777216 < 2147483648) ∨
      (((v.free_in_c_4 0).val = 255 ∧ (v.free_in_c_5 0).val = 255
          ∧ (v.free_in_c_6 0).val = 255 ∧ (v.free_in_c_7 0).val = 255) ∧
        (v.free_in_c_0 0).val + (v.free_in_c_1 0).val * 256
          + (v.free_in_c_2 0).val * 65536
          + (v.free_in_c_3 0).val * 16777216 ≥ 2147483648) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow] using h_sext_choice
  exact ZiskFv.EquivCore.Addiw.equiv_ADDIW_of_wf
    state addiw_input r1 rd imm m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v 0
    ⟨h_main_active, h_main_op_addiw⟩
    h_match_v
    (v.free_in_c_0 0) (v.free_in_c_1 0) (v.free_in_c_2 0)
    (v.free_in_c_3 0) (v.free_in_c_4 0) (v.free_in_c_5 0)
    (v.free_in_c_6 0) (v.free_in_c_7 0)
    (0 : FGL) (v.carry_0 0) (v.carry_1 0) (v.carry_2 0)
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_0 0))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_1 0))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row
      (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_2 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row
      (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_3 0))
    (2 * v.use_first_byte 0) (0 : FGL) (0 : FGL) (v.mode32 0)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.c0_lt out.c1_lt out.c2_lt out.c3_lt hc4 hc5 hc6 hc7
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_eq
    h_sext_choice_v h_match_clo h_match_chi
    (by
      simpa [v, ZiskFv.EquivCore.Addw.binaryValidA32,
        ZiskFv.EquivCore.Addw.binaryRowA32,
        ZiskFv.AirsClean.Binary.validOfRow] using h_input_r1_extract)
    h_lane_rd h_input_imm_extract

end ZiskFv.EquivCore.Addiw
