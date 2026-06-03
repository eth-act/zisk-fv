import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.Addi
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.EquivCore.Bridge.BinaryAdd
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.addi
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.MemoryBus
import ZiskFv.EquivCore.WriteValueProofs.Arith
import ZiskFv.EquivCore.Promises.IType
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Add
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 ADDI.

Mirrors `Equivalence.Sub` / `Equivalence.And` shape with
`rop.<OP> → iop.ADDI` on the Sail side and `OP_SUB/AND → OP_ADD`
on the circuit side. ADDI shares `OP_ADD` with ADD — the piggyback
is transpiler-internal; the Main-AIR row carries the sign-extended
12-bit immediate through `(b_lo, b_hi)` rather than from `xreg(rs2)`.

**Bus-shape note (inherited from SLLI precedent).** The equivalence
hypotheses still take three memory-bus entries `[e0, e1, e2]` even
though an ITYPE microinstruction reads only one register, to keep
the `bus_effect_matches_sail_alu_rrw` interface uniform for all
register-write ALU ops.
-/

namespace ZiskFv.EquivCore.Addi

open Goldilocks
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.Addi
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Airs.BinaryAdd


/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDI
    reduces to `PureSpec.execute_ITYPE_addi_pure`. Wraps
    `PureSpec.execute_ITYPE_addi_pure_equiv`. -/
lemma equiv_ADDI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = let addi_output := PureSpec.execute_ITYPE_addi_pure addi_input
        (do
          Sail.writeReg Register.nextPC addi_output.nextPC
          match addi_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_addi_pure_equiv
    addi_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64 ADDI equals
    the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows.

    The previous Tier-1 form bundled the BinaryAdd row witness, the
    cross-AIR `matches_entry`, and the per-row Main constraints into
    a single `h_circuit : addi_circuit_holds_with_binaryadd m b
    r_main r_binary` parameter; alongside it the caller supplied the
    BinaryAdd-row-form imm bridge `h_input_imm_circuit`. Both were
    *promise hypotheses* the canonical proof body substituted without
    deriving.

    This refactor follows the AddExemplar / LuiExemplar
    *structural-unpacking* pattern (see
    `trust/structural-unpacking-exceptions.txt`): the caller now
    supplies the universal-row Main constraints
    (`h_main_subset`, `h_main_mode`), the universal-row BinaryAdd
    validity (`h_b_core`), and the Main-form immediate bridge
    (`h_addi_subset` — the constructibility-bundle predicate
    `itype_imm_subset_holds_main`). The proof body internally:

    1. Derives the BinaryAdd row witness `r_binary` and the
       `matches_entry` predicate from `op_bus_perm_sound_BinaryAdd`
       (class #4 — *trust ledger*).
    2. Translates the Main-form imm bridge to BinaryAdd-row form
       via `matches_entry`'s `b`-lane conjuncts under `h_m32 = 0`.
    3. Composes with the existing `WriteValueProofs.Arith` discharge
       lemma.

    Per-opcode metric: +1 binder vs. the prior canonical. Falls under
    the structural-unpacking exception (`trust/structural-unpacking-
    exceptions.txt`) — `(m, b, ∀ r, core_every_row b r)` collapse into
    shared parameters across all BinaryAdd-shape opcodes in
    `Compliance.lean`; `h_addi_subset` is the per-program
    constructibility pin delivered uniformly across ADDI rows.

    Row-explicit variant: takes the BinaryAdd row witness + matches_entry
    directly, bypassing `op_bus_perm_sound_BinaryAdd`. The thin forwarder
    `equiv_ADDI` below derives them via the axiom. -/
lemma equiv_ADDI_with_match
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (b : Valid_BinaryAdd FGL FGL)
    (r_main r_binary : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_addi_mode m r_main)
    (h_b_core : ZiskFv.Airs.BinaryAdd.core_every_row b r_binary)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_binary))
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_a_range : a_chunks_in_range b r_binary)
    (h_b_range : b_chunks_in_range b r_binary)
    (h_c_range : c_chunks_in_range b r_binary)
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main addi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ := bounds
  obtain ⟨h_input_r1, h_input_imm, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  have h_active : m.is_external_op r_main = 1 := h_main_mode.1
  have h_op : m.op r_main = (10 : FGL) := h_main_mode.2.1
  have h_m32 : m.m32 r_main = 0 := h_main_mode.2.2.1
  have h_circuit : ZiskFv.ZiskCircuit.Addi.addi_circuit_holds_with_binaryadd
      m b r_main r_binary :=
    ⟨h_main_subset, h_b_core, h_match, h_main_mode⟩
  have h_input_r1_main :=
    ZiskFv.EquivCore.Bridge.SailStateBridge.addi_input_r1_main_eq_of_read_xreg
      m r_main state (regidx_to_fin r1) addi_input.r1_val
      h_a_lo_t h_a_hi_t h_input_r1
  have h_lane_eqs := h_match
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd]
    at h_lane_eqs
  obtain ⟨_, _, h_a_lo, h_a_hi, h_b_lo, h_b_hi, _, _, _, _, _, _⟩ := h_lane_eqs
  rw [h_m32] at h_a_hi h_b_hi
  simp only [one_sub_zero_mul] at h_a_hi h_b_hi
  have h_a0_val : (m.a_0 r_main).val = (b.a_0 r_binary).val :=
    congrArg Fin.val h_a_lo
  have h_a1_val : (m.a_1 r_main).val = (b.a_1 r_binary).val :=
    congrArg Fin.val h_a_hi
  have h_b0_val : (m.b_0 r_main).val = (b.b_0 r_binary).val :=
    congrArg Fin.val h_b_lo
  have h_b1_val : (m.b_1 r_main).val = (b.b_1 r_binary).val :=
    congrArg Fin.val h_b_hi
  have h_input_r1_circuit : addi_input.r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296) := by
    rw [h_input_r1_main, h_a0_val, h_a1_val]
  have h_input_imm_circuit : BitVec.signExtend 64 addi_input.imm
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296) := by
    have h := h_addi_subset
    simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main] at h
    rw [h, h_b0_val, h_b1_val]
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.Arith.h_rd_val_arith_addi
      m b r_main r_binary e2 addi_input.r1_val addi_input.imm
      h_circuit h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a_range h_b_range h_c_range
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_ADDI_sail state addi_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_addi_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

-- Legacy `equiv_ADDI` (BinaryAdd-arm thin forwarder using
-- op_bus_perm_sound_BinaryAdd) deleted in T4-purge P3.10.

/-- **Binary-arm equiv_ADDI** (T2.2 multi-provider migration).
    Mirrors `equiv_ADD_of_wf` with the ADDI operand bridge and the `r2_val`
    register-read bridge replaced by the immediate constructibility pin
    `h_addi_subset`. -/
lemma equiv_ADDI_of_wf
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL) (r_binary : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main addi_input.imm)
    (c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
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
    (h_byte_4 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) c4 cin4 fl4 pi4)
    (h_byte_5 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) c5 cin5 fl5 pi5)
    (h_byte_6 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) c6 cin6 fl6 pi6)
    (h_byte_7 : ZiskFv.Airs.Binary.consumer_byte_match_chain_wf
      ZiskFv.Airs.Tables.BinaryTable.OP_ADD
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) c7 cin7 fl7 pi7)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1) (h_pi7 : pi7.val = 1)
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_input_r1_circuit : addi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryValidA64 v r_binary)
    (h_input_imm_circuit : BitVec.signExtend 64 addi_input.imm =
      ZiskFv.EquivCore.Add.binaryValidB64 v r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
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
  have ha4 : (v.free_in_a_4 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_4
    rw [← h_a]; exact h_wf.1.1
  have ha5 : (v.free_in_a_5 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_5
    rw [← h_a]; exact h_wf.1.1
  have ha6 : (v.free_in_a_6 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_6
    rw [← h_a]; exact h_wf.1.1
  have ha7 : (v.free_in_a_7 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, h_a, _, _, _, _, _⟩ := h_byte_7
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
  have hb4 : (v.free_in_b_4 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_4
    rw [← h_b]; exact h_wf.1.2.1
  have hb5 : (v.free_in_b_5 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_5
    rw [← h_b]; exact h_wf.1.2.1
  have hb6 : (v.free_in_b_6 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_6
    rw [← h_b]; exact h_wf.1.2.1
  have hb7 : (v.free_in_b_7 r_binary).val < 256 := by
    obtain ⟨_, h_wf, _, _, h_b, _, _, _, _⟩ := h_byte_7
    rw [← h_b]; exact h_wf.1.2.1
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.Arith.h_rd_val_arith_add_of_wf
      m r_main e2 addi_input.r1_val (BitVec.signExtend 64 addi_input.imm)
      (v.free_in_a_0 r_binary) (v.free_in_a_1 r_binary) (v.free_in_a_2 r_binary) (v.free_in_a_3 r_binary)
      (v.free_in_a_4 r_binary) (v.free_in_a_5 r_binary) (v.free_in_a_6 r_binary) (v.free_in_a_7 r_binary)
      (v.free_in_b_0 r_binary) (v.free_in_b_1 r_binary) (v.free_in_b_2 r_binary) (v.free_in_b_3 r_binary)
      (v.free_in_b_4 r_binary) (v.free_in_b_5 r_binary) (v.free_in_b_6 r_binary) (v.free_in_b_7 r_binary)
      c0 c1 c2 c3 c4 c5 c6 c7
      cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
      fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
      pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
      h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
      ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
      h_pi0 h_pi1 h_pi2 h_pi3 h_pi4 h_pi5 h_pi6 h_pi7
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_ADDI_sail state addi_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_addi_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- Row-native static-provider BinaryTable route for `equiv_ADDI`. -/
lemma equiv_ADDI_of_static_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main addi_input.imm)
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_zero : row.mode.mode32 = 0)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_ADD)
    (h_input_r1_row : addi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64 row)
    (h_input_imm_row : BitVec.signExtend 64 addi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64 row)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  let v := ZiskFv.AirsClean.Binary.validOfRow row
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [v, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  have out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      row h_facts ZiskFv.Airs.Tables.BinaryTable.OP_ADD h_core
      h_mode32_zero h_b_op
  have h_carry_7_zero :=
    ZiskFv.EquivCore.Bridge.Binary.carry_7_zero_ADD_of_static_chain
      v 0 out h_core h_core.2.1
  have h_lane_eqs := h_match_v
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_lane_eqs
  obtain ⟨_, _, _, _, _, _, h_c_lo_m, h_c_hi_m, _, _, _, _⟩ := h_lane_eqs
  have h_match_clo :
      m.c_0 r_main = v.free_in_c_0 0 + v.free_in_c_1 0 * 256
        + v.free_in_c_2 0 * 65536 + v.free_in_c_3 0 * 16777216 := by
    rw [h_c_lo_m, h_carry_7_zero]
    ring
  have h_match_chi :
      m.c_1 r_main = v.free_in_c_4 0 + v.free_in_c_5 0 * 256
        + v.free_in_c_6 0 * 65536 + v.free_in_c_7 0 * 16777216 := by
    rw [h_c_hi_m]
    ring
  exact ZiskFv.EquivCore.Addi.equiv_ADDI_of_wf
    state addi_input r1 rd imm m r_main
    ⟨exec_row, e0, e1, e2⟩
    promises
    v 0
    ⟨h_main_active, h_main_op_add⟩
    h_match_v h_addi_subset
    (v.free_in_c_0 0) (v.free_in_c_1 0) (v.free_in_c_2 0)
    (v.free_in_c_3 0) (v.free_in_c_4 0) (v.free_in_c_5 0)
    (v.free_in_c_6 0) (v.free_in_c_7 0)
    (0 : FGL) (v.carry_0 0) (v.carry_1 0) (v.carry_2 0)
    (v.carry_3 0) (v.carry_4 0) (v.carry_5 0) (v.carry_6 0)
    (ZiskFv.AirsClean.Binary.lookupFlags012Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_0 0))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_1 0))
    (ZiskFv.AirsClean.Binary.lookupFlags012Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_2 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_3 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_4 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_5 0))
    (ZiskFv.AirsClean.Binary.lookupFlags3456Row (ZiskFv.AirsClean.Binary.rowAt v 0) (v.carry_6 0))
    (ZiskFv.AirsClean.Binary.lookupFlags7Row (ZiskFv.AirsClean.Binary.rowAt v 0))
    (2 * v.use_first_byte 0) (0 : FGL) (0 : FGL) (v.mode32 0)
    (0 : FGL) (0 : FGL) (0 : FGL) (1 - v.mode32 0)
    out.chain_0 out.chain_1 out.chain_2 out.chain_3
    out.chain_4 out.chain_5 out.chain_6 out.chain_7
    out.c0_lt out.c1_lt out.c2_lt out.c3_lt out.c4_lt out.c5_lt out.c6_lt out.c7_lt
    out.cin0_eq out.cin1_eq out.cin2_eq out.cin3_eq
    out.cin4_eq out.cin5_eq out.cin6_eq out.cin7_eq
    out.pi0_ne out.pi1_ne out.pi2_ne out.pi3_ne
    out.pi4_ne out.pi5_ne out.pi6_ne out.pi7_eq
    h_match_clo h_match_chi
    (by
      simpa [v, ZiskFv.EquivCore.Add.binaryValidA64,
        ZiskFv.EquivCore.Add.binaryRowA64, ZiskFv.AirsClean.Binary.validOfRow]
        using h_input_r1_row)
    (by
      simpa [v, ZiskFv.EquivCore.Add.binaryValidB64,
        ZiskFv.EquivCore.Add.binaryRowB64, ZiskFv.AirsClean.Binary.validOfRow]
        using h_input_imm_row)
    h_lane_rd

/-- **BinaryAdd-arm row-native equiv_ADDI** (T2.2c). Mirror of
    `equiv_ADD_of_binaryadd_row` with ADD → ADDI: takes a concrete Clean
    `BinaryAddRow` + core_every_row at row 0 + matches_entry against
    the Clean row's emission, takes `m.m32 = 0` + `m.set_pc = 0`
    explicitly, and projects to the canonical
    `equiv_ADDI`. -/
lemma equiv_ADDI_of_binaryadd_row
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (row : ZiskFv.AirsClean.BinaryAdd.BinaryAddRow FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
    (_h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryAdd.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.BinaryAdd.core_every_row
      (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_main_subset : add_subset_holds m r_main)
    (h_a_lo_t : m.a_0 r_main =
      ZiskFv.Trusted.lane_lo ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_a_hi_t : m.a_1 r_main =
      ZiskFv.Trusted.lane_hi ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 state).xreg (regidx_to_fin r1)))
    (h_a_range : a_chunks_in_range (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_b_range : b_chunks_in_range (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_c_range : c_chunks_in_range (ZiskFv.AirsClean.BinaryAdd.validOfRow row) 0)
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main addi_input.imm)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op_add⟩ := pins
  let b := ZiskFv.AirsClean.BinaryAdd.validOfRow row
  have h_e2_0 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 0
  have h_e2_1 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 1
  have h_e2_2 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 2
  have h_e2_3 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 3
  have h_e2_4 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 4
  have h_e2_5 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 5
  have h_e2_6 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 6
  have h_e2_7 := ZiskFv.Channels.MemoryBusBytes.byteAt_val_lt_256 e2 7
  have h_match_b :
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b 0) := by
    simpa [b, ZiskFv.AirsClean.BinaryAdd.validOfRow,
      ZiskFv.AirsClean.BinaryAdd.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_BinaryAdd] using _h_match
  exact ZiskFv.EquivCore.Addi.equiv_ADDI_with_match
    state addi_input r1 rd imm m b r_main 0
    ⟨exec_row, e0, e1, e2⟩
    promises h_main_subset
    ⟨h_main_active, h_main_op_add, h_m32, h_set_pc⟩
    h_core h_match_b h_a_lo_t h_a_hi_t h_a_range h_b_range h_c_range
    h_addi_subset h_lane_rd
    ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩

end ZiskFv.EquivCore.Addi
