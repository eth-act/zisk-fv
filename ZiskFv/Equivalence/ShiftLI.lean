import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.Execution
import ZiskFv.ZiskCircuit.ShiftLI
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.SailSpec.slliw
import ZiskFv.SailSpec.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Equivalence.WriteValueProofs.BinaryShift
import ZiskFv.Equivalence.WriteValueProofs.SailBridge
import ZiskFv.Equivalence.Bridge.BinaryExtension
import ZiskFv.Equivalence.Promises.ShiftImm

/-!
End-to-end theorem for RV64 SLLIW (`ShiftArchetype`
sibling, W-variant immediate).

Mirrors `Equivalence.Shift` for SLLW, with the Sail instruction
constructor swapped from `.RTYPEW (r2, r1, rd, ropw.SLLW)` to
`.SHIFTIWOP (shamt, r1, rd, sopw.SLLIW)` (no `r2` register read — the
shift amount is an immediate). The Main-AIR compositional lemma is the
`ShiftArchetype` m32=1 instantiation at `OP_SLL_W` (same opcode as
SLLW — the bus shape doesn't distinguish register vs immediate shift
source).

Bus shape (a): register-read (r1) + register-write (rd), same as SLLW
modulo the dropped r2-read.

NOTE: SLLIW's execution bus actually has only **one** source-register
read (r1) versus SLLW's two (r1, r2). The Main AIR row still emits the
same two-entry execution bus (read PC + write nextPC), but the
memory-bus rd-write structure matches SLLW: `e2.ptr = rd, e2.x*` carry
the 64-bit result. The `bus_effect_matches_sail_alu_rrw` lemma is
shape-(a) and takes three memory entries `[e0, e1, e2]` where `e0/e1`
are the source reads (mapped to register-file source addresses) and
`e2` is the destination write. For SLLIW we pass `e0` as an arbitrary
register-read entry at address-space 1 (matches the Main-AIR's
emission of the r1 read; the shamt source slot is populated with the
immediate as a constant, which the memory bus represents as a
second-source no-op read entry).
-/

namespace ZiskFv.Equivalence.ShiftLI

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.ZiskCircuit.ShiftLI

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SLLIW reduces to the pure-function block. Wraps
    `PureSpec.execute_SHIFTIWOP_slliw_pure_equiv`. -/
lemma equiv_SLLIW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slliw_input.r1_val state)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slliw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = let slliw_output := PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input
        (do
          Sail.writeReg Register.nextPC slliw_output.nextPC
          match slliw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIWOP_slliw_pure_equiv
    slliw_input r1 rd h_input_r1 h_input_rd h_input_pc

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    SLLIW equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output directly; that equation is derived
    internally from circuit witnesses via the
    `WriteValueProofs.BinaryShift.h_rd_val_shift_slliw` discharge lemma. -/
theorem equiv_SLLIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (m : Valid_Main C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (promises : ZiskFv.Equivalence.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd exec_row e0 e1 e2)
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op : m.op r_main = ZiskFv.Trusted.OP_SLL_W)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  obtain ⟨h_input_r1, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- Project matches_entry into (op, c_lo, c_hi) sub-facts.
  obtain ⟨h_op_fgl, h_match_clo, h_match_chi⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  have h_op : (v.op r_binary).val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W := by
    rw [← h_op_fgl, h_main_op]; decide
  -- Discharge c-lo/c-hi sum bounds + h_bytes from row-level axioms.
  have hc_lo_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_lo_sum_lt_of_match
      m v r_main r_binary h_match_clo
  have hc_hi_sum_lt :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.hc_hi_sum_lt_of_match
      m v r_main r_binary h_match_chi
  have h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  -- Derive op_is_shift = 1 from the BinaryExtension AIR op_is_shift pin.
  have h_op_is_shift_fact :=
    ZiskFv.Airs.BinaryExtension.binary_extension_op_is_shift_pin v r_binary
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SLL_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift r_binary = 1 :=
    h_op_is_shift_fact.1 (Or.inr (Or.inr (Or.inr (Or.inl h_op_v_eq))))
  -- Discharge h_input_r1_extract + h_shift_pin via SailStateBridge
  -- + transpile_SLLIW + matches_entry projection (m32 = 1; op_is_shift = 1).
  obtain ⟨_, h_m32, _, _, _, _, h_a_lo_t, h_a_hi_t, h_b_lo_t, _h_b_hi_t⟩ :=
    transpile_SLLIW m r_main (regidx_to_fin r1) (regidx_to_fin rd) slliw_input.shamt
      (ZiskFv.Equivalence.Bridge.SailStateBridge.sail_to_rv64 state)
      h_main_active h_main_op
  have h_input_r1_extract :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.packed_a_lo32_eq_of_shift_match_m32_1
      m v r_main r_binary (regidx_to_fin r1) slliw_input.r1_val
      h_m32 h_a_lo_t h_a_hi_t h_input_r1 h_op_is_shift h_match
  have h_shift_pin :=
    ZiskFv.Equivalence.Bridge.BinaryExtension.shift_pin_w_immediate_eq_of_shift_match
      m v r_main r_binary slliw_input.shamt h_b_lo_t h_op_is_shift h_match
  -- Derive 8 e2 byte ranges from `memory_bus_entry_byte_range_perm_sound`.
  obtain ⟨h_e2_0, h_e2_1, h_e2_2, h_e2_3, h_e2_4, h_e2_5, h_e2_6, h_e2_7⟩ :=
    ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e2
  -- Derive the 8 a-byte ranges + 16 c-byte 32-bit ranges from
  -- `binary_extension_columns_in_range` (BinaryExtension AIR's
  -- range-check soundness axiom on the trust ledger). This discharges
  -- the 17 per-byte *promise hypotheses* without any caller obligation.
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, _hb,
          hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
          hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, _, _⟩ :=
    ZiskFv.Airs.BinaryExtension.binary_extension_columns_in_range v r_binary
  have h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary :=
    ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩
  set a4sum : ℕ := (v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
        + (v.free_in_a_2 r_binary).val * 65536
        + (v.free_in_a_3 r_binary).val * 16777216 with h_a4_def
  set shift : ℕ := slliw_input.shamt.toNat with h_shift_def
  have h_r1lo : Sail.BitVec.extractLsb slliw_input.r1_val 31 0
      = BitVec.ofNat 32 a4sum := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, h_input_r1_extract, h_a4_def]
  have h_discharge :=
    ZiskFv.Equivalence.WriteValueProofs.BinaryShift.h_rd_val_shift_slliw
      m v r_main r_binary e2
      (Sail.BitVec.extractLsb slliw_input.r1_val 31 0)
      shift h_op h_bytes h_a_range
      hc0 hc2 hc4 hc6 hc8 hc10 hc12 hc14
      hc1 hc3 hc5 hc7 hc9 hc11 hc13 hc15
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_r1lo
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.Equivalence.WriteValueProofs.SailBridge.sail_slliw_bridge
      slliw_input.r1_val slliw_input.shamt a4sum shift
      (h_input_r1_extract.trans (by rw [h_a4_def]))
      h_shift_def
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_left
            (Sail.BitVec.extractLsb slliw_input.r1_val 31 0) slliw_input.shamt) :=
    h_discharge.trans ((by rw [h_r1lo] : BitVec.signExtend 64
        (BitVec.shiftLeft (Sail.BitVec.extractLsb slliw_input.r1_val 31 0) shift)
      = BitVec.signExtend 64
        (BitVec.shiftLeft (BitVec.ofNat 32 a4sum) shift)).trans h_bridge)
  rw [equiv_SLLIW_sail state slliw_input r1 rd
        h_input_r1 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_SHIFTIWOP_slliw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.ShiftLI
