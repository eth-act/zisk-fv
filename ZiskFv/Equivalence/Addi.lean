import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Addi
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Equivalence.Bridge.BinaryAdd
import ZiskFv.Equivalence.Bridge.SailStateBridge
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.addi
import ZiskFv.Sail.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.MemoryBus
import ZiskFv.Equivalence.RdValDerivation.Arith

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

namespace ZiskFv.Equivalence.Addi

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Addi
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype
open ZiskFv.Airs.BinaryAdd

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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

/-- **Canonical equivalence (Step 4.2r3.I — structural-unpacking
    refactor).** Sail's `execute_instruction` on an RV64 ADDI equals
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
    3. Composes with the existing `RdValDerivation.Arith` discharge
       lemma.

    Per-opcode metric: +1 binder vs. the prior canonical. Falls under
    the structural-unpacking exception (`trust/structural-unpacking-
    exceptions.txt`) — `(m, b, ∀ r, core_every_row b r)` collapse into
    shared parameters across all BinaryAdd-shape opcodes in
    `Compliance.lean`; `h_addi_subset` is the per-program
    constructibility pin delivered uniformly across ADDI rows. -/
theorem equiv_ADDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Sail-state input bridges
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC)
    -- Bus-protocol structural hypotheses
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : addi_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_main_subset : add_subset_holds m r_main)
    (h_main_mode : main_row_in_addi_mode m r_main)
    (h_b_core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row b r)
    (h_addi_subset :
      ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
        m r_main addi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Project the four mode-pin fields of `main_row_in_addi_mode`.
  have h_active : m.is_external_op r_main = 1 := h_main_mode.1
  have h_op : m.op r_main = (10 : FGL) := h_main_mode.2.1
  have h_m32 : m.m32 r_main = 0 := h_main_mode.2.2.1
  -- Step 1: derive the BinaryAdd row witness via op-bus permutation
  -- soundness (class #4, *trust ledger*).
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_BinaryAdd m b r_main h_active h_op
  -- Step 2: reconstruct the Tier-1 `addi_circuit_holds_with_binaryadd`
  -- bundle from the structural-unpacking parameters.
  have h_circuit : ZiskFv.Circuit.Addi.addi_circuit_holds_with_binaryadd
      m b r_main r_binary :=
    ⟨h_main_subset, h_b_core r_binary, h_match, h_main_mode⟩
  -- Step 3: chunk-range facts via `binary_add_columns_in_range` (no
  -- caller hypothesis needed).
  obtain ⟨h_a_range, h_b_range, h_c_range⟩ :=
    ZiskFv.Equivalence.Bridge.BinaryAdd.chunk_ranges_at_holds b r_binary
  -- Step 4: Main-form input-r1 bridge via SailStateBridge.
  have h_input_r1_main :=
    ZiskFv.Equivalence.Bridge.SailStateBridge.addi_input_r1_main_eq_of_read_xreg
      m r_main state (regidx_to_fin r1) (regidx_to_fin rd)
      addi_input.r1_val h_active h_op h_input_r1
  -- Step 5: project matches_entry to translate Main lanes → BinaryAdd
  -- lanes.
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
  -- Step 6: translate the Main-form `h_addi_subset` (imm-bridge) to
  -- BinaryAdd-row form.
  have h_input_imm_circuit : BitVec.signExtend 64 addi_input.imm
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296) := by
    have h := h_addi_subset
    simp only [ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main] at h
    rw [h, h_b0_val, h_b1_val]
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.Arith.h_rd_val_arith_addi
      m b r_main r_binary e2 addi_input.r1_val addi_input.imm
      h_circuit h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_a_range h_b_range h_c_range
      h_input_r1_circuit h_input_imm_circuit
  rw [equiv_ADDI_sail state addi_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_ITYPE_addi_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

end ZiskFv.Equivalence.Addi
