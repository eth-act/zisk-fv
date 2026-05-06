import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Jal
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.jal
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Equivalence.RdValDerivation.JumpUType

/-!
End-to-end theorem for RV64 JAL. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_JAL`),
* the compositional JAL spec (`ZiskFv.Circuit.Jal.jal_pc_advance`),
* the Sail pure-function equivalence (`PureSpec.execute_JAL_pure_equiv`),

into a canonical theorem:

* `equiv_JAL_metaplan` — the metaplan target shape:
  `execute_instruction (.JAL (imm, rd)) state
    = (bus_effect exec_row mem_row state).2`.

For JAL the operation bus is inactive (`is_external_op = 0`); only
the execution + memory bus entries matter.
-/

namespace ZiskFv.Equivalence.Jal

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Jal

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level JAL theorem.** Given the jump-subset Main
    constraints plus the mode witnesses from `transpile_JAL`, the
    next-pc cell advances by `jmp_offset1 = imm`:
    `next_pc = pc + jmp_offset1`.

    This is the circuit-level companion to `equiv_JAL_sail` below —
    together they form the analogue of `equiv_ADD` + `equiv_ADD_sail`
    from the ADD archetype. Uses the transpile axiom's pinning of
    `jmp_offset1` to relate the field-level offset to the RV64 `imm`. -/
theorem equiv_JAL
    (_rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : jal_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main :=
  jal_pc_advance m r_main next_pc h_circuit

/-- **Closed-form circuit-level JAL theorem.** Eliminates the
    `next_pc : FGL` parameter by deriving it from the extracted
    closed-form `pc_handshake` (Main constraint 20) via
    `pc_handshake_to_next_pc`. The caller supplies instead:

    * the booleans + disjointness + internal-op subset for row `r_main`,
    * the JAL mode witnesses at `r_main`,
    * the extracted handshake at `r_main + 1` (closed form — no
      `next_pc` quantifier),
    * the non-segment-boundary witness `segment_l1 (r_main + 1) = 0`.

    The next-row `pc` cell (`m.pc (r_main + 1)`) plays the role of
    `next_pc` in the conclusion. -/
theorem equiv_JAL_closed
    (_rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (h_flag_bool : flag_boolean m r_main)
    (h_ext_bool : is_external_op_boolean m r_main)
    (h_disjoint : flag_set_pc_disjoint m r_main)
    (h_c0_zero : internal_op0_zeroes_c0 m r_main)
    (h_c1_zero : internal_op0_zeroes_c1 m r_main)
    (h17 : internal_op0_sets_flag m r_main)
    (h_mode : main_row_in_jal_mode m r_main)
    (h_seg : m.segment_l1 (r_main + 1) = 0)
    (h_handshake_next : pc_handshake m (r_main + 1)) :
    m.pc (r_main + 1) = m.pc r_main + m.jmp_offset1 r_main :=
  jal_pc_advance m r_main (m.pc (r_main + 1))
    ⟨⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0_zero, h_c1_zero, h17,
      pc_handshake_to_next_pc m r_main h_seg h_handshake_next⟩,
     h_mode⟩

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 JAL reduces to the pure-function block supplied by
    `PureSpec.execute_JAL_pure`, given source-register readability, PC
    knowledge, and the ZisK `misa[C] = 0` (no compressed extension)
    witness.

    Wraps `PureSpec.execute_JAL_pure_equiv` to expose the Sail chain at
    this module's export surface. -/
theorem equiv_JAL_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = let jal_output := PureSpec.execute_JAL_pure jal_input
        (do
          match jal_output.nextPC with
            | .some nextPC => Sail.writeReg Register.nextPC nextPC
            | .none => pure ()
          match jal_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          if jal_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !jal_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_JAL_pure_equiv jal_input imm rd
    h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 JAL
    equals the state computed by applying `bus_effect` to the circuit's
    execution and memory bus rows.

    Unlike BEQ, JAL *does* populate a memory-bus entry (the rd write via
    `store_pc`); the operation-bus is inactive because
    `is_external_op = 0`. -/
theorem equiv_JAL_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Structural bus hypotheses.
    -- JAL has a single memory-bus write entry (rd ← PC+4 via `store_pc`).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    -- Happy-path hypotheses: no alignment fault under ZisK's RV64IM profile.
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    -- Decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    -- `h_rd_idx` ties the circuit rd-pointer to the Sail rd; `h_rd_val`
    -- ties the 8 byte lanes to the pure-spec written value (`PC + 4`).
    -- JAL's rd dite has a compound condition (bit0/bit1/rd=0), so we go
    -- through the `.rd = _` projection form rather than unfolding
    -- `execute_JAL_pure` directly.
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = jal_input.PC + 4) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  rw [equiv_JAL_sail state jal_input imm rd misa_val
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  -- Discharge `.throws = false`, `.success = true`, `.nextPC = some _` via
  -- the happy-path hypotheses before unfolding the spec.
  simp only [h_nextPC_option, h_not_throws, h_success, Bool.not_true]
  -- From h_not_throws (throws = !bit0_valid = false ⇒ bit0_valid = true)
  -- and h_success (success = bit0_valid && bit1_valid = true ⇒ also bit1_valid = true),
  -- derive each of the two bit-validity facts individually so we can
  -- rewrite the JAL pure spec's compound dite.
  have h_bit0_neg :
      (!BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[0]! == 0#1)
      = false := by
    have h_t : (PureSpec.execute_JAL_pure jal_input).throws = false := h_not_throws
    simp only [PureSpec.execute_JAL_pure] at h_t
    exact h_t
  have h_bit1_neg :
      (!BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[1]! == 0#1)
      = false := by
    have h_s : (PureSpec.execute_JAL_pure jal_input).success = true := h_success
    simp only [PureSpec.execute_JAL_pure] at h_s
    simp_all
  -- Unfold the pure spec and discharge the rd dite.
  simp only [PureSpec.execute_JAL_pure, h_rd_idx, h_bit0_neg, h_bit1_neg, Bool.false_or]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e_rd.ptr = 0
  · simp only [h_rd_zero, decide_true, ↓reduceDIte, Bool.false_eq_true,
               if_false, ite_false, bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, decide_false, ↓reduceDIte, Bool.false_eq_true,
               if_false, ite_false, bind, pure, EStateM.bind, EStateM.pure]
    rw [h_rd_val]

/-- **Tier-1: JAL without `h_rd_val` parameter.**

    Companion to `equiv_JAL_metaplan` that drops the `h_rd_val :`
    OUTPUT-EQ residual parameter. Internally derives the rd-write
    equality `U64.toBV ... = jal_input.PC + 4` via
    `RdValDerivation.JumpUType.h_rd_val_jut_jal`, which composes:

    * `transpile_PC_for_JAL` (S1) — Sail-PC ↔ Main-pc-column bridge,
    * `jal_store_value_lo_bv` / `_hi_bv` (S3) — bus-emission BitVec
      bridges,
    * `store_pc_lanes_match_{lo,hi}_of_bus_emission` (S4, callers
      supply via the `h_lane_lo` / `h_lane_hi` LANE-MATCH parameters),
    * `WidePCNoWrap.fgl_pc_plus_4_lo` / `_hi` (S2) — wide-PC no-wrap
      arithmetic.

    The new parameters all live in {CIRCUIT-CONSTRAINT, LANE-MATCH,
    RANGE, TRANSPILE-PIN}. NO OUTPUT-EQ parameters survive. -/
theorem equiv_JAL_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Tier-1 discharge parameters (replace h_rd_val).
    (h_circuit : ZiskFv.Circuit.Jal.jal_circuit_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_lane_lo : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo m r_main e_rd)
    (h_lane_hi : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi m r_main e_rd)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296)
    (h_e_rd_0 : e_rd.x0.val < 256) (h_e_rd_1 : e_rd.x1.val < 256)
    (h_e_rd_2 : e_rd.x2.val < 256) (h_e_rd_3 : e_rd.x3.val < 256)
    (h_e_rd_4 : e_rd.x4.val < 256) (h_e_rd_5 : e_rd.x5.val < 256)
    (h_e_rd_6 : e_rd.x6.val < 256) (h_e_rd_7 : e_rd.x7.val < 256) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.JumpUType.h_rd_val_jut_jal
      jal_input.PC m r_main next_pc e_rd
      h_circuit h_jmp2 h_lane_lo h_lane_hi
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
      h_e_rd_0 h_e_rd_1 h_e_rd_2 h_e_rd_3
      h_e_rd_4 h_e_rd_5 h_e_rd_6 h_e_rd_7
  exact equiv_JAL_metaplan state jal_input imm rd misa_val exec_row e_rd
    nextPC_val h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as
    h_not_throws h_success h_nextPC_option h_rd_idx h_rd_val

/-- **Bus-driven companion for JAL.** Drops `h_input_pc` and
    `h_input_rd` in favor of `h_bus : (bus_effect exec_row [e_rd] state).1`
    plus match hypotheses `h_pc` and `h_rd_ptr`. Uses
    `chip_bus_hyps_jump_rrw` + `readReg_of_readReg_succ`.

    `h_input_imm`, `h_input_misa`, `h_misa_c` stay as parameters —
    they live in different shapes than chip_bus_hyps provides (immediate
    value, privileged-register state, misa-bit witness). -/
theorem equiv_JAL_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : jal_input.imm = imm)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    -- Bus precondition + ptr/value match (replaces h_input_pc, h_input_rd).
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_pc : jal_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = jal_input.PC + 4) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_jump_rrw
    state exec_row e_rd
    h_exec_len h_e0_mult h_e1_mult h_rd_mult h_rd_as h_bus
  have h_input_rd : jal_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some jal_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_JAL_metaplan state jal_input imm rd misa_val exec_row e_rd
    nextPC_val h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as
    h_not_throws h_success h_nextPC_option h_rd_idx h_rd_val

/-- Constructor: build a `PureSpec.JalInput` from bus + imm. -/
def JalInput_of_bus
    (e_rd : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 21) : PureSpec.JalInput :=
  { imm := imm
    rd := Transpiler.wrap_to_regidx e_rd.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for JAL.** Bus-derived input form: drops
    `h_input_imm`, `h_pc`, `h_rd_idx` to `rfl`. -/
theorem equiv_JAL_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_not_throws : (PureSpec.execute_JAL_pure (JalInput_of_bus e_rd exec_row imm)).throws = false)
    (h_success : (PureSpec.execute_JAL_pure (JalInput_of_bus e_rd exec_row imm)).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure (JalInput_of_bus e_rd exec_row imm)).nextPC = .some nextPC_val)
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = (JalInput_of_bus e_rd exec_row imm).PC + 4) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  exact equiv_JAL_metaplan_from_bus state
    (JalInput_of_bus e_rd exec_row imm) imm rd misa_val
    exec_row e_rd nextPC_val
    rfl h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_not_throws h_success h_nextPC_option
    h_bus rfl h_rd_ptr rfl h_rd_val

/-! ## Misaligned-target companions

JAL is unconditional (no taken/not-taken case-split), so the misaligned cases
fire purely on the bits of `PC + sext imm`. Pure-spec encoding:
* `bit0_valid := (...[0]! == 0#1)`, `bit1_valid := (...[1]! == 0#1)`.
* `success := bit0_valid && bit1_valid`, `throws := !bit0_valid`.
* `rd := if !bit0_valid || !bit1_valid || rd = 0 then .none else ...`,
  so on either misaligned case the rd write is suppressed.

Misaligned-bit-1 case (bit0=0, bit1=1): throws=false, success=false,
nextPC = .some (PC + 4) → Sail emits `Memory_Exception` (E_Fetch_Addr_Align).
Misaligned-bit-0 case (bit0=1): throws=true → Sail throws Assertion. -/

/-- **Misaligned-target companion (bit-1 case): Sail-side reduction.**
    Mirrors `RV64D/jal.lean` lines 125-132 lifted to the equivalence
    surface. `rd` write is suppressed by `!bit1_valid` triggering the
    `.none` arm of the dite. -/
theorem equiv_JAL_metaplan_misaligned
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_bit0_aligned :
      BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[0] = 0#1)
    (h_bit1_misaligned :
      BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[1] = 1#1) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = EStateM.Result.ok
          (ExecutionResult.Memory_Exception
            ((virtaddr.Virtaddr (jal_input.PC + BitVec.signExtend 64 jal_input.imm)),
             (ExceptionType.E_Fetch_Addr_Align ())))
          (write_reg_state state Register.nextPC (jal_input.PC + 4#64)) := by
  rw [equiv_JAL_sail state jal_input imm rd misa_val
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c]
  simp [PureSpec.execute_JAL_pure, h_bit0_aligned, h_bit1_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure, write_reg_state]

/-- **Misaligned-target companion (bit-0 case): Sail-side reduction.**
    Mirrors `RV64D/jal.lean` lines 173-176. `throws = !bit0_valid` is
    true, so Sail emits an Assertion error. -/
theorem equiv_JAL_metaplan_misaligned_bit0
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_bit0_misaligned :
      BitVec.ofBool (jal_input.PC + BitVec.signExtend 64 jal_input.imm)[0] = 1#1) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = EStateM.Result.error
          (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          (write_reg_state state Register.nextPC (jal_input.PC + 4#64)) := by
  rw [equiv_JAL_sail state jal_input imm rd misa_val
        h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c]
  simp [PureSpec.execute_JAL_pure, h_bit0_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind,
        EStateM.bind, write_reg_state]

end ZiskFv.Equivalence.Jal
