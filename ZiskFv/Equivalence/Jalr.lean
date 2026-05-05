import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Jalr
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.jalr
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Equivalence.RdValDerivation.JumpUType

/-!
End-to-end theorem for RV64 JALR (Phase 2.5 D4 archetype-macro
validation). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_JALR`),
* the compositional JALR spec (`ZiskFv.Circuit.Jalr.jalr_pc_advance`),
* the Sail pure-function equivalence
  (`PureSpec.execute_JALR_pure_equiv`, closed via the trusted
  `execute_JALR_pure_equiv_axiom` at `ZiskFv/RV64D/jalr.lean:67` —
  see `docs/fv/trusted-base.md` for the closure path),

into a metaplan-shaped theorem:

* `equiv_JALR_metaplan` — the metaplan target shape:
  `execute_instruction (.JALR (imm, rs1, rd)) state
    = (bus_effect exec_row mem_row state).2`.

Like JAL's metaplan (Phase 2.5 D3 shape (c)), the JALR metaplan
theorem is **not** parameterized on `h_bus_execute_matches_sail` — the
bus-matching hypothesis is discharged internally via
`bus_effect_matches_sail_jump_rrw`, which handles any "two-exec-entry
+ one-rd-write-mem-entry" shape. JALR emits exactly that shape under
the archetype-validation contract in `transpile_JALR`
(internal-copyb, `store_pc = 1`, no operation-bus hop).
-/

namespace ZiskFv.Equivalence.Jalr

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Jalr

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level JALR theorem.** Given the JALR constraint subset
    plus the mode witnesses from `transpile_JALR`, the next-pc cell
    advances to `b_0 + jmp_offset1 = rs1_lo + imm12`.

    This is the circuit-level companion to `equiv_JALR_sail` below —
    together they form the analogue of `equiv_JAL` + `equiv_JAL_sail`
    from the JAL archetype. Uses the transpile axiom's pinning of
    `jmp_offset1` to relate the field-level offset to the RV64 `imm12`
    and `b_0` to `rs1_lo`. -/
theorem equiv_JALR
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : jalr_circuit_holds m r_main next_pc) :
    next_pc = m.b_0 r_main + m.jmp_offset1 r_main :=
  jalr_pc_advance m r_main next_pc h_circuit

/-- **Closed-form circuit-level JALR theorem.** Phase 2.5 D2 eliminated
    the `next_pc : FGL` parameter by deriving it from the extracted
    closed-form `pc_handshake` (Main constraint 20) via
    `pc_handshake_to_next_pc`. The caller supplies instead:

    * the booleans + disjointness + internal-op-1 subset for row `r_main`,
    * the JALR mode witnesses at `r_main`,
    * the extracted handshake at `r_main + 1` (closed form — no
      `next_pc` quantifier),
    * the non-segment-boundary witness `segment_l1 (r_main + 1) = 0`.

    The next-row `pc` cell (`m.pc (r_main + 1)`) plays the role of
    `next_pc` in the conclusion. -/
theorem equiv_JALR_closed
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (h_flag_bool : flag_boolean m r_main)
    (h_ext_bool : is_external_op_boolean m r_main)
    (h_disjoint : flag_set_pc_disjoint m r_main)
    (h_c0_copy : internal_op1_copies_b0 m r_main)
    (h_c1_copy : internal_op1_copies_b1 m r_main)
    (h18 : internal_op1_clears_flag m r_main)
    (h_mode : main_row_in_jalr_mode m r_main)
    (h_seg : m.segment_l1 (r_main + 1) = 0)
    (h_handshake_next : pc_handshake m (r_main + 1)) :
    m.pc (r_main + 1) = m.b_0 r_main + m.jmp_offset1 r_main :=
  jalr_pc_advance m r_main (m.pc (r_main + 1))
    ⟨⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0_copy, h_c1_copy, h18,
      pc_handshake_to_next_pc m r_main h_seg h_handshake_next⟩,
     h_mode⟩

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 JALR reduces to the pure-function block supplied by
    `PureSpec.execute_JALR_pure`, given source-register readability
    (rs1), PC knowledge, misa, and ZisK-level privilege/PMA witnesses.

    Wraps `PureSpec.execute_JALR_pure_equiv`, which is closed via the
    trusted `execute_JALR_pure_equiv_axiom` (see `trusted-base.md`).
    The metaplan theorem below composes this with the shape-(c)
    bus-matching lemma. -/
theorem equiv_JALR_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = let jalr_output := PureSpec.execute_JALR_pure jalr_input
        (do
          match jalr_output.nextPC with
            | .some nextPC => Sail.writeReg Register.nextPC nextPC
            | .none => pure ()
          match jalr_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          if !jalr_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (0xFFFFFFFFFFFFFFFE &&& (jalr_input.rs1_val +
                  BitVec.signExtend 64 jalr_input.imm))),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_JALR_pure_equiv jalr_input imm rs1 rd
    h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
    h_cur_privilege h_mseccfg

/-- **Metaplan theorem.** The shape the original metaplan targets for
    RV64 JALR: Sail's `execute_instruction` on an RV64 JALR equals the
    state computed by applying `bus_effect` to the circuit's execution
    and memory bus rows.

    Composes `equiv_JALR_sail` with the shape-(c) bus-matching lemma
    `bus_effect_matches_sail_jump_rrw` (Phase 2.5 D3). Unlike JAL, JALR
    does **not** raise `Assertion` on a misaligned target (its jump
    argument is pre-masked), so the `throws = false` path is trivially
    inhabited — no `h_not_throws` hypothesis is needed.

    **Hypotheses.**
    * Sail side (from `equiv_JALR_sail`): register readability for rs1
      (`h_input_rs1`), PC (`h_input_pc`), misa (`h_input_misa`), and
      privilege/mseccfg witnesses.
    * Bus side (structural, Phase-4-derivable): exec_row has two
      entries (pc-read + nextPC-write) with the appropriate
      multiplicities; `e_rd` is the single register-write entry for rd.
    * Happy-path witness: `h_success` (no JALR alignment fault).
    * `h_nextPC_option` / `h_rd_match`: relate the Sail pure-spec's
      rd/nextPC outputs to the bus-emitted values (shape-(c) closes
      these assuming a PIL bus-emission spec). -/
theorem equiv_JALR_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    -- Phase 2.5 D3: shape-(c) structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    -- Happy-path hypothesis: no alignment fault (ZisK enforces via
    -- the JALR_MASK operand in the transpiler).
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    -- JALR's rd dite has a compound condition (bit1/rd=0), so we bridge
    -- the bit-validity disjunct via the happy-path `h_success` hypothesis.
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = jalr_input.PC + 4) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  rw [equiv_JALR_sail state jalr_input imm rs1 rd misa_val mseccfg
        h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
        h_cur_privilege h_mseccfg]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  simp only [h_nextPC_option, h_success, Bool.not_true]
  -- From h_success (success = bit1_valid = true), derive !bit1_valid = false.
  have h_bit1_neg :
      (!BitVec.ofBool (jalr_input.rs1_val + BitVec.signExtend 64 jalr_input.imm)[1]! == 0#1)
      = false := by
    have h_s : (PureSpec.execute_JALR_pure jalr_input).success = true := h_success
    simp only [PureSpec.execute_JALR_pure] at h_s
    simp_all
  -- Unfold the pure spec and discharge the rd dite.
  simp only [PureSpec.execute_JALR_pure, h_rd_idx, h_bit1_neg]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e_rd.ptr = 0
  · simp only [h_rd_zero, decide_true, Bool.false_or, ↓reduceDIte,
               Bool.false_eq_true, if_false, ite_false,
               bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, decide_false, Bool.or_false, ↓reduceDIte,
               Bool.false_eq_true, if_false, ite_false,
               bind, pure, EStateM.bind, EStateM.pure]
    rw [h_rd_val]

/-- **Tier-1 metaplan: JALR without `h_rd_val` parameter** (finishing5 S5+S6).

    Companion to `equiv_JALR_metaplan` that drops the `h_rd_val :`
    OUTPUT-EQ residual parameter. Internally derives the rd-write
    equality via `RdValDerivation.JumpUType.h_rd_val_jut_jalr`. Same
    Tier-1 toolkit composition as the JAL companion; the only
    difference is the underlying circuit-hypothesis predicate
    (`jalr_circuit_holds` instead of `jal_circuit_holds`).

    All parameter classes: {CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE,
    TRANSPILE-PIN}. NO OUTPUT-EQ parameters survive. -/
theorem equiv_JALR_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Tier-1 discharge parameters (replace h_rd_val).
    (h_circuit : ZiskFv.Circuit.Jalr.jalr_circuit_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_lane_lo : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo m r_main e_rd)
    (h_lane_hi : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi m r_main e_rd)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296)
    (h_e_rd_0 : e_rd.x0.val < 256) (h_e_rd_1 : e_rd.x1.val < 256)
    (h_e_rd_2 : e_rd.x2.val < 256) (h_e_rd_3 : e_rd.x3.val < 256)
    (h_e_rd_4 : e_rd.x4.val < 256) (h_e_rd_5 : e_rd.x5.val < 256)
    (h_e_rd_6 : e_rd.x6.val < 256) (h_e_rd_7 : e_rd.x7.val < 256) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.JumpUType.h_rd_val_jut_jalr
      jalr_input.PC m r_main next_pc e_rd
      h_circuit h_jmp2 h_lane_lo h_lane_hi
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
      h_e_rd_0 h_e_rd_1 h_e_rd_2 h_e_rd_3
      h_e_rd_4 h_e_rd_5 h_e_rd_6 h_e_rd_7
  exact equiv_JALR_metaplan state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd nextPC_val
    h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
    h_cur_privilege h_mseccfg
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_success h_nextPC_option h_rd_idx h_rd_val

/-- **Phase 5 V12 companion for JALR.** Drops `h_input_pc` and
    `h_input_rd` via `chip_bus_hyps_jump_rrw` + `readReg_of_readReg_succ`.
    `h_input_rs1` stays (rs1 read is routed via operation bus for JALR,
    not the memory bus). Other stateful hyps (misa, cur_privilege,
    mseccfg) stay as parameters — privileged-register reads are
    orthogonal to the memory-bus shape. -/
theorem equiv_JALR_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    -- Phase 5 V12: bus precondition + ptr/value match (replaces h_input_pc, h_input_rd).
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_pc : jalr_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = jalr_input.PC + 4) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_jump_rrw
    state exec_row e_rd
    h_exec_len h_e0_mult h_e1_mult h_rd_mult h_rd_as h_bus
  have h_input_rd : jalr_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_JALR_metaplan state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd nextPC_val
    h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
    h_cur_privilege h_mseccfg
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_success h_nextPC_option h_rd_idx h_rd_val

/-- Constructor: build a `PureSpec.JalrInput` from bus + imm + rs1_val.
    rs1 read goes via the operation bus (not memory bus), so rs1_val
    stays as a free parameter. -/
def JalrInput_of_bus
    (e_rd : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 12) (rs1_val : BitVec 64) : PureSpec.JalrInput :=
  { imm := imm
    rs1_val := rs1_val
    rd := Transpiler.wrap_to_regidx e_rd.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for JALR.** Bus-derived input form: drops
    `h_input_imm`, `h_pc`, `h_rd_idx` to `rfl` via `JalrInput_of_bus`.
    `h_input_rs1` stays (rs1 routed via op bus); other privileged-state
    hyps stay. -/
theorem equiv_JALR_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (rs1_val : BitVec 64)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok rs1_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_success :
      (PureSpec.execute_JALR_pure (JalrInput_of_bus e_rd exec_row imm rs1_val)).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure (JalrInput_of_bus e_rd exec_row imm rs1_val)).nextPC = .some nextPC_val)
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = (JalrInput_of_bus e_rd exec_row imm rs1_val).PC + 4) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  exact equiv_JALR_metaplan_from_bus state
    (JalrInput_of_bus e_rd exec_row imm rs1_val)
    imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val
    rfl h_input_rs1 h_input_misa h_misa_c h_cur_privilege h_mseccfg
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_success h_nextPC_option
    h_bus rfl h_rd_ptr rfl h_rd_val

/-- **Track Q POC for JALR.** Operation-bus companion to
    `equiv_JALR_metaplan_from_bus`: drops the scenario-binding
    `h_input_rs1` parameter in favour of an op-bus precondition.

    JALR has a single source register (rs1), pinned by `transpile_JALR`
    onto the Main row's `b` lanes (`m.b_0 = lane_lo (xreg rs1)`,
    `m.b_1 = lane_hi (xreg rs1)`). The op-bus companion therefore reads
    rs1 from the entry's `b`-lane fields via `chip_op_bus_hyps_jalr`,
    which delegates to the branch-shape lemma with `rs1` supplied as
    both bus-bound `r1`/`r2` (the `a`-side equality is discarded).

    The user supplies a witness `h_b_match` that the bus's
    `lanes_to_bv64`-reconstructed b-lanes equal `jalr_input.rs1_val`.

    All other privileged-state hypotheses (misa, cur_privilege, mseccfg)
    pass through unchanged — they are orthogonal to the bus shape. -/
theorem equiv_JALR_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (op_entry : OperationBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_input_imm : jalr_input.imm = imm)
    -- Op-bus precondition (replaces h_input_rs1).
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin rs1) (regidx_to_fin rs1)).1)
    (h_b_match :
      jalr_input.rs1_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_bus : (bus_effect exec_row [e_rd] state).1)
    (h_pc : jalr_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    (h_rd_val :
      U64.toBV #v[e_rd.x0, e_rd.x1, e_rd.x2, e_rd.x3,
                  e_rd.x4, e_rd.x5, e_rd.x6, e_rd.x7]
      = jalr_input.PC + 4) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- Extract the rs1 read from the op-bus precondition (b-lanes).
  have h_rs1_read := ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_jalr
    state op_entry (regidx_to_fin rs1) h_op_mult h_op_bus
  have h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state := by
    rw [h_b_match]; exact h_rs1_read
  exact equiv_JALR_metaplan_from_bus state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd nextPC_val
    h_input_imm h_input_rs1 h_input_misa h_misa_c h_cur_privilege h_mseccfg
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_success h_nextPC_option
    h_bus h_pc h_rd_ptr h_rd_idx h_rd_val

/-! ## Phase 6 Track T fan-out: misaligned-target companion

JALR fan-out of the BLT misaligned-target POC (commit 9345092). JALR
differs from JAL at the alignment-check boundary: its jump argument
is pre-masked via `Sail.BitVec.update target 0 0#1`, which clears
bit-0 silently. Hence:

* Pure-spec output has only `success` — no `throws` field (jalr.lean:13-19).
* Bit-0 misaligned case **never fires** (cleared by the mask before the
  alignment check). No `_bit0` companion.
* Bit-1 misaligned case → `success = false` → Sail emits
  `Memory_Exception (Virtaddr (mask &&& (rs1_val + sext imm)),
  E_Fetch_Addr_Align)`.

The mask in the Memory_Exception's virtaddr is `0xFFFFFFFFFFFFFFFE`,
which equals `Sail.BitVec.update (rs1_val + sext imm) 0 0#1` (clearing
bit-0). The pure-spec uses the explicit `&&&` form, while the underlying
Sail uses the `update` form; both reduce to the same value, but the
pure-spec block from `equiv_JALR_sail` already exposes the `&&&` form. -/

/-- **Misaligned-target companion (bit-1 case): Sail-side reduction.**
    JALR has only one misaligned case (bit-0 is silently cleared by the
    target mask), so no `_bit0` sibling. -/
theorem equiv_JALR_metaplan_misaligned
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_bit1_misaligned :
      BitVec.ofBool (jalr_input.rs1_val + BitVec.signExtend 64 jalr_input.imm)[1] = 1#1) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = EStateM.Result.ok
          (ExecutionResult.Memory_Exception
            ((virtaddr.Virtaddr
              (0xFFFFFFFFFFFFFFFE &&&
                (jalr_input.rs1_val + BitVec.signExtend 64 jalr_input.imm))),
             (ExceptionType.E_Fetch_Addr_Align ())))
          (write_reg_state state Register.nextPC (jalr_input.PC + 4#64)) := by
  rw [equiv_JALR_sail state jalr_input imm rs1 rd misa_val mseccfg
        h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
        h_cur_privilege h_mseccfg]
  simp [PureSpec.execute_JALR_pure, h_bit1_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure, write_reg_state]

end ZiskFv.Equivalence.Jalr
