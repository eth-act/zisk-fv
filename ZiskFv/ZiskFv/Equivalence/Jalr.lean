import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Jalr
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.jalr
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses

/-!
End-to-end theorem for RV64 JALR (Phase 2.5 D4 archetype-macro
validation). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_JALR`),
* the compositional JALR spec (`ZiskFv.Spec.Jalr.jalr_pc_advance`),
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
open ZiskFv.Spec.Jalr

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

end ZiskFv.Equivalence.Jalr
