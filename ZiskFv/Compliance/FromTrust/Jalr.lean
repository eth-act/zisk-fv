import Mathlib

import ZiskFv.Equivalence.Jalr
import ZiskFv.Tactics.JumpArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_JALR` Compliance wrapper — ControlFlow non-branch (Step 4.2)

> **Status:** within-shape wrapper, derived mechanically from
> `FromTrust/Lui.lean` (Step 4.1.1). Lives outside the canonical
> surface so V1 anti-laundering metrics on the canonical theorem
> are unaffected.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_JALR` via
  `jalr_discharge_lanes` (consumes `main_store_pc_emission_bundle`,
  trust class #4). Pre-discharged on the canonical surface.
* **Mode pins.** N/A on the provider side. Main-side mode pins come
  from `transpile_JALR` (class #1).
* **Sign-witness pins.** N/A.
* **Range/bound.** Internalized by `equiv_JALR`.
* **Operand bridges.** `read_xreg rs1` is consumed by
  `equiv_JALR_sail`; the wrapper passes it through.

## Anti-laundering report

* **Zero new axioms** — consumes `transpile_JALR` (class #1) plus
  `equiv_JALR`'s existing closure.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_JALR`.** Mirrors
    `equiv_LUI_from_trust`'s structure with `transpile_JALR` substituted
    for `transpile_LUI` and JALR's mode/subset definitions in place of
    LUI's. JALR uses `OP_COPYB` activation (internal copyb route per
    archetype-validation modeling). -/
theorem equiv_JALR_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- AIR validator + row index.
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    -- Activation + opcode pins (Compliance ROM handshake).
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jalr : m.op r_main = OP_COPYB)
    -- Per-row Main constraint bundle.
    (h_jalr_subset :
      ZiskFv.Tactics.JumpArchetype.jalr_subset_holds m r_main next_pc)
    -- Sail-side state predicates (SPEC-PRE).
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
    -- Bus-shape structural hypotheses — pass-through from `equiv_JALR`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    -- Happy-path hypothesis (ZisK target-aligned SPEC-PRE).
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Range/no-wrap obligations.
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- ============ Derive routing mode pins via `transpile_JALR` ============
  have h_tr := ZiskFv.Trusted.transpile_JALR m r_main (0 : Fin 32) (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 } h_main_active h_main_op_jalr
  obtain ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _⟩ := h_tr
  -- ============ Assemble `jalr_circuit_holds` ============
  -- The canonical `jalr_circuit_holds` predicate packs the
  -- jalr-subset + mode pins; under the archetype-validation route,
  -- the mode pins are `is_external_op = 0`, `op = 1`, `m32 = 0`,
  -- `set_pc = 1`, `store_pc = 1`. We have these from
  -- `h_main_active` + `h_main_op_jalr` + the transpile-derived ones.
  have h_circuit : ZiskFv.ZiskCircuit.Jalr.jalr_circuit_holds m r_main next_pc := by
    refine ⟨h_jalr_subset, ?_⟩
    refine ⟨h_main_active, ?_, h_m32, h_set_pc, h_store_pc⟩
    rw [h_main_op_jalr]; rfl
  -- ============ Delegate to canonical `equiv_JALR` ============
  exact ZiskFv.Equivalence.Jalr.equiv_JALR
    state jalr_input imm rs1 rd misa_val mseccfg
    exec_row e_rd nextPC_val m r_main next_pc
    h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
    h_cur_privilege h_mseccfg
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_success h_nextPC_option h_rd_idx
    h_circuit h_pc_bound h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
