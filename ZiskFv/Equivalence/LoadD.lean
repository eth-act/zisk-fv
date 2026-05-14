import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.LoadD
import ZiskFv.Circuit.LoadDerivation
import ZiskFv.Circuit.MemModel
import ZiskFv.Airs.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Airs.BusEmission
import ZiskFv.Equivalence.Bridge.Mem
import ZiskFv.Sail.ld
import ZiskFv.Sail.BusEffect

/-!
End-to-end theorem for RV64 LD (load doubleword). Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_LD`),
* the compositional LD spec
  (`ZiskFv.Circuit.LoadD.load_d_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LOADD_pure_equiv`; closed via the trusted
  memory-model axiom `execute_LOADD_pure_equiv_axiom` — see
  `RV64D/ld.lean` and `docs/fv/trusted-base.md` entry M1),

into three companion theorems paralleling the ADD and BEQ archetypes:

* `equiv_LD_circuit` — circuit-level. States that the Main row's packed `c`
  lanes (as FGL) equal the 8-byte memory-bus entry's packed value,
  given the constraint-set + mode + memory-match hypotheses.
* `equiv_LD_sail` — Sail-level. Wraps `execute_LOADD_pure_equiv`.
* `equiv_LD` — the canonical theorem
  `execute_instruction (.LOAD …) = (bus_effect …).2`.

The per-byte rd-write-value parameter `h_rd_val` is derived from
`mem_load_correct` (see `Spec/MemModel.lean`) plus a ptr-match
hypothesis tying the memory-read entry's pointer to Sail's
`r1_val + signExtend imm` and a per-byte mem-read-entry ↔ rd-write-entry
passthrough hypothesis. These carry circuit content (Mem AIR witness +
Main AIR witness + bus emission shape), not Sail-spec output content.
-/

namespace ZiskFv.Equivalence.LoadD

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Circuit.LoadD

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LD (`.LOAD (imm, rs1, rd, false, 8)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADD_pure`,
    given the register/PC/memory/alignment assumptions.

    Wraps `PureSpec.execute_LOADD_pure_equiv`, which delegates to the
    trusted `execute_LOADD_pure_equiv_axiom` (see `RV64D/ld.lean` and
    `docs/fv/trusted-base.md`). -/
lemma equiv_LD_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.ld_state_assumptions ld_input state) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state
      = let output := PureSpec.execute_LOADD_pure ld_input
        (do
          Sail.writeReg Register.nextPC output.nextPC
          match output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_LOADD_pure_equiv
    ld_input risc_v_assumptions h_opcode_assumptions

/-- **Metaplan theorem.** Sail's `execute_instruction` on an LD equals
    the state computed by applying `bus_effect` to the circuit's
    execution + memory bus rows.

    The per-byte rd-write-value equality is **derived internally** from
    `Circuit.MemModel.mem_load_correct` plus circuit hypotheses
    (`main`, `mem`, `r_main`, `h_main_emit_b`, `h_ptr_match`,
    `h_e1_e2_bytes`). The `h_rd_zero_iff` and `h_rd_idx` hypotheses are
    scenario-binding ptr-match facts (Sail's `rd` operand vs the bus's
    `e2.ptr`) that cannot be derived from circuit content alone. -/
theorem equiv_LD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (mstatus : RegisterType Register.mstatus)
    (pmaRegion : PMA_Region)
    (misa : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (risc_v_assumptions :
      RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions :
      PureSpec.ld_state_assumptions ld_input state)
    -- Structural bus hypotheses (shape d — LD).
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_LOADD_pure ld_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 2)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 1)
    -- Circuit-level parameters that supplant `h_rd_val`.
    (main : Valid_Main C FGL FGL) (mem : Valid_Mem C FGL FGL) (r_main : ℕ)
    (h_ext : main.is_external_op r_main = 0)
    (h_op : main.op r_main = (1 : FGL)) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- Step 0. Discharge the Mem-shape promise hypotheses via the
  -- Mem bridge entry point. This pulls `h_main_emit_b`, `h_main_emit_c`,
  -- `h_ptr_match`, `h_rd_zero_iff`, `h_rd_idx`, `h_copy0`, `h_copy1`
  -- from `main_load_emission_bundle` (class #4 trust ledger).
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match,
          h_rd_zero_iff, h_rd_idx, h_copy0, h_copy1⟩ :=
    ZiskFv.Equivalence.Bridge.Mem.ld_discharge_full
      main r_main e1 e2 ld_input.r1_val ld_input.imm ld_input.rd
      h_ext h_op h_m1_mult h_m1_as h_m2_mult h_m2_as
  -- Step 1. Reduce LHS via Sail-level equivalence.
  rw [equiv_LD_sail state ld_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  -- Step 2. Reduce RHS via the 8-byte load bus-effect lemma.
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_load_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  -- Step 3. Derive the per-byte data ↔ e1.x_i agreement via mem_load_correct
  -- + the load-side state.mem assumptions + ptr-match.
  have h_mem :=
    ZiskFv.Circuit.MemModel.mem_load_correct
      main mem r_main e1 state h_main_emit_b
  -- Unpack ld_state_assumptions: data0..data7 are at successive
  -- state.mem keys starting at r1_val + signExt(imm).
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1, h_d2, h_d3, h_d4, h_d5, h_d6, h_d7,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  -- Bridge state.mem facts via h_ptr_match: e1.ptr.toNat = r1_val +
  -- signExt(imm).toNat, so mem_load_correct's keys equal the
  -- assumption-side keys. Hence (e1.x_i : BitVec 8) = data_i via
  -- .some-injectivity.
  have h_ptr_match' := h_ptr_match
  rw [h_ptr_match'] at h_mem
  obtain ⟨he0, he1, he2, he3, he4, he5, he6, he7⟩ := h_mem
  -- Combine with state.mem assumptions to get (e1.x_i : BitVec 8) = data_i.
  have hd0 : (e1.x0 : BitVec 8) = ld_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : (e1.x1 : BitVec 8) = ld_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have hd2 : (e1.x2 : BitVec 8) = ld_input.data2 := by
    rw [h_d2] at he2; exact (Option.some.inj he2).symm
  have hd3 : (e1.x3 : BitVec 8) = ld_input.data3 := by
    rw [h_d3] at he3; exact (Option.some.inj he3).symm
  have hd4 : (e1.x4 : BitVec 8) = ld_input.data4 := by
    rw [h_d4] at he4; exact (Option.some.inj he4).symm
  have hd5 : (e1.x5 : BitVec 8) = ld_input.data5 := by
    rw [h_d5] at he5; exact (Option.some.inj he5).symm
  have hd6 : (e1.x6 : BitVec 8) = ld_input.data6 := by
    rw [h_d6] at he6; exact (Option.some.inj he6).symm
  have hd7 : (e1.x7 : BitVec 8) = ld_input.data7 := by
    rw [h_d7] at he7; exact (Option.some.inj he7).symm
  -- Derive (e2.x_i : BitVec 8) = (e1.x_i : BitVec 8) from circuit witnesses
  -- via copyb passthrough (Main constraints 9/16) plus byte ranges.
  have h_emit_b_lo_hi :
      main.b_0 r_main = memory_entry_lo e1
      ∧ main.b_1 r_main = memory_entry_hi e1 :=
    ⟨h_main_emit_b.1, h_main_emit_b.2.1⟩
  -- Memory-bus entry byte ranges discharged via the byte-range bus
  -- protocol axiom (`memory_bus_entry_byte_range_perm_sound`).
  have h_e1_range : memory_entry_bytes_in_range e1 :=
    memory_bus_entry_byte_range_perm_sound e1
  have h_e2_range : memory_entry_bytes_in_range e2 :=
    memory_bus_entry_byte_range_perm_sound e2
  obtain ⟨h12_0, h12_1, h12_2, h12_3, h12_4, h12_5, h12_6, h12_7⟩ :=
    ZiskFv.Circuit.LoadDerivation.load_copyb_e1_e2_bytes_eq_bv
      main r_main e1 e2 h_copy0 h_copy1 h_ext h_op
      h_emit_b_lo_hi h_main_emit_c h_e1_range h_e2_range
  have hd2_0 : (e2.x0 : BitVec 8) = ld_input.data0 := h12_0.trans hd0
  have hd2_1 : (e2.x1 : BitVec 8) = ld_input.data1 := h12_1.trans hd1
  have hd2_2 : (e2.x2 : BitVec 8) = ld_input.data2 := h12_2.trans hd2
  have hd2_3 : (e2.x3 : BitVec 8) = ld_input.data3 := h12_3.trans hd3
  have hd2_4 : (e2.x4 : BitVec 8) = ld_input.data4 := h12_4.trans hd4
  have hd2_5 : (e2.x5 : BitVec 8) = ld_input.data5 := h12_5.trans hd5
  have hd2_6 : (e2.x6 : BitVec 8) = ld_input.data6 := h12_6.trans hd6
  have hd2_7 : (e2.x7 : BitVec 8) = ld_input.data7 := h12_7.trans hd7
  -- Build the rd-value equality (the previous `h_rd_val` shape).
  have h_rd_val_derived :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
        = ld_input.data7 ++ ld_input.data6 ++ ld_input.data5 ++ ld_input.data4
          ++ ld_input.data3 ++ ld_input.data2 ++ ld_input.data1
          ++ ld_input.data0 := by
    simp only [U64.toBV, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hd2_0, hd2_1, hd2_2, hd2_3, hd2_4, hd2_5, hd2_6, hd2_7]
  -- Discharge the rd-match branch via the decomposed hypotheses.
  simp only [PureSpec.execute_LOADD_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · -- Zero case: both sides reduce to `pure ()`.
    rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · -- Nonzero case: both sides write the same rd with the same value.
    have h_rd_input_ne : ld_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne, h_rd_val_derived]
    -- Establish the `Finset.Icc 1 31` subtype equality and rewrite it
    -- in the LHS. The two wrappers carry identical proofs modulo the
    -- underlying Nat; only the Nat side matters.
    have h_rd_ub : (Transpiler.wrap_to_regidx e2.ptr).val < 32 :=
      (Transpiler.wrap_to_regidx e2.ptr).isLt
    have h_tn_bound : ld_input.rd.toNat < 32 := by
      obtain ⟨⟨n, hn⟩⟩ := ld_input.rd
      simp [BitVec.toNat]; omega
    have h_tn_ne : ld_input.rd.toNat ≠ 0 := by
      intro h
      apply h_rd_input_ne
      apply BitVec.eq_of_toNat_eq
      simp [h]
    have h_idx_eq :
        (⟨(Transpiler.wrap_to_regidx e2.ptr).val, by
            apply Finset.mem_Icc.mpr
            refine ⟨?_, by omega⟩
            rw [← h_rd_idx]; omega⟩
          : Finset.Icc 1 31)
          = ⟨ld_input.rd.toNat,
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩ := by
      apply Subtype.ext
      exact h_rd_idx.symm
    rw [h_idx_eq]

end ZiskFv.Equivalence.LoadD
