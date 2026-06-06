import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.ZiskCircuit.LoadD
import ZiskFv.ZiskCircuit.LoadDerivation
import ZiskFv.ZiskCircuit.MemModel
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.EquivCore.Bridge.Mem
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.SailSpec.ld
import ZiskFv.SailSpec.BusEffect
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Channels.MemoryBusBytes

/-!
End-to-end theorem for RV64 LD (load doubleword). Combines:

* explicit LD Main-row, memory, and route facts,
* the compositional LD spec
  (`ZiskFv.ZiskCircuit.LoadD.load_d_compositional`),
* the Sail pure-function equivalence
  (`PureSpec.execute_LOADD_pure_equiv`; closed via the trusted
  memory-model axiom `execute_LOADD_pure_equiv_axiom` — see
  `RV64D/ld.lean` and `trust/trusted-base.md` entry M1),

into three companion theorems paralleling the ADD and BEQ archetypes:

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

namespace ZiskFv.EquivCore.Ld

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.LoadD


/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 LD (`.LOAD (imm, rs1, rd, false, 8)`) reduces to the
    pure-function block supplied by `PureSpec.execute_LOADD_pure`,
    given the register/PC/memory/alignment assumptions.

    Wraps `PureSpec.execute_LOADD_pure_equiv`, which delegates to the
    trusted `execute_LOADD_pure_equiv_axiom` (see `RV64D/ld.lean` and
    `trust/trusted-base.md`). -/
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

/-- LD equivalence from already-discharged Main/provider memory facts.

This is the lookup-free proof core. The canonical `equiv_LD` below still
feeds it through the legacy bridge while T4 is in progress; the Clean
variant feeds it from `Bridge.MemClean.ld_discharge_full_clean_provider`.
-/
lemma equiv_LD_of_discharged
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (h_main_emit_b :
      main.b_0 r_main = memory_entry_lo bus.e1
      ∧ main.b_1 r_main = memory_entry_hi bus.e1
      ∧ bus.e1.as = 2
      ∧ bus.e1.multiplicity = -1)
    (h_main_emit_c :
      main.c_0 r_main = memory_entry_lo bus.e2
      ∧ main.c_1 r_main = memory_entry_hi bus.e2)
    (h_ptr_match :
      bus.e1.ptr.toNat = ld_input.r1_val.toNat
        + (BitVec.signExtend 64 ld_input.imm).toNat)
    (h_rd_zero_iff :
      Transpiler.wrap_to_regidx bus.e2.ptr = 0 ↔ ld_input.rd = 0)
    (h_rd_idx :
      ld_input.rd.toNat = (Transpiler.wrap_to_regidx bus.e2.ptr).val)
    (h_copy0 : ZiskFv.Airs.Main.internal_op1_copies_b0 main r_main)
    (h_copy1 : ZiskFv.Airs.Main.internal_op1_copies_b1 main r_main)
    (h_mem :
      state.mem[bus.e1.ptr.toNat]? = .some (byteAt bus.e1 0)
      ∧ state.mem[bus.e1.ptr.toNat + 1]? = .some (byteAt bus.e1 1)
      ∧ state.mem[bus.e1.ptr.toNat + 2]? = .some (byteAt bus.e1 2)
      ∧ state.mem[bus.e1.ptr.toNat + 3]? = .some (byteAt bus.e1 3)
      ∧ state.mem[bus.e1.ptr.toNat + 4]? = .some (byteAt bus.e1 4)
      ∧ state.mem[bus.e1.ptr.toNat + 5]? = .some (byteAt bus.e1 5)
      ∧ state.mem[bus.e1.ptr.toNat + 6]? = .some (byteAt bus.e1 6)
      ∧ state.mem[bus.e1.ptr.toNat + 7]? = .some (byteAt bus.e1 7)) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_ext, h_op⟩ := pins
  obtain ⟨mstatus, pmaRegion, misa, mseccfg⟩ := regs
  obtain ⟨risc_v_assumptions, h_opcode_assumptions, h_exec_len,
          h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as⟩ := promises
  -- Step 1. Reduce LHS via Sail-level equivalence.
  rw [equiv_LD_sail state ld_input mstatus pmaRegion misa mseccfg
        risc_v_assumptions h_opcode_assumptions]
  symm
  -- Step 2. Reduce RHS via the 8-byte load bus-effect lemma.
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_load_rrrw
        state exec_row e0 e1 e2
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  -- Unpack ld_state_assumptions: data0..data7 are at successive
  -- state.mem keys starting at r1_val + signExt(imm).
  obtain ⟨_h_pc, _h_r1_read,
          h_d0, h_d1, h_d2, h_d3, h_d4, h_d5, h_d6, h_d7,
          _h_bound, _h_aligned⟩ := h_opcode_assumptions
  have h_ptr_match' := h_ptr_match
  rw [h_ptr_match'] at h_mem
  obtain ⟨he0, he1, he2, he3, he4, he5, he6, he7⟩ := h_mem
  have hd0 : ((byteAt e1 0) : BitVec 8) = ld_input.data0 := by
    rw [h_d0] at he0; exact (Option.some.inj he0).symm
  have hd1 : ((byteAt e1 1) : BitVec 8) = ld_input.data1 := by
    rw [h_d1] at he1; exact (Option.some.inj he1).symm
  have hd2 : ((byteAt e1 2) : BitVec 8) = ld_input.data2 := by
    rw [h_d2] at he2; exact (Option.some.inj he2).symm
  have hd3 : ((byteAt e1 3) : BitVec 8) = ld_input.data3 := by
    rw [h_d3] at he3; exact (Option.some.inj he3).symm
  have hd4 : ((byteAt e1 4) : BitVec 8) = ld_input.data4 := by
    rw [h_d4] at he4; exact (Option.some.inj he4).symm
  have hd5 : ((byteAt e1 5) : BitVec 8) = ld_input.data5 := by
    rw [h_d5] at he5; exact (Option.some.inj he5).symm
  have hd6 : ((byteAt e1 6) : BitVec 8) = ld_input.data6 := by
    rw [h_d6] at he6; exact (Option.some.inj he6).symm
  have hd7 : ((byteAt e1 7) : BitVec 8) = ld_input.data7 := by
    rw [h_d7] at he7; exact (Option.some.inj he7).symm
  have h_emit_b_lo_hi :
      main.b_0 r_main = memory_entry_lo e1
      ∧ main.b_1 r_main = memory_entry_hi e1 :=
    ⟨h_main_emit_b.1, h_main_emit_b.2.1⟩
  obtain ⟨h12_0, h12_1, h12_2, h12_3, h12_4, h12_5, h12_6, h12_7⟩ :=
    ZiskFv.ZiskCircuit.LoadDerivation.load_copyb_e1_e2_bytes_eq_bv
      main r_main e1 e2 h_copy0 h_copy1 h_ext h_op
      h_emit_b_lo_hi h_main_emit_c
  have hd2_0 : ((byteAt e2 0) : BitVec 8) = ld_input.data0 := h12_0.trans hd0
  have hd2_1 : ((byteAt e2 1) : BitVec 8) = ld_input.data1 := h12_1.trans hd1
  have hd2_2 : ((byteAt e2 2) : BitVec 8) = ld_input.data2 := h12_2.trans hd2
  have hd2_3 : ((byteAt e2 3) : BitVec 8) = ld_input.data3 := h12_3.trans hd3
  have hd2_4 : ((byteAt e2 4) : BitVec 8) = ld_input.data4 := h12_4.trans hd4
  have hd2_5 : ((byteAt e2 5) : BitVec 8) = ld_input.data5 := h12_5.trans hd5
  have hd2_6 : ((byteAt e2 6) : BitVec 8) = ld_input.data6 := h12_6.trans hd6
  have hd2_7 : ((byteAt e2 7) : BitVec 8) = ld_input.data7 := h12_7.trans hd7
  have h_rd_val_derived :
      U64.toBV #v[byteAt e2 0, byteAt e2 1, byteAt e2 2, byteAt e2 3,
                  byteAt e2 4, byteAt e2 5, byteAt e2 6, byteAt e2 7]
        = ld_input.data7 ++ ld_input.data6 ++ ld_input.data5 ++ ld_input.data4
          ++ ld_input.data3 ++ ld_input.data2 ++ ld_input.data1
          ++ ld_input.data0 := by
    simp only [U64.toBV, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hd2_0, hd2_1, hd2_2, hd2_3, hd2_4, hd2_5, hd2_6, hd2_7]
  simp only [PureSpec.execute_LOADD_pure]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e2.ptr = 0
  · rw [dif_pos h_rd_zero, dif_pos (h_rd_zero_iff.mp h_rd_zero)]
  · have h_rd_input_ne : ld_input.rd ≠ 0 :=
      fun h => h_rd_zero (h_rd_zero_iff.mpr h)
    rw [dif_neg h_rd_zero, dif_neg h_rd_input_ne, h_rd_val_derived]
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

/-- Clean-backed LD equivalence with explicit structural memory witnesses.

This theorem proves the LD path without `main_load_emission_bundle` or
`lookup_consumer_matches_provider_load`: the Main emission and Mem provider
facts are supplied by `Bridge.MemClean.ld_discharge_full_clean_provider`.
It is intentionally non-canonical for now; T4 will move the canonical
wrapper over only after the shared structural witness bundle is threaded
through `Compliance.lean`. -/
lemma equiv_LD_clean_provider
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (h_memory_burden : promises.memoryBurden)
    (r_main r_mem : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (mainRow : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (memRow : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_main_row :
      mainRow.core = ZiskFv.AirsClean.Main.rowAt main r_main)
    (h_mem_row :
      memRow = ZiskFv.AirsClean.Mem.rowAt mem r_mem)
    (h_main_spec : ZiskFv.AirsClean.Main.Spec mainRow.core)
    (h_store_pc : mainRow.core.store_pc = 0)
    (h_main_b_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage mainRow) (-1) 2))
    (h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage mainRow) 1 1))
    (h_mem_match :
      ZiskFv.Airs.MemoryBus.matches_memory_payload bus.e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Mem.memBusMessage memRow) 1 2))
    (h_addr1 :
      mainRow.rom.addr1.toNat =
        ld_input.r1_val.toNat + (BitVec.signExtend 64 ld_input.imm).toNat)
    (h_addr2_zero_iff :
      Transpiler.wrap_to_regidx mainRow.rom.addr2 = 0 ↔ ld_input.rd = 0)
    (h_addr2_idx :
      ld_input.rd.toNat = (Transpiler.wrap_to_regidx mainRow.rom.addr2).val)
    (h_mem_sel : mem.sel r_mem = 1)
    (h_mem_wr : mem.wr r_mem = 0) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_bundle, h_mem⟩ :=
    ZiskFv.EquivCore.Bridge.MemClean.ld_discharge_full_clean_provider
      main mem r_main r_mem mainRow memRow bus.e1 bus.e2 state
      ld_input.r1_val ld_input.imm ld_input.rd
      h_main_row h_mem_row h_main_spec h_store_pc
      h_main_b_match h_main_c_match h_mem_match
      h_addr1 h_addr2_zero_iff h_addr2_idx
      h_mem_sel h_mem_wr (promises.mem_trace_agreement h_memory_burden)
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match, h_rd_zero_iff,
          h_rd_idx, h_copy0, h_copy1⟩ := h_bundle
  exact equiv_LD_of_discharged state ld_input regs bus promises main r_main pins
    h_main_emit_b h_main_emit_c h_ptr_match h_rd_zero_iff h_rd_idx
    h_copy0 h_copy1 h_mem

/-- Bundle-shaped Clean-backed LD equivalence.

This is the migration-facing form: adding one structural witness binder at
the canonical layer is reviewable in the caller-burden ledger, while the
bundle fields document the actual Main/Mem row and adapter pins. -/
lemma equiv_LD_clean_provider_witness
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL)
    (h_memory_burden : promises.memoryBurden)
    (r_main : ℕ)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LdCleanWitness
        main mem r_main bus ld_input) :
    execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_bundle, h_mem⟩ :=
    ZiskFv.EquivCore.Bridge.MemClean.ld_discharge_full_clean_provider_of_witness
      main mem r_main bus state ld_input w (promises.mem_trace_agreement h_memory_burden)
  obtain ⟨h_main_emit_b, h_main_emit_c, h_ptr_match, h_rd_zero_iff,
          h_rd_idx, h_copy0, h_copy1⟩ := h_bundle
  exact equiv_LD_of_discharged state ld_input regs bus promises main r_main pins
    h_main_emit_b h_main_emit_c h_ptr_match h_rd_zero_iff h_rd_idx
    h_copy0 h_copy1 h_mem

end ZiskFv.EquivCore.Ld
