import Mathlib

import ZiskFv.EquivCore.Lb
import ZiskFv.EquivCore.Bridge.MemClean
import ZiskFv.EquivCore.Promises.Load
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionRanges
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Compliance.SharedBundles

/-!
# `equiv_LB` Compliance wrapper — signed-load BinExt SEXT_B chain

Post-T4-purge canonical: takes BinaryExtension row witness +
matches_entry + static lookup soundness directly. The legacy BinaryAdd-arm
route was retired in T4-purge.

Trust footprint: `transpile_*`, `range_bus_sound`,
`memory_bus_entry_byte_range_perm_sound`, MemBridge facts, plus
BinaryExtension `circuit` (static-table lookup soundness via
`StaticLookupSoundness`). Notably absent:
`op_bus_permutation_sound`, `bin_ext_table_consumer_wf`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus


theorem equiv_LB
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lb_input : PureSpec.LbInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      matches_entry (opBus_row_Main main r_main) (opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 ZiskFv.Trusted.OP_SIGNEXTEND_B)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lb_state_assumptions lb_input state)
        (PureSpec.execute_LOADB_pure lb_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
        main mem r_main bus lb_input.r1_val lb_input.imm lb_input.rd) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lb_input.imm, regidx.Regidx lb_input.r1, regidx.Regidx lb_input.rd, false, 1
      ))) state = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨_h_main_active, h_main_op⟩ := pins
  obtain ⟨h_clean_bundle, _h_mem8⟩ :=
    ZiskFv.EquivCore.Bridge.MemClean.ld_discharge_full_clean_provider
      main mem r_main w.r_mem w.mainRow w.memRow e1 e2 state
      lb_input.r1_val lb_input.imm lb_input.rd
      w.main_row w.mem_row w.main_spec w.store_pc
      w.main_b_match w.main_c_match w.mem_match
      w.addr1 w.addr2_zero_iff w.addr2_idx
      w.mem_sel w.mem_legacy_addr w.mem_wr
  have lfd :=
    ZiskFv.EquivCore.Promises.load_full_discharge_LB_of_match_clean
      main v r_main r_binary offset env e1 h_static h_match h_main_op
      h_clean_bundle.1.1
  let h_bytes :=
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
    ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
      v r_binary offset env h_static
  exact ZiskFv.EquivCore.Lb.equiv_LB_clean_provider_of_wf
    state lb_input regs
    ⟨exec_row, e0, e1, e2⟩
    promises
    main mem r_main w.r_mem
    v r_binary lfd.h_op_binary h_bytes h_wfs
    lfd.hc_lo_sum_lt lfd.hc_hi_sum_lt
    lfd.h_match_clo lfd.h_match_chi
    lfd.h_a0_match
    w.mainRow w.memRow w.main_row w.mem_row w.main_spec w.store_pc
    w.main_b_match w.main_c_match w.mem_match
    w.addr1 w.addr2_zero_iff w.addr2_idx
    w.mem_sel w.mem_legacy_addr w.mem_wr

end ZiskFv.Compliance
