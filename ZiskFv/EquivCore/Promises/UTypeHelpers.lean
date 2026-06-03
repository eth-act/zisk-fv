import Mathlib

import ZiskFv.EquivCore.Promises.UType
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.StaticRowProvenance
import ZiskFv.Compliance.AeneasRowProvenance

/-!
# `UTypePromises` companion helpers

Provides helpers that assemble `h_circuit` — the
`<op>_archetype_circuit_holds` term that `equiv_<OP>` accepts alongside
the structural `UTypePromises` bundle.

The AUIPC compatibility helper now takes mode pins explicitly. The LUI route
uses explicit Aeneas-row provenance so the focused per-opcode proof does not
consume the hand-written Lean static transpiler.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.Transpiler.Static


/-- Assemble AUIPC's `h_circuit` from the Main-side activation/opcode
    pins and the per-row AUIPC subset constraint. -/
def auipc_h_circuit_of_main_constraints
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_auipc : m.op r_main = OP_FLAG)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_store_pc : m.store_pc r_main = 1)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc) :
    auipc_archetype_circuit_holds m r_main next_pc :=
  let h_auipc_mode : main_row_in_auipc_mode m r_main :=
    ⟨h_main_active, by rw [h_main_op_auipc]; rfl, h_m32, h_set_pc, h_store_pc⟩
  ⟨h_auipc_subset, h_auipc_mode⟩

/-! ## Static-provenance variants

These helpers are the proof-facing migration target for Aeneas-backed
decode/lower evidence. They assemble the same UTYPE circuit predicates from an
explicit `MainStaticRowProvenance` witness plus facts about the selected static
row, instead of firing legacy transpiler bridge theorems.
-/

/-- Assemble LUI's `h_circuit` from static-row provenance. The static-row
    hypotheses are exactly the decode/lower columns that the Aeneas-extracted
    transpiler path is expected to justify for a selected LUI row. -/
def lui_h_circuit_of_static_provenance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    {inst : Rv64Inst}
    (p : ZiskFv.Compliance.MainStaticRowProvenance m r_main inst)
    (h_static_op : p.staticRow.op = Const.opCopyB)
    (h_static_internal : p.staticRow.isExternalOp = false)
    (h_static_m32 : p.staticRow.m32 = false)
    (h_static_set_pc : p.staticRow.setPc = false)
    (h_static_store_pc : p.staticRow.storePc = false)
    (h_lui_subset : lui_subset_holds m r_main next_pc) :
    lui_archetype_circuit_holds m r_main next_pc :=
  let h_lui_mode : main_row_in_lui_mode m r_main :=
    ⟨ by
        rw [p.is_external_op_eq, h_static_internal]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.op_eq, h_static_op]
        simp [ZiskFv.Compliance.natF, Const.opCopyB]
    , by
        rw [p.m32_eq, h_static_m32]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.set_pc_eq, h_static_set_pc]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.store_pc_eq, h_static_store_pc]
        simp [ZiskFv.Compliance.boolF] ⟩
  ⟨h_lui_subset, h_lui_mode⟩

/-- Assemble LUI's `h_circuit` from Aeneas-backed static-row provenance. -/
def lui_h_circuit_of_aeneas_provenance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : ZiskFv.Compliance.MainAeneasRowProvenance m r_main inst)
    (h_lui_subset : lui_subset_holds m r_main next_pc) :
    lui_archetype_circuit_holds m r_main next_pc :=
  let ⟨h_static_op, h_static_internal, h_static_m32, h_static_set_pc, h_static_store_pc⟩ :=
    ZiskFv.Compliance.MainAeneasRowProvenance.lui_static_mode p
  let h_lui_mode : main_row_in_lui_mode m r_main :=
    ⟨ by
        rw [p.is_external_op_eq, h_static_internal]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.op_eq, h_static_op]
        simp [ZiskFv.Compliance.natF, ZiskFv.Transpiler.Aeneas.Const.opCopyB]
    , by
        rw [p.m32_eq, h_static_m32]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.set_pc_eq, h_static_set_pc]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.store_pc_eq, h_static_store_pc]
        simp [ZiskFv.Compliance.boolF] ⟩
  ⟨h_lui_subset, h_lui_mode⟩

/-- Assemble AUIPC's `h_circuit` from static-row provenance. The static-row
    hypotheses are exactly the decode/lower columns that the Aeneas-extracted
    transpiler path is expected to justify for a selected AUIPC row. -/
def auipc_h_circuit_of_static_provenance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    {inst : Rv64Inst}
    (p : ZiskFv.Compliance.MainStaticRowProvenance m r_main inst)
    (h_static_op : p.staticRow.op = Const.opFlag)
    (h_static_internal : p.staticRow.isExternalOp = false)
    (h_static_m32 : p.staticRow.m32 = false)
    (h_static_set_pc : p.staticRow.setPc = false)
    (h_static_store_pc : p.staticRow.storePc = true)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc) :
    auipc_archetype_circuit_holds m r_main next_pc :=
  let h_auipc_mode : main_row_in_auipc_mode m r_main :=
    ⟨ by
        rw [p.is_external_op_eq, h_static_internal]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.op_eq, h_static_op]
        simp [ZiskFv.Compliance.natF, Const.opFlag]
    , by
        rw [p.m32_eq, h_static_m32]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.set_pc_eq, h_static_set_pc]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.store_pc_eq, h_static_store_pc]
        simp [ZiskFv.Compliance.boolF] ⟩
  ⟨h_auipc_subset, h_auipc_mode⟩

/-- Assemble AUIPC's `h_circuit` from Aeneas-backed static-row provenance. -/
def auipc_h_circuit_of_aeneas_provenance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    {inst : ZiskFv.Transpiler.Aeneas.Rv64imInst}
    (p : ZiskFv.Compliance.MainAeneasAuipcRowProvenance m r_main inst)
    (h_inst_rd_ne_zero : inst.rd ≠ 0#u32)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc) :
    auipc_archetype_circuit_holds m r_main next_pc :=
  let ⟨h_static_op, h_static_internal, h_static_m32, h_static_set_pc, h_static_store_pc⟩ :=
    ZiskFv.Compliance.MainAeneasAuipcRowProvenance.auipc_static_mode p h_inst_rd_ne_zero
  let h_auipc_mode : main_row_in_auipc_mode m r_main :=
    ⟨ by
        rw [p.is_external_op_eq, h_static_internal]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.op_eq, h_static_op]
        simp [ZiskFv.Compliance.natF, ZiskFv.Transpiler.Aeneas.Const.opFlag]
    , by
        rw [p.m32_eq, h_static_m32]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.set_pc_eq, h_static_set_pc]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.store_pc_eq, h_static_store_pc]
        simp [ZiskFv.Compliance.boolF] ⟩
  ⟨h_auipc_subset, h_auipc_mode⟩

end ZiskFv.EquivCore.Promises
