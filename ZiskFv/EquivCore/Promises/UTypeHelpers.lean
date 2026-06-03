import Mathlib

import ZiskFv.EquivCore.Promises.UType
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Compliance.RowProvenance

/-!
# `UTypePromises` companion helpers

Provides helpers that assemble `h_circuit` — the
`<op>_archetype_circuit_holds` term that `equiv_<OP>` accepts alongside
the structural `UTypePromises` bundle.

The compatibility helpers take mode pins explicitly or consume extracted
row-shape provenance. They do not depend on generated Aeneas artifacts.
-/

namespace ZiskFv.EquivCore.Promises

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype


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

/-- Assemble LUI's `h_circuit` from the Main-side activation/opcode
    pins and the per-row LUI subset constraint. -/
def lui_h_circuit_of_main_constraints
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_lui : m.op r_main = OP_COPYB)
    (h_m32 : m.m32 r_main = 0)
    (h_set_pc : m.set_pc r_main = 0)
    (h_store_pc : m.store_pc r_main = 0)
    (h_lui_subset : lui_subset_holds m r_main next_pc) :
    lui_archetype_circuit_holds m r_main next_pc :=
  let h_lui_mode : main_row_in_lui_mode m r_main :=
    ⟨h_main_active, by rw [h_main_op_lui]; rfl, h_m32, h_set_pc, h_store_pc⟩
  ⟨h_lui_subset, h_lui_mode⟩

/-! ## Row-provenance variants

These helpers are the proof-facing migration target for generated
decode/lower evidence. They assemble the same UTYPE circuit predicates from an
explicit `MainRowProvenance` witness plus facts about the selected
production-extracted row shape.
-/

/-- Assemble LUI's `h_circuit` from row-shape provenance. The row-shape
    hypotheses are exactly the decode/lower columns that the Aeneas-extracted
    row-shape path is expected to justify for a selected LUI row. -/
def lui_h_circuit_of_row_provenance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (p : ZiskFv.Compliance.MainRowProvenance m r_main)
    (mode : ZiskFv.Compliance.MainRowProvenance.LuiRowMode p)
    (h_lui_subset : lui_subset_holds m r_main next_pc) :
    lui_archetype_circuit_holds m r_main next_pc :=
  let h_lui_mode : main_row_in_lui_mode m r_main :=
    ⟨ by
        rw [p.is_external_op_eq, mode.internal_eq]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.op_eq, mode.op_eq]
        simp [ZiskFv.Compliance.natF, ZiskFv.Compliance.ExtractedConst.opCopyB]
    , by
        rw [p.m32_eq, mode.m32_eq]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.set_pc_eq, mode.set_pc_eq]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.store_pc_eq, mode.store_pc_eq]
        simp [ZiskFv.Compliance.boolF] ⟩
  ⟨h_lui_subset, h_lui_mode⟩

/-- Assemble AUIPC's `h_circuit` from row-shape provenance. The row-shape
    hypotheses are exactly the decode/lower columns that the generated
    row-shape path is expected to justify for a selected AUIPC row. -/
def auipc_h_circuit_of_row_provenance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (p : ZiskFv.Compliance.MainRowProvenance m r_main)
    (mode : ZiskFv.Compliance.MainRowProvenance.AuipcRowMode p)
    (h_auipc_subset : auipc_subset_holds m r_main next_pc) :
    auipc_archetype_circuit_holds m r_main next_pc :=
  let h_auipc_mode : main_row_in_auipc_mode m r_main :=
    ⟨ by
        rw [p.is_external_op_eq, mode.internal_eq]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.op_eq, mode.op_eq]
        simp [ZiskFv.Compliance.natF, ZiskFv.Compliance.ExtractedConst.opFlag]
    , by
        rw [p.m32_eq, mode.m32_eq]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.set_pc_eq, mode.set_pc_eq]
        simp [ZiskFv.Compliance.boolF]
    , by
        rw [p.store_pc_eq, mode.store_pc_eq]
        simp [ZiskFv.Compliance.boolF] ⟩
  ⟨h_auipc_subset, h_auipc_mode⟩

end ZiskFv.EquivCore.Promises
