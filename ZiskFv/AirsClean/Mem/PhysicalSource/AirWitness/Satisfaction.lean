import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.Recovery
import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.Algebra
import ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceEquations

/-! Supplemental complete AIR-satisfaction feasibility for ONE actual computed
source image. No production/native/world validation, full ensemble, balance
oracle, Root caller promise, strengthened validator or protected cutover occurs.
All34 source clauses and required local lookups are explicit below. GROUP0 is
never replaced by legacy AIR0, and no extension coefficient is discarded. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

/-- Every primary field is projected from the computed same-source native view,
not supplied as a function independently from the source buffer. -/
def nativePrimary (row : Index) : MemRow FGL where
  addr := complete.memColumns.addr row
  step := complete.memColumns.step row
  sel := complete.memColumns.sel row
  addr_changes := complete.memColumns.addr_changes row
  step_dual := complete.memColumns.step_dual row
  sel_dual := complete.memColumns.sel_dual row
  value_0 := complete.memColumns.value_0 row
  value_1 := complete.memColumns.value_1 row
  wr := complete.memColumns.wr row
  previous_step := complete.memColumns.previous_step row
  increment_0 := complete.memColumns.increment_0 row
  increment_1 := complete.memColumns.increment_1 row
  read_same_addr := complete.memColumns.read_same_addr row

theorem native_primary_eq (row : Index) : nativePrimary row = primaryRow row := by
  cases h : primaryRow row
  simp only [nativePrimary, CompleteView.memColumns, primary_recovery,
    primaryRow] at h ⊢
  cases h
  rfl

/-- The nine base-only clauses use the unchanged real generated projection at
its existing extracted single-row interface. Typed native AST is used for all
mixed/extension clauses; in particular c33 cannot use legacy exposed AIR0. -/
def actualClause (row : Index) (equation : Fin 34) : Prop :=
  let localRow := MemMirrorWeld.extractedMemRow (nativePrimary row)
  match equation.val with
  | 0 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_0.constraint = some 0
  | 1 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_1.constraint = some 0
  | 2 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_2.constraint = some 0
  | 3 => Mem.extraction.constraint_3_every_row localRow 0
  | 4 => Mem.extraction.constraint_4_every_row localRow 0
  | 5 => Mem.extraction.constraint_5_every_row localRow 0
  | 6 => Mem.extraction.constraint_6_every_row localRow 0
  | 7 => Mem.extraction.constraint_7_every_row localRow 0
  | 8 => Mem.extraction.constraint_8_every_row localRow 0
  | 9 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_9.constraint = some 0
  | 10 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_10.constraint = some 0
  | 11 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_11.constraint = some 0
  | 12 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_12.constraint = some 0
  | 13 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_13.constraint = some 0
  | 14 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_14.constraint = some 0
  | 15 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_15.constraint = some 0
  | 16 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_16.constraint = some 0
  | 17 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_17.constraint = some 0
  | 18 => Mem.extraction.constraint_18_every_row localRow 0
  | 19 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_19.constraint = some 0
  | 20 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_20.constraint = some 0
  | 21 => Mem.extraction.constraint_21_every_row localRow 0
  | 22 => Stage2.evaluate? occurrence row.val constraintOnly_Mem_22.constraint = some 0
  | 23 => Mem.extraction.constraint_23_every_row localRow 0
  | 24 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 0) = some 0
  | 25 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 1) = some 0
  | 26 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 2) = some 0
  | 27 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 3) = some 0
  | 28 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 4) = some 0
  | 29 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 5) = some 0
  | 30 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 6) = some 0
  | 31 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 7) = some 0
  | 32 => Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear 8) = some 0
  | _ => Stage2.evaluate? occurrence row.val constraint_Mem_33 = some 0

private theorem mem_scope : SourceFinalizer.memOccurrence occurrence = true := rfl

private theorem evaluation_recovery (row : Index) (expr : Expr) :
    Stage2.evaluate? occurrence row.val expr = polynomial complete.base row expr := by
  simp only [Stage2.evaluate?, mem_scope, ↓reduceIte]
  exact polynomial_recovery complete row expr

theorem actual_mixed (row : Index) (equation : Fin 15) :
    Stage2.evaluate? occurrence row.val (mixedSource equation).constraint = some 0 := by
  rw [evaluation_recovery, mixed_source_correspondence, segment_satisfies]
  rfl

theorem actual_nonlinear (row : Index) (equation : Fin 9) :
    Stage2.evaluate? occurrence row.val (Stage2.actualNonlinear equation) = some 0 := by
  rw [evaluation_recovery, nonlinear_source_correspondence]
  have satisfies := (stage2_satisfies complete.base row).1
  fin_cases equation <;>
    simp only [Stage2.PolynomialRow.Circuit] at satisfies <;>
    simp_all [Stage2.PolynomialRow.residual]

theorem actual_finalizer (row : Index) :
    Stage2.evaluate? occurrence row.val constraint_Mem_33 = some 0 := by
  rw [evaluation_recovery, finalizer_source_correspondence, (stage2_satisfies complete.base row).2]

/-- All actual34 clauses at ALL physical4194304 rows, including row0 cyclic
predecessor and the unique true physical-last L1 rotation. No prefix/count or
forall-holds input occurs in this theorem. -/
theorem all_actual_clauses : ∀ row : Index, ∀ equation : Fin 34, actualClause row equation := by
  intro row equation
  have mixed := actual_mixed row
  have nonlinear := actual_nonlinear row
  have boundary := actual_finalizer row
  have locals := (local_generated_correspondence row).mp (primary_spec row)
  rw [← native_primary_eq row] at locals
  rcases locals with ⟨l3, l4, l5, l6, l7, l8, l18, l21, l23⟩
  fin_cases equation
  · exact mixed 0
  · exact mixed 1
  · exact mixed 2
  · exact l3
  · exact l4
  · exact l5
  · exact l6
  · exact l7
  · exact l8
  · exact mixed 3
  · exact mixed 4
  · exact mixed 5
  · exact mixed 6
  · exact mixed 7
  · exact mixed 8
  · exact mixed 9
  · exact mixed 10
  · exact mixed 11
  · exact l18
  · exact mixed 12
  · exact mixed 13
  · exact l21
  · exact mixed 14
  · exact l23
  · exact nonlinear 0
  · exact nonlinear 1
  · exact nonlinear 2
  · exact nonlinear 3
  · exact nonlinear 4
  · exact nonlinear 5
  · exact nonlinear 6
  · exact nonlinear 7
  · exact nonlinear 8
  · exact boundary

/-- Local lookup facts are bound to actual native primary cells, not merely
facts about a detached row record. Source bits/range calls are not added to an
unpacked native validator or used to narrow Root acceptance. -/
theorem actual_primary_lookup_widths (row : Index) (column : Fin 13) :
    ∃ value, ZiskFv.AirsClean.NativeTraceCells.cell? .mem occurrence false row.val column.val =
      some value ∧ value.val < 2 ^ Stage1.SourceColumns.packedWidth column := by
  exact ⟨(primary row)[column], canonical_primary_recovery complete row column,
    (local_lookups row).1 column⟩

theorem all_required_local_lookups : ∀ row : Index, LocalLookups row := local_lookups

/-- Final handoff is a theorem about an ACTUALLY computed same-source witness.
It is not a new acceptance field or an assumption asserting AIR satisfaction. -/
theorem constructed_source_satisfies :
    completeFromResolved? occurrence = some complete ∧
    (∀ row : Index, ∀ equation : Fin 34, actualClause row equation) ∧
    (∀ row : Index, LocalLookups row) ∧
    (∃! row : complete.Index, complete.base.l1? (complete.base.next row) = some 1) :=
  ⟨complete_recovers, all_actual_clauses, all_required_local_lookups,
    complete.base.unique_physical_last⟩

end ZiskFv.AirsClean.Mem.PhysicalSource.AirWitness.SourceImage
