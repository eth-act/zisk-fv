import Extraction.MemAlignWriteByte
import ZiskFv.AirsClean.MemAlignWriteByte.Circuit

namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open ZiskFv.AirsClean.MemAlignByte (byte_value_factor value_8b_factor value_16b_factor)

/-- A transparent source view. Every lane outside the fourteen modeled columns
is supplied explicitly, never interpreted by a default-zero fallback. -/
structure SourceTrace (F ExtF : Type) where
  rows : ℕ → MemAlignWriteByteRow FGL
  otherMain : ℕ → ℕ → ℕ → ℕ → FGL
  fixed : ℕ → ℕ → ℕ → FGL
  challenges : ℕ → FGL
  airValues : ℕ → FGL

@[reducible]
def sourceMain (c : SourceTrace FGL FGL) (id column row rotation : ℕ) : FGL :=
  if id = 1 ∧ rotation = 0 then
    match column with
    | 0 => (c.rows row).sel_high_4b
    | 1 => (c.rows row).sel_high_2b
    | 2 => (c.rows row).sel_high_b
    | 3 => (c.rows row).direct_value
    | 4 => (c.rows row).composed_value
    | 5 => (c.rows row).written_composed_value
    | 6 => (c.rows row).written_byte_value
    | 7 => (c.rows row).value_16b
    | 8 => (c.rows row).value_8b
    | 9 => (c.rows row).byte_value
    | 10 => (c.rows row).addr_w
    | 11 => (c.rows row).step
    | 12 => (c.rows row).mem_write_values_0
    | 13 => (c.rows row).mem_write_values_1
    | _ => c.otherMain id column row rotation
  else c.otherMain id column row rotation

instance sourceCircuit : Extraction.Circuit FGL FGL SourceTrace where
  main := sourceMain
  preprocessed c := c.fixed
  challenge c := c.challenges
  exposed c := c.airValues

def ExtractedPolynomials (c : SourceTrace FGL FGL) (r : ℕ) : Prop :=
  MemAlignWriteByte.extraction.constraint_0_every_row c r ∧
  MemAlignWriteByte.extraction.constraint_1_every_row c r ∧
  MemAlignWriteByte.extraction.constraint_2_every_row c r ∧
  MemAlignWriteByte.extraction.constraint_3_every_row c r ∧
  MemAlignWriteByte.extraction.constraint_4_every_row c r ∧
  MemAlignWriteByte.extraction.constraint_5_every_row c r ∧
  MemAlignWriteByte.extraction.constraint_6_every_row c r

/-- All seven, at every source row. Unmodeled lanes remain arbitrary. -/
theorem polynomials_iff_extracted (c : SourceTrace FGL FGL) (r : ℕ) :
    PolynomialSpec (c.rows r) ↔ ExtractedPolynomials c r := by
  simp only [ExtractedPolynomials,
    MemAlignWriteByte.extraction.constraint_0_every_row,
    MemAlignWriteByte.extraction.constraint_1_every_row,
    MemAlignWriteByte.extraction.constraint_2_every_row,
    MemAlignWriteByte.extraction.constraint_3_every_row,
    MemAlignWriteByte.extraction.constraint_4_every_row,
    MemAlignWriteByte.extraction.constraint_5_every_row,
    MemAlignWriteByte.extraction.constraint_6_every_row,
    sourceCircuit, sourceMain, PolynomialSpec,
    byte_value_factor, value_8b_factor, value_16b_factor, sub_eq_zero]
  rfl

/-- The seven equations consumed by the source weld come from the actual local
component's Spec, not a detached copy of the polynomials. -/
theorem extracted_of_component_spec (c : SourceTrace FGL FGL) (r : ℕ)
    (h : Spec (c.rows r)) : ExtractedPolynomials c r :=
  (polynomials_iff_extracted c r).mp h.1

/-- The source weld is load-bearing for the actual local `main`, including c4
and all three range routes. The source row's data is embedded as constants;
no separate polynomial, range, or source-row-equality premise is requested. -/
theorem extracted_of_main_constraints (c : SourceTrace FGL FGL) (r offset : ℕ)
    (env : Environment FGL)
    (h_holds : ConstraintsHold.Soundness env
      ((main (ProvableType.const (c.rows r))).operations offset)) :
    ExtractedPolynomials c r := by
  apply extracted_of_component_spec c r
  have hspec := spec_of_main_constraints offset env (ProvableType.const (c.rows r)) h_holds
  simpa only [ProvableType.eval_const] using hspec

/-- Pin the resolved source instance to the independently recorded fourteen
stage-1 columns; arbitrary unmodeled source cells remain explicit. -/
theorem sourceCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL SourceTrace) =
      { main := sourceMain
        preprocessed := fun c => c.fixed
        challenge := fun c => c.challenges
        exposed := fun c => c.airValues } := rfl

end ZiskFv.AirsClean.MemAlignWriteByte
