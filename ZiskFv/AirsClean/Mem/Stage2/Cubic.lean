import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Source cubic arithmetic for Mem stage 2

Source: immutable `ff0e33a9`,
`/nix/store/zqhhhzb9rq7gcbv46c1fz4k91pk42yni-source/pil2-stark/src/goldilocks/src/goldilocks_cubic_extension.hpp`.
Lines 13–18 specify three coefficients and the polynomial `X^3 - X - 1`.
Lines 169–225 specify addition, subtraction and negation; lines 232–260
specify optimized multiplication and mixed base/extension multiplication.

This module models those arithmetic blocks over any commutative ring. It does
not assert irreducibility, a field instance, or a runtime representation binding.
-/

namespace ZiskFv.AirsClean.Mem.Stage2

/-- The ordered coefficients of `c0 + c1 * X + c2 * X^2`. -/
@[ext]
structure Ext3 (F : Type*) where
  c0 : F
  c1 : F
  c2 : F
  deriving DecidableEq

namespace Ext3

variable {F : Type*}

/-- Read a source coefficient (indices zero, one, two). -/
def coeff (a : Ext3 F) (i : Fin 3) : F :=
  match i.val with
  | 0 => a.c0
  | 1 => a.c1
  | _ => a.c2

/-- Construct a whole extension block from its three coefficients. -/
def ofFn (f : Fin 3 → F) : Ext3 F := ⟨f 0, f 1, f 2⟩

@[simp] theorem coeff_zero (a : Ext3 F) : coeff a 0 = a.c0 := rfl
@[simp] theorem coeff_one (a : Ext3 F) : coeff a 1 = a.c1 := rfl
@[simp] theorem coeff_two (a : Ext3 F) : coeff a 2 = a.c2 := rfl

@[simp] theorem coeff_ofFn (f : Fin 3 → F) (i : Fin 3) :
    coeff (ofFn f) i = f i := by
  fin_cases i <;> rfl

@[simp] theorem ofFn_coeff (a : Ext3 F) : ofFn (coeff a) = a := by
  cases a
  rfl

 theorem eq_of_coeff_eq {a b : Ext3 F} (h : ∀ i, coeff a i = coeff b i) : a = b := by
  apply Ext3.ext
  · exact h 0
  · exact h 1
  · exact h 2

variable [CommRing F]

instance : Zero (Ext3 F) := ⟨⟨0, 0, 0⟩⟩
instance : One (Ext3 F) := ⟨⟨1, 0, 0⟩⟩
instance : Add (Ext3 F) := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Sub (Ext3 F) := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩⟩
instance : Neg (Ext3 F) := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩

/-- Base values occupy only coefficient zero, not all three coefficients. -/
def ofBase (c : F) : Ext3 F := ⟨c, 0, 0⟩

/-- Literal arithmetic schedule of source lines 232–245. -/
def sourceMul (a b : Ext3 F) : Ext3 F :=
  let A := (a.c0 + a.c1) * (b.c0 + b.c1)
  let B := (a.c0 + a.c2) * (b.c0 + b.c2)
  let C := (a.c1 + a.c2) * (b.c1 + b.c2)
  let D := a.c0 * b.c0
  let E := a.c1 * b.c1
  let G := D - E
  let H := a.c2 * b.c2
  ⟨(C + G) - H, (((A + C) - E) - E) - D, B - G⟩

/-- Independently expanded polynomial convolution, then reduction using
`X^3 = X + 1` and `X^4 = X^2 + X`. -/
def convolutionMul (a b : Ext3 F) : Ext3 F :=
  let d0 := a.c0 * b.c0
  let d1 := a.c0 * b.c1 + a.c1 * b.c0
  let d2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
  let d3 := a.c1 * b.c2 + a.c2 * b.c1
  let d4 := a.c2 * b.c2
  ⟨d0 + d3, d1 + d3 + d4, d2 + d4⟩

/-- Kernel ring normalization establishes the source/reduction correspondence. -/
theorem sourceMul_eq_convolutionMul (a b : Ext3 F) :
    sourceMul a b = convolutionMul a b := by
  apply Ext3.ext <;> dsimp [sourceMul, convolutionMul] <;> ring

instance : Mul (Ext3 F) := ⟨sourceMul⟩

/-- Actual source mixed multiplication (lines 246–260). -/
instance : SMul F (Ext3 F) :=
  ⟨fun c a => ⟨c * a.c0, c * a.c1, c * a.c2⟩⟩

@[simp] theorem coeff_zero_block (i : Fin 3) : coeff (0 : Ext3 F) i = 0 := by
  fin_cases i <;> rfl

@[simp] theorem coeff_one_block (i : Fin 3) :
    coeff (1 : Ext3 F) i = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl

@[simp] theorem coeff_add (a b : Ext3 F) (i : Fin 3) :
    coeff (a + b) i = coeff a i + coeff b i := by
  fin_cases i <;> rfl

@[simp] theorem coeff_sub (a b : Ext3 F) (i : Fin 3) :
    coeff (a - b) i = coeff a i - coeff b i := by
  fin_cases i <;> rfl

@[simp] theorem coeff_neg (a : Ext3 F) (i : Fin 3) :
    coeff (-a) i = -coeff a i := by
  fin_cases i <;> rfl

@[simp] theorem coeff_smul (c : F) (a : Ext3 F) (i : Fin 3) :
    coeff (c • a) i = c * coeff a i := by
  fin_cases i <;> rfl

@[simp] theorem coeff_ofBase (c : F) (i : Fin 3) :
    coeff (ofBase c) i = if i = 0 then c else 0 := by
  fin_cases i <;> simp [coeff, ofBase]

@[simp] theorem ofBase_zero : ofBase (0 : F) = 0 := rfl
@[simp] theorem ofBase_one : ofBase (1 : F) = 1 := rfl

@[simp] theorem ofBase_add (a b : F) : ofBase (a + b) = ofBase a + ofBase b := by
  apply Ext3.ext
  · rfl
  · exact (add_zero (0 : F)).symm
  · exact (add_zero (0 : F)).symm

@[simp] theorem ofBase_sub (a b : F) : ofBase (a - b) = ofBase a - ofBase b := by
  apply Ext3.ext
  · rfl
  · exact (sub_self (0 : F)).symm
  · exact (sub_self (0 : F)).symm

@[simp] theorem ofBase_neg (a : F) : ofBase (-a) = -ofBase a := by
  apply Ext3.ext <;> simp [ofBase, Neg.neg]

 theorem mul_eq_convolutionMul (a b : Ext3 F) : a * b = convolutionMul a b :=
  sourceMul_eq_convolutionMul a b

@[simp] theorem ofBase_mul (a b : F) : ofBase (a * b) = ofBase a * ofBase b := by
  rw [mul_eq_convolutionMul]
  apply Ext3.ext <;> simp [ofBase, convolutionMul]

/-- Mixed extension/base addition changes only the constant coefficient. -/
theorem add_ofBase (a : Ext3 F) (c : F) :
    a + ofBase c = ⟨a.c0 + c, a.c1, a.c2⟩ := by
  apply Ext3.ext
  · rfl
  · exact add_zero a.c1
  · exact add_zero a.c2

 theorem sub_ofBase (a : Ext3 F) (c : F) :
    a - ofBase c = ⟨a.c0 - c, a.c1, a.c2⟩ := by
  apply Ext3.ext
  · rfl
  · exact sub_zero a.c1
  · exact sub_zero a.c2

 theorem ofBase_sub_block (c : F) (a : Ext3 F) :
    ofBase c - a = ⟨c - a.c0, -a.c1, -a.c2⟩ := by
  apply Ext3.ext
  · rfl
  · exact zero_sub a.c1
  · exact zero_sub a.c2

 theorem ofBase_mul_block (c : F) (a : Ext3 F) : ofBase c * a = c • a := by
  rw [mul_eq_convolutionMul]
  apply Ext3.ext <;> simp [ofBase, convolutionMul, HSMul.hSMul, SMul.smul]

 theorem mul_ofBase (a : Ext3 F) (c : F) : a * ofBase c = c • a := by
  rw [mul_eq_convolutionMul]
  apply Ext3.ext <;> simp [ofBase, convolutionMul, HSMul.hSMul, SMul.smul, mul_comm]

/-- Every source output block can be assembled by its coefficient function. -/
theorem mul_constructible (a b : Ext3 F) :
    a * b = ofFn (fun i => coeff (convolutionMul a b) i) := by
  rw [ofFn_coeff, mul_eq_convolutionMul]

end Ext3
end ZiskFv.AirsClean.Mem.Stage2
