import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The prescribed rational Gram section

The v15 manuscript fixes LX = X (Xᵀ X)⁻¹ after its interpolation lemma.
Full column rank suffices over the rationals: the Gram matrix has the same
kernel as X, since a rational sum of squares vanishes only at zero.
-/
namespace Karlin.FaithfulGramSection
open scoped Matrix

variable {m w : Type*} [Fintype m] [Fintype w] [DecidableEq w]

def actualGram (X : Matrix m w ℚ) : Matrix w w ℚ := Xᵀ * X

omit [Fintype w] [DecidableEq w] in
theorem actualGram_symmetric (X : Matrix m w ℚ) : (actualGram X)ᵀ = actualGram X := by
  simp only [actualGram, Matrix.transpose_mul, Matrix.transpose_transpose]

omit [DecidableEq w] in
theorem actualGram_injective (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) :
    Function.Injective (fun x => (actualGram X).mulVec x) := by
  have hker : LinearMap.ker X.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hX
  have hgker : LinearMap.ker (actualGram X).mulVecLin = ⊥ :=
    (Matrix.ker_mulVecLin_transpose_mul_self X).trans hker
  exact LinearMap.ker_eq_bot.mp hgker

theorem actualGram_isUnit (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : IsUnit (actualGram X) :=
  Matrix.mulVec_injective_iff_isUnit.mp (actualGram_injective X hX)

theorem actualGram_det_ne_zero (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : (actualGram X).det ≠ 0 := by
  have hunit : IsUnit (actualGram X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (actualGram_isUnit X hX)
  exact isUnit_iff_ne_zero.mp hunit

theorem actualGram_mul_inv (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : actualGram X * (actualGram X)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (actualGram_det_ne_zero X hX))

theorem actualGram_inv_mul (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : (actualGram X)⁻¹ * actualGram X = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (actualGram_det_ne_zero X hX))

/-- Literal v15 choice, with no arbitrary left-inverse selection. -/
noncomputable def gramLX (X : Matrix m w ℚ) : Matrix m w ℚ :=
  X * (Xᵀ * X)⁻¹

theorem gramLX_spec (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : Xᵀ * gramLX X = 1 := by
  rw [gramLX, ← Matrix.mul_assoc]
  exact actualGram_mul_inv X hX

theorem gramLX_transpose_spec (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : (gramLX X)ᵀ * X = 1 := by
  have h := congrArg Matrix.transpose (gramLX_spec X hX)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using h

end Karlin.FaithfulGramSection
