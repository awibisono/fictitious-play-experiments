import Karlin.FaithfulGramSection

/-!
# Executable rational Gram inverse

Mathlib's generic matrix inverse instance uses Ring.inverse and is marked
noncomputable. Over the rationals, determinant division and the adjugate give
an executable implementation, provably equal to that exact matrix inverse.
-/
namespace Karlin.FaithfulEffectiveGram
open scoped Matrix

variable {m w : Type*} [Fintype m] [Fintype w] [DecidableEq w]

def inverse (A : Matrix w w ℚ) : Matrix w w ℚ := A.det⁻¹ • A.adjugate

/-- Equality holds also on singular matrices, where both definitions are zero. -/
theorem inverse_eq (A : Matrix w w ℚ) : inverse A = A⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/-- Computable literal LX = X (Xᵀ X)⁻¹ from a finite rational matrix. -/
def gramLX (X : Matrix m w ℚ) : Matrix m w ℚ := X * inverse (Xᵀ * X)

theorem gramLX_eq (X : Matrix m w ℚ) : gramLX X = X * (Xᵀ * X)⁻¹ := by
  rw [gramLX, inverse_eq]

theorem gramLX_eq_prescribed (X : Matrix m w ℚ) :
    gramLX X = FaithfulGramSection.gramLX X := gramLX_eq X

/-- Kernel-proved compiler replacement for the mathematical Gram section. -/
@[csimp] theorem gramLX_csimp : @FaithfulGramSection.gramLX = @gramLX := by
  funext m w _ _ _ X
  exact (gramLX_eq_prescribed X).symm

theorem gramLX_spec (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : Xᵀ * gramLX X = 1 := by
  rw [gramLX_eq_prescribed]
  exact FaithfulGramSection.gramLX_spec X hX

theorem gramLX_transpose_spec (X : Matrix m w ℚ)
    (hX : Function.Injective (fun x => X.mulVec x)) : (gramLX X)ᵀ * X = 1 := by
  rw [gramLX_eq_prescribed]
  exact FaithfulGramSection.gramLX_transpose_spec X hX

end Karlin.FaithfulEffectiveGram
