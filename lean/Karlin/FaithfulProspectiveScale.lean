import Karlin.FaithfulScale

/-!
# Canonical higher tests before constructing the next clock

The input is only the finite algebraic summary (M, lengthRow, chi). The scale
and integer row are the same canonical outputs of FaithfulScale throughout.
The table interface assumes exact coordinate identities, not a solution,
compatibility, or an already constructed next Clock.
-/
namespace Karlin.FaithfulProspectiveScale
open scoped BigOperators Matrix
open FaithfulScale

/-- The predetermined integer row reconstructs the selected polynomial row
in divided-power coordinates for an arbitrary algebraic summary. -/
theorem canonicalCorrection_DP (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    let L := referenceSolver k hk M lengthRow chi cref
    let tau := integerScale k L
    Matrix.vecMul (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ))
      (S_mat (k + 1)) = (fun j => (L j).eval (tau : ℚ)) := by
  intro L tau
  have hcast : (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ)) =
      referenceCorrection k hk M lengthRow chi cref :=
    funext (referenceCorrectionInt_cast k hk M lengthRow chi cref hchi)
  rw [hcast, referenceCorrection, Matrix.vecMul_vecMul, S_inv_mat_mul_S_mat,
    Matrix.vecMul_one]

/-- The same fixed integer correction satisfies all higher divided-power
tests. There is no replacement by a newly chosen existential integer row. -/
theorem canonicalCorrection_DP_higher_tests (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0) :
    let L := referenceSolver k hk M lengthRow chi cref
    let tau := integerScale k L
    0 < tau ∧ ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_DP (k + 1) h)
        ((Matrix.of fun i j => (referenceInterior k M lengthRow chi cref i j).eval (tau : ℚ)) -
          outerProd
            (Matrix.vecMul (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ))
              (S_mat (k + 1)))
            (fun j => (referencePsi k chi cref j).eval (tau : ℚ))) = 0 := by
  intro L tau
  obtain ⟨htau, ell, hell, htests⟩ := reference_integer_scale k hk M lengthRow chi cref hchi
  refine ⟨htau, ?_⟩
  intro h hkh hht heven
  have htest := htests h hkh hht heven
  rw [hell] at htest
  rw [canonicalCorrection_DP k hk M lengthRow chi cref hchi]
  exact htest

/-- Pointwise transfer at the canonical scale needs only the interior
summary identities. Boundary values of either table are unrestricted. -/
theorem canonicalCorrection_higher_tests_at_scale (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0)
    (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (psi : Fin (k + 1) → ℚ)
    (hF : ∀ i j : Fin (k + 1), 0 < i.val → 0 < j.val →
      ((S_mat (k + 1)).transpose * F * S_mat (k + 1)) i j =
        (referenceInterior k M lengthRow chi cref i j).eval
          (integerScale k (referenceSolver k hk M lengthRow chi cref) : ℚ))
    (hpsi : ∀ j : Fin (k + 1), 0 < j.val →
      Matrix.vecMul psi (S_mat (k + 1)) j = (referencePsi k chi cref j).eval
        (integerScale k (referenceSolver k hk M lengthRow chi cref) : ℚ)) :
    ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom (S_mat (k + 1)) h)
        (F - outerProd (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ)) psi) = 0 := by
  intro h hkh hht heven
  obtain ⟨_, htests⟩ := canonicalCorrection_DP_higher_tests k hk M lengthRow chi cref hchi
  rw [matInnerProd_Z_binom_eq_Z_DP, Matrix.mul_sub, Matrix.sub_mul, outerProd_basis_change]
  calc
    matInnerProd (Z_DP (k + 1) h)
        ((S_mat (k + 1)).transpose * F * S_mat (k + 1) -
          outerProd
            (Matrix.vecMul (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ))
              (S_mat (k + 1)))
            (Matrix.vecMul psi (S_mat (k + 1)))) =
      matInnerProd (Z_DP (k + 1) h)
        ((Matrix.of fun i j => (referenceInterior k M lengthRow chi cref i j).eval
          (integerScale k (referenceSolver k hk M lengthRow chi cref) : ℚ)) -
          outerProd
            (Matrix.vecMul (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ))
              (S_mat (k + 1)))
            (fun j => (referencePsi k chi cref j).eval
              (integerScale k (referenceSolver k hk M lengthRow chi cref) : ℚ))) := by
      apply higher_test_congr_interior hkh
      intro i j hi hj
      simp only [Matrix.sub_apply, outerProd, Matrix.of_apply]
      rw [hF i j hi hj, hpsi j hj]
    _ = 0 := htests h hkh hht heven

/-- Family interface matching reference_integer_scale_for_tables, but with
the canonical integer correction as the output rather than an existential
row that could be selected after a later parameter. -/
theorem canonicalCorrection_higher_tests_for_tables (k : ℕ) (hk : 2 ≤ k)
    (M : Matrix (Fin k) (Fin k) ℚ) (lengthRow chi : Fin k → ℚ) (cref : ℚ)
    (hchi : chi ⟨k - 1, by omega⟩ ≠ 0)
    (F : ℕ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (psi : ℕ → Fin (k + 1) → ℚ)
    (hF : ∀ tau : ℕ, 0 < tau → ∀ i j : Fin (k + 1), 0 < i.val → 0 < j.val →
      ((S_mat (k + 1)).transpose * F tau * S_mat (k + 1)) i j =
        (referenceInterior k M lengthRow chi cref i j).eval (tau : ℚ))
    (hpsi : ∀ tau : ℕ, 0 < tau → ∀ j : Fin (k + 1), 0 < j.val →
      Matrix.vecMul (psi tau) (S_mat (k + 1)) j = (referencePsi k chi cref j).eval (tau : ℚ)) :
    let L := referenceSolver k hk M lengthRow chi cref
    let tau := integerScale k L
    0 < tau ∧ ∀ h, k < h → h ≤ 2 * k → Even h →
      matInnerProd (Z_binom (S_mat (k + 1)) h)
        (F tau - outerProd (fun j => (referenceCorrectionInt k hk M lengthRow chi cref j : ℚ))
          (psi tau)) = 0 := by
  intro L tau
  have htau : 0 < tau := integerScale_pos k L
  exact ⟨htau, canonicalCorrection_higher_tests_at_scale k hk M lengthRow chi cref hchi
    (F tau) (psi tau) (hF tau htau) (hpsi tau htau)⟩

end Karlin.FaithfulProspectiveScale
