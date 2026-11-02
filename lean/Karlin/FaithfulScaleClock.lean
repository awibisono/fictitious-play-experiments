import Karlin.FaithfulTables

/-!
# v15 integer scale and correction for an actual parent Clock

This module specializes the symbolic scale construction to the literal old
deficit and dyadic count tables.  It proves the integer-scale ingredient of
admissibility; it does not assert the separate positive-cone ingredient.
-/

namespace Karlin.FaithfulScaleClock

open scoped BigOperators Matrix
open FaithfulClock FaithfulScale FaithfulTables

variable {k : ℕ} (P : Clock k)

/-- The actual parent algebraic summary, with the scale still unchosen. -/
def momentSummary : Matrix (Fin k) (Fin k) ℚ := P.Rᵀ * P.countTable

def lengthSummary : Fin k → ℚ := Matrix.vecMul (fun _ => 1) P.countTable

def scoreSummary : Fin k → ℚ := P.R P.b

/-- The exact `DᵀX` has the reference interior after basis change.  The two
remaining summary products disappear because their support is on the boundary. -/
theorem DX_DP_interior (tau : ℕ) (c H delta : ℚ)
    (i j : Fin (k + 1)) (hi : 0 < i.val) (hj : 0 < j.val) :
    ((S_mat (k + 1))ᵀ * ((D P tau c H delta)ᵀ * X P tau) * S_mat (k + 1)) i j =
      (referenceInterior k (momentSummary P) (lengthSummary P) (scoreSummary P) c i j).eval (tau : ℚ) := by
  have href := congrArg (fun A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ => A i j)
    (referenceInterior_eval k tau (momentSummary P) (lengthSummary P) (scoreSummary P) c)
  dsimp only [Matrix.of_apply] at href
  rw [href, DX_summary]
  simp only [Matrix.mul_add, Matrix.add_mul, outerProd_basis_change,
    e0_vecMul_S, Matrix.add_apply]
  have hi0 : e0_row (k + 1) i = 0 := by simp [e0_row, Nat.ne_of_gt hi]
  have hj0 : e0_row (k + 1) j = 0 := by simp [e0_row, Nat.ne_of_gt hj]
  simp only [outerProd, Matrix.of_apply, hi0, hj0, zero_mul, mul_zero, add_zero]
  simp only [momentSummary, lengthSummary, scoreSummary, rationalL, FaithfulTables.L,
    f, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.vecMul_vecMul]

/-- The literal reference-height difference is the symbolic reference row
after evaluation and basis change; the height baseline cancels exactly. -/
theorem psi_DP (tau : ℕ) (c H : ℚ) :
    Matrix.vecMul (psi (scoreSummary P) tau c H) (S_mat (k + 1)) =
      (fun j => (referencePsi k (scoreSummary P) c j).eval (tau : ℚ)) := by
  rw [referencePsi_eval, psi_eq_neg_increment (by have := P.order_ge_two; omega)]
  congr 1
  ext j
  simp only [increment, Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-- The deterministic correction-polynomial family from the actual Clock. -/
noncomputable def correctionPolynomials (cref : ℚ) : Fin (k + 1) → Polynomial ℚ :=
  referenceSolver k P.order_ge_two (momentSummary P) (lengthSummary P) (scoreSummary P) cref

/-- Exactly the paper's general scale `D_* k!`, fixed before all later lift
parameters, phases, or times. -/
noncomputable def chosenScale (cref : ℚ) : ℕ := integerScale k (correctionPolynomials P cref)

/-- The deterministic integer correction row obtained by the same calculation. -/
noncomputable def chosenCorrection (cref : ℚ) : Fin (k + 1) → ℤ :=
  referenceCorrectionInt k P.order_ge_two (momentSummary P) (lengthSummary P) (scoreSummary P) cref

theorem chosenScale_pos (cref : ℚ) : 0 < chosenScale P cref :=
  integerScale_pos k (correctionPolynomials P cref)

/-- The existential integer-scale ingredient uses the actual old-action
deficit and counts, at the specified reference height `Arem+3`.  Its scale is
the deterministic one above and does not depend on `delta`. -/
theorem integer_scale_actual_tables (cref delta : ℚ) :
    0 < chosenScale P cref ∧ ∃ ell : Fin (k + 1) → ℤ,
      ∀ h, k < h → h ≤ 2 * k → Even h →
        matInnerProd (Z_binom (S_mat (k + 1)) h)
          ((D P (chosenScale P cref) cref (P.Arem + 3) delta)ᵀ * X P (chosenScale P cref) -
            outerProd (fun j => (ell j : ℚ))
              (psi (scoreSummary P) (chosenScale P cref) cref (P.Arem + 3))) = 0 := by
  exact reference_integer_scale_for_tables k P.order_ge_two
    (momentSummary P) (lengthSummary P) (scoreSummary P) cref
    (ne_of_gt P.leading_height)
    (fun tau => (D P tau cref (P.Arem + 3) delta)ᵀ * X P tau)
    (fun tau => psi (scoreSummary P) tau cref (P.Arem + 3))
    (fun tau _ i j hi hj => DX_DP_interior P tau cref (P.Arem + 3) delta i j hi hj)
    (fun tau _ j _ => congrFun (psi_DP P tau cref (P.Arem + 3)) j)

/-- The predetermined integer row reconstructs the very same divided-power
solution used to select the scale. -/
theorem chosenCorrection_DP (cref : ℚ) :
    Matrix.vecMul (fun j => (chosenCorrection P cref j : ℚ)) (S_mat (k + 1)) =
      (fun j => (correctionPolynomials P cref j).eval (chosenScale P cref : ℚ)) := by
  have hcast : (fun j => (chosenCorrection P cref j : ℚ)) =
      referenceCorrection k P.order_ge_two (momentSummary P) (lengthSummary P) (scoreSummary P) cref :=
    funext (referenceCorrectionInt_cast k P.order_ge_two (momentSummary P) (lengthSummary P)
      (scoreSummary P) cref (ne_of_gt P.leading_height))
  rw [hcast, referenceCorrection, Matrix.vecMul_vecMul, S_inv_mat_mul_S_mat, Matrix.vecMul_one]
  rfl

/-- Every higher test holds for the predetermined integer correction, for
every height baseline and translation parameter after the same scale is fixed.
No newly selected existential correction is substituted here. -/
theorem chosenCorrection_higher_tests (cref H delta : ℚ) (h : ℕ)
    (hkh : k < h) (hht : h ≤ 2 * k) (heven : Even h) :
    matInnerProd (Z_binom (S_mat (k + 1)) h)
      ((D P (chosenScale P cref) cref H delta)ᵀ * X P (chosenScale P cref) -
        outerProd (fun j => (chosenCorrection P cref j : ℚ))
          (psi (scoreSummary P) (chosenScale P cref) cref H)) = 0 := by
  obtain ⟨_, ell, hell, htests⟩ := reference_integer_scale k P.order_ge_two
    (momentSummary P) (lengthSummary P) (scoreSummary P) cref (ne_of_gt P.leading_height)
  have htest := htests h hkh hht heven
  rw [hell] at htest
  rw [matInnerProd_Z_binom_eq_Z_DP, Matrix.mul_sub, Matrix.sub_mul,
    outerProd_basis_change, chosenCorrection_DP, psi_DP]
  calc
    matInnerProd (Z_DP (k + 1) h)
        ((S_mat (k + 1))ᵀ * ((D P (chosenScale P cref) cref H delta)ᵀ * X P (chosenScale P cref)) *
            S_mat (k + 1) -
          outerProd (fun j => (correctionPolynomials P cref j).eval (chosenScale P cref : ℚ))
            (fun j => (referencePsi k (scoreSummary P) cref j).eval (chosenScale P cref : ℚ))) =
      matInnerProd (Z_DP (k + 1) h)
        ((Matrix.of fun i j =>
          (referenceInterior k (momentSummary P) (lengthSummary P) (scoreSummary P) cref i j).eval
            (chosenScale P cref : ℚ)) -
          outerProd (fun j => (correctionPolynomials P cref j).eval (chosenScale P cref : ℚ))
            (fun j => (referencePsi k (scoreSummary P) cref j).eval (chosenScale P cref : ℚ))) := by
      apply higher_test_congr_interior hkh
      intro i j hi hj
      simp only [Matrix.sub_apply, Matrix.of_apply]
      rw [DX_DP_interior P (chosenScale P cref) cref H delta i j hi hj]
    _ = 0 := htest

/-- The integer-data ingredient of v15 admissibility, at the mandated baseline.
The remaining positive-weight ingredient of admissibility is separate. -/
theorem baseline_integer_data (cref : ℚ) :
    1 ≤ chosenScale P cref ∧ ∀ delta : ℚ, ∀ h,
      k < h → h ≤ 2 * k → Even h →
        matInnerProd (Z_binom (S_mat (k + 1)) h)
          ((D P (chosenScale P cref) cref (P.Arem + 3) delta)ᵀ * X P (chosenScale P cref) -
            outerProd (fun j => (chosenCorrection P cref j : ℚ))
              (psi (scoreSummary P) (chosenScale P cref) cref (P.Arem + 3))) = 0 :=
  ⟨chosenScale_pos P cref, fun delta h hkh hht heven =>
    chosenCorrection_higher_tests P cref (P.Arem + 3) delta h hkh hht heven⟩

/-- Across actual parent clocks, the predetermined scale and integer row use
only the invariant algebraic summaries specified in v15.  Clocks may have
different action counts; the summary dimensions depend only on their order. -/
theorem chosen_pair_summary_independent (Q : Clock k) (c c' : ℚ)
    (hM : ∀ a b, 0 < a.val → momentSummary P a b = momentSummary Q a b)
    (hlen : lengthSummary P = lengthSummary Q)
    (hchi : ∀ a, 0 < a.val → scoreSummary P a = scoreSummary Q a) :
    chosenScale P c = chosenScale Q c' ∧ chosenCorrection P c = chosenCorrection Q c' := by
  unfold chosenScale correctionPolynomials chosenCorrection
  rw [← hlen]
  exact referenceCorrectionInt_scale_independent k P.order_ge_two
    (momentSummary P) (momentSummary Q) (lengthSummary P) (scoreSummary P) (scoreSummary Q)
    c c' hM hchi

#print axioms DX_DP_interior
#print axioms chosenCorrection_DP
#print axioms chosenCorrection_higher_tests
#print axioms baseline_integer_data
#print axioms chosen_pair_summary_independent

end Karlin.FaithfulScaleClock
