import Karlin.PaperProof
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Finite differences recover the actual binomial coefficients

These elementary identities sit below the scale construction. They allow its
existing integer-valued-row specification to follow the finite-difference
argument in the manuscript without importing completed family constructions.
-/

namespace Karlin.FaithfulFiniteDifference
open scoped BigOperators

/-- The alternating finite sum for the iterated forward difference at zero. -/
theorem forward_difference_formula (f : ℕ → ℚ) (j : ℕ) :
    (fwdDiff 1)^[j] f 0 =
      ∑ h ∈ Finset.range (j + 1), (-1 : ℚ) ^ (j-h) * (j.choose h : ℚ) * f h := by
  simpa [zsmul_eq_mul] using fwdDiff_iter_eq_sum_shift (1 : ℕ) f j 0

theorem forward_difference_choose_zero (m j : ℕ) :
    (fwdDiff 1)^[j] (fun q : ℕ => (q.choose m : ℚ)) 0 =
      if j = m then 1 else 0 := by
  have h := fwdDiff_iter_choose_zero m j
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [zero_add, smul_eq_mul, mul_one] at h
  rw [forward_difference_formula]
  exact_mod_cast h

/-- Coefficient recovery for the given row, with no alternate interpolant. -/
theorem binomial_row_eq_forward_difference {w : ℕ} (row : Fin w → ℚ) (j : Fin w) :
    row j = (fwdDiff 1)^[j.val]
      (fun q : ℕ => ∑ i : Fin w, row i * (q.choose i.val : ℚ)) 0 := by
  have he : (fun q : ℕ => ∑ i : Fin w, row i * (q.choose i.val : ℚ)) =
      ∑ i : Fin w, row i • (fun q : ℕ => (q.choose i.val : ℚ)) := by
    ext q
    simp
  rw [he, fwdDiff_iter_finset_sum]
  simp only [fwdDiff_iter_const_smul, Finset.sum_apply, Pi.smul_apply,
    forward_difference_choose_zero, smul_eq_mul]
  symm
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hn : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
    simp [hn]
  · simp

end Karlin.FaithfulFiniteDifference
