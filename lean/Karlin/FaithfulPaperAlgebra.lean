import Karlin.FaithfulGrowthRecurrences
import Karlin.FaithfulScaleClock
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.Bernoulli

/-!
# Polynomial proof steps in the v15 manuscript

These are additive proofs for the existing polynomial tables.  In particular,
the integrality argument below extracts the *actual* binomial row by iterated
forward differences, without the triangular-value induction in FaithfulScale.
-/

namespace Karlin.FaithfulPaperAlgebra

open scoped BigOperators
open Polynomial Filter Topology Asymptotics
open FaithfulScale FaithfulGrowthRecurrences

set_option maxHeartbeats 1500000

/-- The explicit finite-difference formula in the footnote following (maps). -/
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

/-- Forward differences recover the coefficients of the given row itself. -/
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

/-- Integrality from the finite-difference sum, independent of triangular inversion. -/
theorem binomial_row_integral_by_differences {w : ℕ} (row : Fin w → ℚ)
    (hvalues : ∀ q < w, IntegerMultiple 1
      (∑ i : Fin w, row i * (q.choose i.val : ℚ))) :
    ∀ j : Fin w, IntegerMultiple 1 (row j) := by
  intro j
  rw [binomial_row_eq_forward_difference row j, forward_difference_formula]
  apply integerMultiple_sum
  intro h hh
  obtain ⟨z, hz⟩ := hvalues h (by have := Finset.mem_range.mp hh; omega)
  refine ⟨(-1 : ℤ) ^ (j.val-h) * (j.val.choose h : ℤ) * z, ?_⟩
  simp [hz]

/-- The actual basis-change row is integral by the manuscript's difference formula. -/
theorem divided_power_to_binomial_integral_by_differences (w : ℕ)
    (ellhat : Fin w → ℚ)
    (hfactorial : ∀ i : Fin w, IntegerMultiple i.val.factorial (ellhat i)) :
    ∀ j : Fin w, IntegerMultiple 1 (Matrix.vecMul ellhat (S_inv_mat w) j) := by
  apply binomial_row_integral_by_differences
  intro q _
  change IntegerMultiple 1 (Matrix.vecMul ellhat (S_inv_mat w) ⬝ᵥ binomBasis w q)
  rw [← Matrix.dotProduct_mulVec, S_inv_mulVec_binomBasis]
  change IntegerMultiple 1 (∑ i : Fin w, ellhat i * ((q : ℚ)^i.val / i.val.factorial))
  apply integerMultiple_sum
  intro i _
  obtain ⟨z, hz⟩ := hfactorial i
  refine ⟨z * (q : ℤ)^i.val, ?_⟩
  have hfac : (i.val.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  rw [hz]
  push_cast
  field_simp

/-- The same denominator-clearing scale and same correction, using differences. -/
theorem correction_integral_by_differences (k : ℕ) (L : Fin (k+1) → ℚ[X])
    (hzero : L ⟨0, by omega⟩ = 0)
    (hvanish : ∀ (i : Fin (k+1)) r, r < i.val → (L i).coeff r = 0) :
    ∀ j : Fin (k+1), IntegerMultiple 1
      (Matrix.vecMul (fun i => (L i).eval (integerScale k L : ℚ)) (S_inv_mat (k+1)) j) :=
  divided_power_to_binomial_integral_by_differences (k+1) _
    (correction_factorial_integrality k L hzero hvanish)

/-- Backward difference of the polynomial, at the manuscript's q and q-1. -/
noncomputable def backwardDifference (p : ℝ[X]) : ℝ[X] := p - taylor (-1) p

theorem backwardDifference_eval (p : ℝ[X]) (x : ℝ) :
    (backwardDifference p).eval x = p.eval x - p.eval (x-1) := by
  simp [backwardDifference, taylor_eval, sub_eq_add_neg]

theorem taylor_pred_coefficient (p : ℝ[X]) (hd : 0 < p.natDegree) (r : ℝ) :
    (taylor r p).coeff (p.natDegree-1) =
      p.coeff (p.natDegree-1) + (p.natDegree : ℝ) * p.leadingCoeff * r := by
  rw [taylor_coeff]
  have hb : (hasseDeriv (p.natDegree-1) p).natDegree < 2 :=
    (natDegree_hasseDeriv_le _ _).trans_lt (by omega)
  rw [Polynomial.eval_eq_sum_range' hb]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul,
    pow_zero, mul_one, pow_one]
  have he : 1 + (p.natDegree-1) = p.natDegree := by omega
  rw [he, ← Nat.choose_symm (by omega : p.natDegree-1 ≤ p.natDegree),
    show p.natDegree - (p.natDegree-1) = 1 by omega, Nat.choose_one_right, coeff_natDegree]

/-- A nonconstant polynomial loses exactly one degree under backward difference. -/
theorem backwardDifference_degree_and_leading (p : ℝ[X]) (hd : 0 < p.natDegree) :
    (backwardDifference p).natDegree = p.natDegree-1 ∧
    (backwardDifference p).leadingCoeff = (p.natDegree : ℝ) * p.leadingCoeff := by
  have hc : (backwardDifference p).coeff (p.natDegree-1) =
      (p.natDegree : ℝ) * p.leadingCoeff := by
    rw [backwardDifference, coeff_sub, taylor_pred_coefficient p hd]
    ring
  have hp : p ≠ 0 := by intro h; simp [h] at hd
  have hcn : (backwardDifference p).coeff (p.natDegree-1) ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast hd.ne') (leadingCoeff_ne_zero.mpr hp)
  have hb : (backwardDifference p).natDegree ≤ p.natDegree-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n = p.natDegree
    · subst n
      simp [backwardDifference, coeff_taylor_natDegree]
    · have hn' : p.natDegree < n := by omega
      simp [backwardDifference, coeff_eq_zero_of_natDegree_lt hn',
        coeff_eq_zero_of_natDegree_lt (show (taylor (-1) p).natDegree < n by simpa)]
  have he := natDegree_eq_of_le_of_coeff_ne_zero hb hcn
  exact ⟨he, by rw [leadingCoeff, he, hc]⟩

theorem polynomial_eq_of_eval_pos_nat (p q : ℝ[X])
    (h : ∀ n : ℕ, 1 ≤ n → p.eval (n : ℝ) = q.eval (n : ℝ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => ((n+1 : ℕ) : ℝ)) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.cast_injective hab)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  exact h (n+1) (by omega)

open FaithfulClock

/-- The right side of the paper's height equation, in ordinary powers. -/
noncomputable def heightDifferencePoly {k : ℕ} (P : Clock k) (tau : ℕ) (c : ℝ) : ℝ[X] :=
  (realRowPoly (P.R P.b)).comp (C (2 * (tau : ℝ)) * X) -
  (realRowPoly (P.R P.b)).comp (C (tau : ℝ) * X) + C c

theorem heightDifferencePoly_eval {k : ℕ} (P : Clock k) (tau q : ℕ) (c : ℝ) :
    (heightDifferencePoly P tau c).eval (q : ℝ) =
      (P.entry (2*tau*q) P.b : ℝ) - (P.entry (tau*q) P.b : ℝ) + c := by
  simp only [heightDifferencePoly, eval_add, eval_sub, eval_comp, eval_mul, eval_C, eval_X]
  have h1 := realRowPoly_eval (by have := P.order_ge_two; omega : 0 < k)
    (P.R P.b) (2*tau*q)
  have h2 := realRowPoly_eval (by have := P.order_ge_two; omega : 0 < k)
    (P.R P.b) (tau*q)
  push_cast at h1 h2
  rw [h1, h2]
  rfl

theorem heightDifferencePoly_degree_and_leading {k : ℕ} (P : Clock k)
    (tau : ℕ) (htau : 0 < tau) (c : ℝ) :
    (heightDifferencePoly P tau c).natDegree = k-1 ∧
    (heightDifferencePoly P tau c).leadingCoeff =
      (k : ℝ) * (liftHeightLeading P tau : ℝ) := by
  have hk := P.order_ge_two
  have hp : (realRowPoly (P.R P.b)).natDegree ≤ k-1 :=
    FaithfulRateError.binomialPoly_natDegree_le _ _
  have htop : (realRowPoly (P.R P.b)).coeff (k-1) = (heightLeading P : ℝ) := by
    rw [realRowPoly, FaithfulRateError.binomialPoly_top_coeff]
    simp [heightLeading, leading, FaithfulRealization.extendRow, show k-1<k by omega]
  have hb : (heightDifferencePoly P tau c).natDegree ≤ k-1 := by
    unfold heightDifferencePoly
    rw [natDegree_add_C]
    apply (natDegree_sub_le_of_le (m := k-1) (n := k-1) ?_ ?_).trans
      (by simp : max (k-1) (k-1) ≤ k-1)
    · exact natDegree_comp_le.trans (by
        have hlin : (C (2 * (tau : ℝ)) * X).natDegree ≤ 1 :=
          (natDegree_C_mul_le _ _).trans natDegree_X_le
        simpa using Nat.mul_le_mul hp hlin)
    · exact natDegree_comp_le.trans (by
        have hlin : (C (tau : ℝ) * X).natDegree ≤ 1 :=
          (natDegree_C_mul_le _ _).trans natDegree_X_le
        simpa using Nat.mul_le_mul hp hlin)
  have hc : (heightDifferencePoly P tau c).coeff (k-1) =
      (k : ℝ) * (liftHeightLeading P tau : ℝ) := by
    simp only [heightDifferencePoly, coeff_add, coeff_sub, comp_C_mul_X_coeff,
      htop, coeff_C, if_neg (by omega : k-1 ≠ 0), add_zero]
    unfold liftHeightLeading
    push_cast
    rw [mul_pow]
    field_simp
  have hn : (heightDifferencePoly P tau c).coeff (k-1) ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast (show k ≠ 0 by omega))
      (by exact_mod_cast (liftHeightLeading_pos P tau htau).ne')
  have hd := natDegree_eq_of_le_of_coeff_ne_zero hb hn
  exact ⟨hd, by rw [leadingCoeff, hd, hc]⟩

/-- Step 4 of clockgrowth: degree drop forces degree k, and matching ordinary
leading coefficients forces the stated coefficient. No degree bound on z is assumed. -/
theorem height_polynomial_degree_by_backward_difference {k : ℕ} (P : Clock k)
    (tau : ℕ) (htau : 0 < tau) (c : ℝ) (z : ℝ[X])
    (hz : ∀ q : ℕ, 1 ≤ q → z.eval (q : ℝ) - z.eval ((q : ℝ)-1) =
      (P.entry (2*tau*q) P.b : ℝ) - (P.entry (tau*q) P.b : ℝ) + c) :
    z.natDegree = k ∧ z.leadingCoeff = (liftHeightLeading P tau : ℝ) := by
  have hk := P.order_ge_two
  have he : backwardDifference z = heightDifferencePoly P tau c := by
    apply polynomial_eq_of_eval_pos_nat
    intro q hq
    rw [backwardDifference_eval, heightDifferencePoly_eval]
    exact hz q hq
  obtain ⟨hrd, hrl⟩ := heightDifferencePoly_degree_and_leading P tau htau c
  have hzd : 0 < z.natDegree := by
    by_contra hn
    have hzC := eq_C_of_natDegree_le_zero (by omega : z.natDegree ≤ 0)
    have hzero : backwardDifference z = 0 := by rw [hzC]; simp [backwardDifference]
    rw [← he, hzero, natDegree_zero] at hrd
    omega
  obtain ⟨hdd, hdl⟩ := backwardDifference_degree_and_leading z hzd
  rw [he, hrd] at hdd
  have hdeg : z.natDegree = k := by omega
  rw [he, hrl, hdeg] at hdl
  exact ⟨hdeg, (mul_left_cancel₀ (by exact_mod_cast (show k ≠ 0 by omega)) hdl).symm⟩

/-- The manuscript's height asymptotic, proved via degree drop and ordinary
coefficient matching rather than the separately available recurrence solution. -/
theorem height_expansion_by_degree_drop {k : ℕ} (P : Clock k)
    (tau : ℕ) (htau : 0 < tau) (c : ℝ) (z : ℝ[X])
    (hz : ∀ q : ℕ, 1 ≤ q → z.eval (q : ℝ)-z.eval ((q : ℝ)-1) =
      (P.entry (2*tau*q) P.b : ℝ)-(P.entry (tau*q) P.b : ℝ)+c) :
    (fun q : ℕ => z.eval (q : ℝ)-(liftHeightLeading P tau : ℝ)*(q : ℝ)^k)
      =O[atTop] (fun q : ℕ => (q : ℝ)^(k-1)) := by
  obtain ⟨hd, hl⟩ := height_polynomial_degree_by_backward_difference P tau htau c z hz
  have hc : z.coeff k = (liftHeightLeading P tau : ℝ) := by
    simpa only [← hd, coeff_natDegree] using hl
  apply IsBigO.of_bound (FaithfulRateError.realCoeffMass z k)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
  have hb := FaithfulRateError.polynomial_remainder_bound z k hd.le (q : ℝ)
    (by exact_mod_cast hq)
  rw [hc] at hb
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) _)] using hb

/-- Ordinary-power antiderivative for integer summation (Faulhaber's formula). -/
noncomputable def powerSumPoly (d : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (d+1), monomial (d+1-i)
    (((_root_.bernoulli i : ℚ) : ℝ) * ((d+1).choose i : ℝ) / (d+1 : ℝ))

theorem powerSumPoly_eval (d n : ℕ) :
    (powerSumPoly d).eval (n : ℝ) = ∑ j ∈ Finset.range n, (j : ℝ)^d := by
  have h := _root_.sum_range_pow n d
  have hR : (∑ j ∈ Finset.range n, (j : ℝ)^d) =
      ∑ i ∈ Finset.range (d+1),
        (((_root_.bernoulli i : ℚ) : ℝ) * ((d+1).choose i : ℝ) *
          (n : ℝ)^(d+1-i) / (d+1 : ℝ)) := by exact_mod_cast h
  rw [hR]
  simp only [powerSumPoly, eval_finset_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem powerSumPoly_degree_le (d : ℕ) : (powerSumPoly d).natDegree ≤ d+1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (Nat.sub_le _ _)

theorem powerSumPoly_top (d : ℕ) : (powerSumPoly d).coeff (d+1) = 1/(d+1 : ℝ) := by
  simp only [powerSumPoly, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hn
    have hi' := Finset.mem_range.mp hi
    simp [show d+1-i ≠ d+1 by omega]
  · simp

noncomputable def powerBundlePoly (d tau : ℕ) : ℝ[X] :=
  (powerSumPoly d).comp (C (2 * (tau : ℝ)) * X) -
  (powerSumPoly d).comp (C (tau : ℝ) * X)

theorem powerBundlePoly_eval (d tau q : ℕ) :
    (powerBundlePoly d tau).eval (q : ℝ) =
      ∑ j ∈ Finset.Ico (tau*q) (2*tau*q), (j : ℝ)^d := by
  rw [Finset.sum_Ico_eq_sub _ (by nlinarith : tau*q ≤ 2*tau*q)]
  simp only [powerBundlePoly, eval_sub, eval_comp, eval_mul, eval_C, eval_X]
  have h1 := powerSumPoly_eval d (2*tau*q)
  have h2 := powerSumPoly_eval d (tau*q)
  push_cast at h1 h2
  rw [h1, h2]

theorem powerBundlePoly_degree_le (d tau : ℕ) :
    (powerBundlePoly d tau).natDegree ≤ d+1 := by
  apply (natDegree_sub_le_of_le (m := d+1) (n := d+1) ?_ ?_).trans (by simp)
  · exact natDegree_comp_le.trans (by
      have hlin : (C (2 * (tau : ℝ)) * X).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans natDegree_X_le
      simpa using Nat.mul_le_mul (powerSumPoly_degree_le d) hlin)
  · exact natDegree_comp_le.trans (by
      have hlin : (C (tau : ℝ) * X).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans natDegree_X_le
      simpa using Nat.mul_le_mul (powerSumPoly_degree_le d) hlin)

theorem powerBundlePoly_top (d tau : ℕ) :
    (powerBundlePoly d tau).coeff (d+1) =
      (tau : ℝ)^(d+1) * (2^(d+1)-1)/(d+1 : ℝ) := by
  simp only [powerBundlePoly, coeff_sub, comp_C_mul_X_coeff, powerSumPoly_top]
  rw [mul_pow]
  ring

/-- Step 3's leading-power sum over exactly [tau*q,2*tau*q). -/
theorem ordinary_power_bundle_expansion (d tau : ℕ) :
    (fun q : ℕ => (∑ j ∈ Finset.Ico (tau*q) (2*tau*q), (j : ℝ)^d) -
      ((tau : ℝ)^(d+1) * (2^(d+1)-1)/(d+1 : ℝ)) * (q : ℝ)^(d+1))
      =O[atTop] (fun q : ℕ => (q : ℝ)^d) := by
  apply IsBigO.of_bound (FaithfulRateError.realCoeffMass (powerBundlePoly d tau) (d+1))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
  have hb := FaithfulRateError.polynomial_remainder_bound (powerBundlePoly d tau) (d+1)
    (powerBundlePoly_degree_le d tau) (q : ℝ) (by exact_mod_cast hq)
  rw [powerBundlePoly_top, powerBundlePoly_eval] at hb
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) _)] using hb

open FaithfulScaleClock

/-- No symbolic assumptions remain: the actual parent's selected row is
integer valued by the forward-difference argument above. -/
theorem actual_correction_integral_by_differences {k : ℕ} (P : Clock k) (cref : ℚ) :
    ∀ j : Fin (k+1), IntegerMultiple 1
      (Matrix.vecMul
        (fun i => (correctionPolynomials P cref i).eval (chosenScale P cref : ℚ))
        (S_inv_mat (k+1)) j) := by
  apply correction_integral_by_differences k (correctionPolynomials P cref)
  · exact polynomialHelper_unselected k _ _ _ ⟨0, by omega⟩ (Or.inl (by simp)) (k-1)
  · intro i r hr
    apply Polynomial.X_pow_dvd_iff.mp ?_ r hr
    exact polynomialHelper_divisible k _ _ _
      (referencePivot_ne_zero k P.order_ge_two (scoreSummary P) P.leading_height.ne')
      (fun a b _ _ => referenceInterior_divisible k (momentSummary P)
        (lengthSummary P) (scoreSummary P) cref a b)
      (referencePsi_divisible k (scoreSummary P) cref) (k-1) i

/-- Integer numerator extraction, with correctness proved by the finite-difference
argument rather than the alternative integrality theorem. -/
theorem chosenCorrection_cast_by_differences {k : ℕ} (P : Clock k) (cref : ℚ)
    (j : Fin (k+1)) :
    (chosenCorrection P cref j : ℚ) =
      Matrix.vecMul
        (fun i => (correctionPolynomials P cref i).eval (chosenScale P cref : ℚ))
        (S_inv_mat (k+1)) j := by
  obtain ⟨z, hz⟩ := actual_correction_integral_by_differences P cref j
  have he : referenceCorrection k P.order_ge_two (momentSummary P)
      (lengthSummary P) (scoreSummary P) cref j = (z : ℚ) := by
    simpa only [Nat.cast_one, one_mul] using hz
  change ((referenceCorrection k P.order_ge_two (momentSummary P)
    (lengthSummary P) (scoreSummary P) cref j).num : ℚ) = _
  change ((referenceCorrection k P.order_ge_two (momentSummary P)
    (lengthSummary P) (scoreSummary P) cref j).num : ℚ) =
      referenceCorrection k P.order_ge_two (momentSummary P)
        (lengthSummary P) (scoreSummary P) cref j
  rw [he]
  simp

/-- Literal finite-difference formula for the unchanged chosen correction. -/
theorem chosenCorrection_forward_difference_formula {k : ℕ} (P : Clock k)
    (cref : ℚ) (j : Fin (k+1)) :
    (chosenCorrection P cref j : ℚ) =
      ∑ h ∈ Finset.range (j.val+1), (-1 : ℚ)^(j.val-h) * (j.val.choose h : ℚ) *
        (∑ i : Fin (k+1),
          (correctionPolynomials P cref i).eval (chosenScale P cref : ℚ) *
            ((h : ℚ)^i.val / i.val.factorial)) := by
  rw [chosenCorrection_cast_by_differences,
    binomial_row_eq_forward_difference
      (Matrix.vecMul (fun i => (correctionPolynomials P cref i).eval (chosenScale P cref : ℚ))
        (S_inv_mat (k+1))) j, forward_difference_formula]
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  change (Matrix.vecMul _ (S_inv_mat (k+1))) ⬝ᵥ binomBasis (k+1) h = _
  rw [← Matrix.dotProduct_mulVec, S_inv_mulVec_binomBasis]
  rfl

/-- The ordinary leading coefficients of the actual action-count polynomials
are nonnegative, as a consequence of eventual nonnegative actual word counts. -/
theorem phase_count_ordinary_coefficient_nonneg {k : ℕ} (P : Clock k) (i : Fin P.m) :
    0 ≤ (realRowPoly (P.countTable i)).coeff (k-1) := by
  rw [realRowPoly, FaithfulRateError.binomialPoly_top_coeff]
  have h := FaithfulGrowth.Clock.leading_count_nonneg P i
  have hk := P.order_ge_two
  simp only [FaithfulRealization.extendRow, dif_pos (by omega : k-1<k)]
  apply div_nonneg
  · exact_mod_cast h
  · positivity

/-- Full column rank makes the sum of those ordinary coefficients positive. -/
theorem phase_length_ordinary_coefficient_positive {k : ℕ} (P : Clock k) :
    0 < (realRowPoly (FaithfulGrowth.Clock.totalCountCoeff P)).coeff (k-1) := by
  rw [realRowPoly, FaithfulRateError.binomialPoly_top_coeff]
  have hk := P.order_ge_two
  simp only [FaithfulRealization.extendRow, dif_pos (by omega : k-1<k)]
  have hh := lengthLeading_pos P
  unfold lengthLeading leading at hh
  exact_mod_cast hh

/-- The sum of the lower-power errors across the moving window.  The number
of summands is tau*q, and every summand is bounded at 2*tau*q. -/
theorem polynomial_bundle_remainder {d : ℕ} (hd : 1 ≤ d) (p : ℝ[X])
    (hp : p.natDegree ≤ d) (tau : ℕ) (htau : 0 < tau) :
    (fun q : ℕ => ∑ s ∈ Finset.Ico (tau*q) (2*tau*q),
      (p.eval (s : ℝ) - p.coeff d * (s : ℝ)^d))
      =O[atTop] (fun q : ℕ => (q : ℝ)^d) := by
  let M := FaithfulRateError.realCoeffMass p d
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply IsBigO.of_bound (M * (tau : ℝ) * (2*(tau : ℝ))^(d-1))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (2*(tau : ℝ)*(q : ℝ))^(d-1) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 d)]
  calc
    |∑ s ∈ Finset.Ico (tau*q) (2*tau*q), (p.eval (s : ℝ)-p.coeff d*(s : ℝ)^d)|
        ≤ ∑ s ∈ Finset.Ico (tau*q) (2*tau*q), |p.eval (s : ℝ)-p.coeff d*(s : ℝ)^d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.Ico (tau*q) (2*tau*q), M*(2*(tau : ℝ)*(q : ℝ))^(d-1) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsI := Finset.mem_Ico.mp hs
      have hqle : q ≤ tau*q := Nat.le_mul_of_pos_left q htau
      have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (hq.trans (hqle.trans hsI.1))
      have hs2 : (s : ℝ) ≤ 2*(tau : ℝ)*(q : ℝ) := by exact_mod_cast hsI.2.le
      exact (FaithfulRateError.polynomial_remainder_bound p d hp _ hs1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs2 _) hM)
    _ = (M*(tau : ℝ)*(2*(tau : ℝ))^(d-1))*(q : ℝ)^d := by
      have hc : 2*tau*q-tau*q = tau*q := by
        rw [show 2*tau*q=tau*q+tau*q by ring, Nat.add_sub_cancel_left]
      simp only [Finset.sum_const, Nat.card_Ico, hc, nsmul_eq_mul, Nat.cast_mul]
      rw [mul_pow]
      have hpow : (q : ℝ)^d = (q : ℝ)^(d-1)*(q : ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      rw [hpow]
      ring

/-- Full Step 3 for the original phase words, using ordinary power sums plus
the separately bounded lower-order errors. -/
theorem clock_bundle_expansion_by_ordinary_powers {k : ℕ} (P : Clock k)
    (tau : ℕ) (htau : 0 < tau) :
    (fun q : ℕ => ((∑ s ∈ Finset.Ico (tau*q) (2*tau*q), (P.word s).length) : ℝ) -
      (bundleLeading P tau : ℝ)*(q : ℝ)^k)
      =O[atTop] (fun q : ℕ => (q : ℝ)^(k-1)) := by
  have hk := P.order_ge_two
  let p := realRowPoly (FaithfulGrowth.Clock.totalCountCoeff P)
  have hp : p.natDegree ≤ k-1 := FaithfulRateError.binomialPoly_natDegree_le _ _
  have hc : p.coeff (k-1) = (lengthLeading P : ℝ) := by
    rw [show p = realRowPoly (FaithfulGrowth.Clock.totalCountCoeff P) from rfl,
      realRowPoly, FaithfulRateError.binomialPoly_top_coeff]
    simp [lengthLeading, leading, FaithfulRealization.extendRow, show k-1<k by omega]
  have hpow := (ordinary_power_bundle_expansion (k-1) tau).const_mul_left (lengthLeading P : ℝ)
  have hrem := polynomial_bundle_remainder (by omega : 1 ≤ k-1) p hp tau htau
  apply (hpow.add hrem).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop P.Q] with q hq
  have hs (s : ℕ) (hmem : s ∈ Finset.Ico (tau*q) (2*tau*q)) :
      p.eval (s : ℝ) = ((P.word s).length : ℝ) := by
    have hqle : q ≤ tau*q := Nat.le_mul_of_pos_left q htau
    have hQs := hq.trans (hqle.trans (Finset.mem_Ico.mp hmem).1)
    have hl := FaithfulGrowth.Clock.lengthPoly_eval P s hQs
    rw [FaithfulGrowth.Clock.lengthPoly, FaithfulGrowth.rowPoly_eval_nat] at hl
    rw [show p = realRowPoly (FaithfulGrowth.Clock.totalCountCoeff P) from rfl,
      realRowPoly_eval (by omega : 0 < k)]
    exact_mod_cast hl
  simp only [hc, show k-1+1=k by omega]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsum : (∑ s ∈ Finset.Ico (tau*q) (2*tau*q), p.eval (s : ℝ)) =
      ((∑ s ∈ Finset.Ico (tau*q) (2*tau*q), (P.word s).length) : ℝ) := by
    exact Finset.sum_congr rfl hs
  rw [hsum]
  unfold bundleLeading
  push_cast
  rw [show ((k-1 : ℕ) : ℝ)+1 = (k : ℝ) by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ k))]
  ring

end Karlin.FaithfulPaperAlgebra
