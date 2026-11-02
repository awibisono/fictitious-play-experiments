import Karlin.FaithfulRateError
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Low-level polynomial routes used by the v15 constructors

This module sits below the lift. Its ordinary-power window summation and
backward-difference degree drop are used in the coefficient consumers, without
changing the binomial tables or the construction's data definitions.
-/
namespace Karlin.FaithfulPolynomialRoutes
open scoped BigOperators
open Polynomial Filter Topology Asymptotics
set_option maxHeartbeats 1500000

/-- Backward difference of the polynomial, at the manuscript's q and q-1. -/
noncomputable def backwardDifference (p : ℚ[X]) : ℚ[X] := p - taylor (-1) p

theorem backwardDifference_eval (p : ℚ[X]) (x : ℚ) :
    (backwardDifference p).eval x = p.eval x - p.eval (x-1) := by
  simp [backwardDifference, taylor_eval, sub_eq_add_neg]

theorem taylor_pred_coefficient (p : ℚ[X]) (hd : 0 < p.natDegree) (r : ℚ) :
    (taylor r p).coeff (p.natDegree-1) =
      p.coeff (p.natDegree-1) + (p.natDegree : ℚ) * p.leadingCoeff * r := by
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
theorem backwardDifference_degree_and_leading (p : ℚ[X]) (hd : 0 < p.natDegree) :
    (backwardDifference p).natDegree = p.natDegree-1 ∧
    (backwardDifference p).leadingCoeff = (p.natDegree : ℚ) * p.leadingCoeff := by
  have hc : (backwardDifference p).coeff (p.natDegree-1) =
      (p.natDegree : ℚ) * p.leadingCoeff := by
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

theorem polynomial_eq_of_eval_pos_nat (p q : ℚ[X])
    (h : ∀ n : ℕ, 1 ≤ n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => ((n+1 : ℕ) : ℚ)) := by
    intro a b hab
    exact Nat.add_right_cancel (Nat.cast_injective hab)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n, rfl⟩
  exact h (n+1) (by omega)


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


/-- Coefficient matching at any supplied degree bound, including vanishing
top coefficients. The nonconstant case uses the exact degree-drop theorem. -/
theorem backwardDifference_top_coefficient (p : ℚ[X]) {k : ℕ}
    (hk : 0 < k) (hp : p.natDegree ≤ k) :
    (backwardDifference p).coeff (k-1) = (k : ℚ) * p.coeff k := by
  by_cases hd : 0 < p.natDegree
  · obtain ⟨hdeg, hlead⟩ := backwardDifference_degree_and_leading p hd
    by_cases he : p.natDegree = k
    · rw [← he, ← hdeg, coeff_natDegree, hlead, coeff_natDegree]
    · have hlt : p.natDegree < k := by omega
      rw [coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  · have hp0 := eq_C_of_natDegree_le_zero (by omega : p.natDegree ≤ 0)
    rw [hp0]
    simp [backwardDifference, Polynomial.coeff_C, hk.ne']

theorem rowPoly_backwardDifference {w : ℕ} (row : Fin w → ℚ) :
    backwardDifference (FaithfulGrowth.rowPoly row) =
      FaithfulGrowth.rowPoly (Matrix.vecMul row (1 - B_mat w)) := by
  apply polynomial_eq_of_eval_pos_nat
  intro q hq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  rw [backwardDifference_eval]
  simp only [Nat.cast_succ, add_sub_cancel_right]
  rw [← Nat.cast_succ]
  simp only [FaithfulGrowth.rowPoly_eval_nat]
  change dotProduct row (binomBasis w (n+1)) - dotProduct row (binomBasis w n) =
    dotProduct (Matrix.vecMul row (1-B_mat w)) (binomBasis w (n+1))
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_dotProduct,
    ← Matrix.dotProduct_mulVec, B_mat_mulVec_binomBasis]

theorem rowPoly_increment_eq {k : ℕ} (chi : Fin k → ℚ) (tau : ℕ) (c : ℚ) :
    FaithfulGrowth.rowPoly
      (Matrix.vecMul chi (E_2tau_mat k tau - E_tau_mat k tau) + c • e0_row (k+1)) =
      (FaithfulGrowth.rowPoly chi).comp (C (2*(tau : ℚ))*X) -
      (FaithfulGrowth.rowPoly chi).comp (C (tau : ℚ)*X) + C c := by
  apply polynomial_eq_of_eval_pos_nat
  intro q _
  simp only [eval_add, eval_sub, eval_comp, eval_mul, eval_C, eval_X]
  have h1 := FaithfulGrowth.rowPoly_eval_nat chi (2*tau*q)
  have h2 := FaithfulGrowth.rowPoly_eval_nat chi (tau*q)
  push_cast at h1 h2
  rw [h1, h2, FaithfulGrowth.rowPoly_eval_nat]
  change dotProduct (Matrix.vecMul chi (E_2tau_mat k tau-E_tau_mat k tau) + c • e0_row (k+1))
    (binomBasis (k+1) q) =
      dotProduct chi (binomBasis k (2*tau*q)) - dotProduct chi (binomBasis k (tau*q)) + c
  rw [add_dotProduct, Matrix.vecMul_sub, sub_dotProduct,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, E_2tau_mat,
    E_tau_mat_mulVec_binomBasis, E_tau_mat_mulVec_binomBasis, smul_dotProduct]
  simp [dotProduct, e0_row, binomBasis]

/-- The ordinary-power and accumulated-error calculation for any polynomial. -/
theorem polynomial_bundle_expansion {d : ℕ} (hd : 1 ≤ d) (p : ℝ[X])
    (hp : p.natDegree ≤ d) (tau : ℕ) (htau : 0 < tau) :
    (fun q : ℕ => (∑ s ∈ Finset.Ico (tau*q) (2*tau*q), p.eval (s : ℝ)) -
      (p.coeff d * (tau : ℝ)^(d+1)*(2^(d+1)-1)/(d+1 : ℝ))*(q : ℝ)^(d+1))
      =O[atTop] (fun q : ℕ => (q : ℝ)^d) := by
  have hpow := (ordinary_power_bundle_expansion d tau).const_mul_left (p.coeff d)
  have hrem := polynomial_bundle_remainder hd p hp tau htau
  apply (hpow.add hrem).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [] with q
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Normalization of an ordinary-power expansion identifies the leading
coefficient. Used to recover the top entry of the unchanged count table. -/
theorem normalized_limit_of_expansion {f : ℕ → ℝ} {a : ℝ} {d : ℕ}
    (hd : 0 < d)
    (h : (fun q : ℕ => f q-a*(q : ℝ)^d) =O[atTop]
      (fun q : ℕ => (q : ℝ)^(d-1))) :
    Tendsto (fun q : ℕ => f q/(q : ℝ)^d) atTop (𝓝 a) := by
  have hlo : (fun q : ℕ => (q : ℝ)^(d-1)) =o[atTop] (fun q : ℕ => (q : ℝ)^d) :=
    (isLittleO_pow_pow_atTop_of_lt (by omega : d-1<d)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
  have hh := ((h.trans_isLittleO hlo).tendsto_div_nhds_zero).add_const a
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  field_simp
  ring

/-- The ordinary polynomial associated with the unchanged rational row. -/
noncomputable def realRow {w : ℕ} (row : Fin w → ℚ) : ℝ[X] :=
  (FaithfulGrowth.rowPoly row).map (Rat.castHom ℝ)

theorem realRow_eval {w : ℕ} (row : Fin w → ℚ) (q : ℕ) :
    (realRow row).eval (q : ℝ) = (dotProduct row (binomBasis w q) : ℚ) := by
  rw [realRow, eval_map, eval₂_at_natCast, FaithfulGrowth.rowPoly_eval_nat]
  rfl

theorem bundle_row_eval {k : ℕ} (row : Fin k → ℚ) (tau q : ℕ) :
    (dotProduct (Matrix.vecMul row (F_tau_mat k tau) + e0_row (k+1))
      (binomBasis (k+1) q) : ℚ) =
      (∑ s ∈ Finset.Ico (tau*q) (2*tau*q), (realRow row).eval (s : ℝ)) + 1 := by
  simp_rw [realRow_eval]
  have hQ : dotProduct (Matrix.vecMul row (F_tau_mat k tau) + e0_row (k+1))
      (binomBasis (k+1) q) =
      (∑ s ∈ Finset.Ico (tau*q) (2*tau*q), dotProduct row (binomBasis k s)) + 1 := by
    rw [add_dotProduct, ← Matrix.dotProduct_mulVec]
    have he : dotProduct (e0_row (k+1)) (binomBasis (k+1) q) = (1 : ℚ) := by
      simp [dotProduct, e0_row, binomBasis]
    rw [he]
    congr 1
    simp only [dotProduct, F_tau_mat_mulVec_binomBasis, Finset.mul_sum]
    exact Finset.sum_comm
  exact_mod_cast hQ

/-- Recover the actual bundle row's top coefficient from ordinary-power
summation and its accumulated lower-degree remainder, not transfer diagonals. -/
theorem bundle_row_top_coefficient {k : ℕ} (hk : 2 ≤ k) (row : Fin k → ℚ)
    (tau : ℕ) (htau : 0 < tau) :
    (Matrix.vecMul row (F_tau_mat k tau) + e0_row (k+1)) (Fin.last k) =
      row ⟨k-1, by omega⟩ * (tau : ℚ)^k * ((2 : ℚ)^k-1) := by
  let p := realRow row
  let g := Matrix.vecMul row (F_tau_mat k tau) + e0_row (k+1)
  have hp : p.natDegree ≤ k-1 :=
    (Polynomial.natDegree_map_le).trans (FaithfulGrowth.rowPoly_natDegree_le row)
  have hc : p.coeff (k-1) = (row ⟨k-1, by omega⟩ : ℝ)/((k-1).factorial : ℝ) := by
    rw [show p = realRow row from rfl, realRow, Polynomial.coeff_map,
      FaithfulGrowth.rowPoly_top_coeff (by omega : 0<k)]
    simp
  let a : ℝ := p.coeff (k-1)*(tau : ℝ)^k*(2^k-1)/(k : ℝ)
  have hsum := polynomial_bundle_expansion (by omega : 1 ≤ k-1) p hp tau htau
  have hone : (fun _q : ℕ => (1 : ℝ)) =O[atTop] (fun q : ℕ => (q : ℝ)^(k-1)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with q hq
    simpa using (one_le_pow₀ (by exact_mod_cast hq : (1 : ℝ) ≤ q) :
      (1 : ℝ) ≤ (q : ℝ)^(k-1))
  have hexp : (fun q : ℕ => (dotProduct g (binomBasis (k+1) q) : ℚ) - a*(q : ℝ)^k)
      =O[atTop] (fun q : ℕ => (q : ℝ)^(k-1)) := by
    apply (hsum.add hone).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [] with q
    rw [show g = Matrix.vecMul row (F_tau_mat k tau) + e0_row (k+1) from rfl,
      bundle_row_eval]
    simp only [show k-1+1=k by omega]
    have hcast : ((k-1 : ℕ) : ℝ)+1 = (k : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ k))
    rw [hcast]
    dsimp only [a, p]
    ring
  have hlim := normalized_limit_of_expansion (by omega : 0<k) hexp
  have hbin := FaithfulGrowth.fin_binomial_normalized_limit (Nat.succ_pos k) g
  have heq : (g (Fin.last k) : ℝ)/(k.factorial : ℝ) = a := by
    apply tendsto_nhds_unique _ hlim
    simpa only [Nat.add_sub_cancel] using hbin
  have hfac : (k.factorial : ℝ) = (k : ℝ)*((k-1).factorial : ℝ) := by
    conv_lhs => rw [show k=k-1+1 by omega, Nat.factorial_succ]
    push_cast
    congr 1
    exact_mod_cast (by omega : k-1+1=k)
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hfr : ((k-1).factorial : ℝ) ≠ 0 := by positivity
  have hreal : (g (Fin.last k) : ℝ) =
      (row ⟨k-1, by omega⟩ : ℝ)*(tau : ℝ)^k*(2^k-1) := by
    dsimp only [a] at heq
    rw [hc, hfac] at heq
    field_simp at heq
    nlinarith [heq]
  exact_mod_cast hreal

end Karlin.FaithfulPolynomialRoutes
