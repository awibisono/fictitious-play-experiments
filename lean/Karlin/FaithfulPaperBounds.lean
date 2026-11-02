import Karlin.FaithfulAppendixBounds
import Karlin.FaithfulRealization

/-!
# Literal intermediate estimates in the v15 proof

The internal estimate below controls the sum of the two norms, as displayed
in the proof of the uniform-bounds lemma.  The endpoint estimates apply to the
phase times and heights of the same canonical clock realization.
-/

namespace Karlin.FaithfulPaperBounds

open scoped BigOperators Matrix
open Faithful FaithfulAppendix

/-- The two internal terms separately retain the sharper `1/(T1*T2)` scale.
Only the bound on `Z/T2` is used, so this applies to either count block. -/
theorem internal_norm_sum_bound {r w : Type*} [Fintype r] [Fintype w]
    [Nonempty r] [Nonempty w] (Z : Matrix r w ℚ) (L : Matrix r r ℚ)
    (B : Matrix w w ℚ) (T1 T2 C : ℚ) (ht1 : 0 < T1) (ht2 : 0 < T2)
    (hz : normStar Z ≤ T2 * C) :
    normStar ((1 / (T1 * T2 ^ 2)) • (L * Z)) +
      normStar ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
      normStar L * C * (1 + normStar B) / (T1 * T2) := by
  have hlz := mul_bound L Z _ _ le_rfl hz
  have hltz := mul_bound Lᵀ Z _ _ (transpose L).le hz
  have hlb := mul_bound (Lᵀ * Z) B _ _ hltz le_rfl
  have heta : 0 < 1 / (T1 * T2 ^ 2) := by positivity
  have h1 := smul_le (1 / (T1 * T2 ^ 2)) (L * Z)
  have h2 := smul_le (1 / (T1 * T2 ^ 2)) (Lᵀ * Z * B)
  rw [abs_of_pos heta] at h1 h2
  calc
    _ ≤ (1 / (T1 * T2 ^ 2)) *
        (normStar (L * Z) + normStar (Lᵀ * Z * B)) := by linarith
    _ ≤ (1 / (T1 * T2 ^ 2)) *
        (normStar L * (T2 * C) + (normStar L * (T2 * C)) * normStar B) :=
      mul_le_mul_of_nonneg_left (add_le_add hlz hlb) heta.le
    _ = _ := by field_simp

/-- The same sum of norms is `O(T1⁻²)` once `T2 ≥ T1`. -/
theorem internal_norm_sum_square_bound {r w : Type*} [Fintype r] [Fintype w]
    [Nonempty r] [Nonempty w] (Z : Matrix r w ℚ) (L : Matrix r r ℚ)
    (B : Matrix w w ℚ) (T1 T2 C : ℚ) (ht1 : 0 < T1) (ht2 : T1 ≤ T2)
    (hz : normStar Z ≤ T2 * C) :
    normStar ((1 / (T1 * T2 ^ 2)) • (L * Z)) +
      normStar ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
      normStar L * C * (1 + normStar B) / T1 ^ 2 := by
  have ht2p : 0 < T2 := ht1.trans_le ht2
  have hC : 0 ≤ C := by nlinarith [nonneg Z]
  have hn : 0 ≤ normStar L * C * (1 + normStar B) :=
    mul_nonneg (mul_nonneg (nonneg L) hC) (by linarith [nonneg B])
  exact (internal_norm_sum_bound Z L B T1 T2 C ht1 ht2p hz).trans
    (div_le_div_of_nonneg_left hn (sq_pos_of_pos ht1) (by nlinarith))

/-- Both literal count blocks satisfy the displayed internal estimate in the
paper's `normStar`, with the very same candidate-dependent constant `bC`. -/
theorem count_block_internal_bounds (k : ℕ) (T1 T2 lam : ℚ)
    (z ell : Fin (k + 1) → ℚ) (L B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (ht1 : 0 < T1) (ht2 : T1 ≤ T2) :
    ∀ Z ∈ ({W_concrete k T1 T2 lam z,
        WE_concrete k T1 T2 lam z (earlyUnit k) ell} :
        Set (Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)),
      normStar ((1 / (T1 * T2 ^ 2)) • (L * Z)) +
        normStar ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
        normStar L * bC k T1 lam z ell * (1 + normStar B) / (T1 * T2) ∧
      normStar ((1 / (T1 * T2 ^ 2)) • (L * Z)) +
        normStar ((1 / (T1 * T2 ^ 2)) • (Lᵀ * Z * B)) ≤
        normStar L * bC k T1 lam z ell * (1 + normStar B) / T1 ^ 2 := by
  intro Z hZ
  obtain ⟨hw, hwe⟩ := count_bounds k T1 T2 lam z ell ht1 ht2
  have hz : normStar Z ≤ T2 * bC k T1 lam z ell := by
    rcases hZ with rfl | hZ
    · exact hw
    · exact hZ ▸ hwe
  exact ⟨internal_norm_sum_bound Z L B T1 T2 _ ht1 (ht1.trans_le ht2) hz,
    internal_norm_sum_square_bound Z L B T1 T2 _ ht1 ht2 hz⟩

open Filter Topology Polynomial Asymptotics FaithfulRateError

/-- The explicit polynomial remainder gives the normalized `O(1/q)` error. -/
theorem polynomial_normalized_isBigO (P : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdegree : P.natDegree = d) :
    (fun q : ℕ => P.eval (q : ℝ) / (q : ℝ) ^ d - P.leadingCoeff)
      =O[atTop] (fun q : ℕ => 1 / (q : ℝ)) := by
  apply IsBigO.of_bound (realCoeffMass P d)
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h := polynomial_normalized_error P hd hdegree.le (q : ℝ) hq1
  rw [show P.coeff d = P.leadingCoeff by rw [← hdegree, Polynomial.coeff_natDegree]] at h
  simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / q),
    mul_one_div] using h

/-- A positive-leading-coefficient polynomial has adjacent values in the ratio
`1 + O(1/q)`.  The denominator is justified by its positive normalized limit. -/
theorem polynomial_successor_ratio_error (P : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdegree : P.natDegree = d) (hc : 0 < P.leadingCoeff) :
    (fun q : ℕ => P.eval ((q : ℝ) + 1) / P.eval (q : ℝ) - 1)
      =O[atTop] (fun q : ℕ => 1 / (q : ℝ)) := by
  let S := P.comp (Polynomial.X + Polynomial.C 1)
  have hSdegree : S.natDegree = d := by
    dsimp [S]
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, hdegree, mul_one]
  have hScoeff : S.leadingCoeff = P.leadingCoeff := by
    dsimp [S]
    rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; norm_num),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have hp : P ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hc.ne'
  have hs : S ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp (by rw [hScoeff]; exact hc.ne')
  have hPdeg : P.degree = d := by rw [Polynomial.degree_eq_natDegree hp, hdegree]
  have hSdeg : S.degree = d := by rw [Polynomial.degree_eq_natDegree hs, hSdegree]
  have hPlim := FaithfulRate.polynomial_normalized_limit P d hPdeg
  have hSlim := FaithfulRate.polynomial_normalized_limit S d hSdeg
  rw [hScoeff] at hSlim
  have hPerr := polynomial_normalized_isBigO P hd hdegree
  have hSerr := polynomial_normalized_isBigO S hd hSdegree
  rw [hScoeff] at hSerr
  have h := quotient_error_isBigO (p := 1) hc hSlim hPlim hSerr hPerr
  apply (h.const_mul_left (1 / 2 : ℝ)).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1,
    hPlim.eventually (lt_mem_nhds hc)] with q hq hpos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqne : (q : ℝ) ^ d ≠ 0 := (pow_pos hqpos d).ne'
  have hPne : P.eval (q : ℝ) ≠ 0 := by
    intro hz
    simp [hz] at hpos
  simp only [Real.rpow_one, S, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  field_simp

open FaithfulRealization

/-- The two phase-boundary ratios used in the proof of `lem:alltime`, for
the actual setup trajectory of any clock, including its fixed starting phase.
Neither ratio is an assumed asymptotic input. -/
theorem clock_phase_boundary_ratios {k : ℕ} (P : FaithfulClock.Clock k) :
    ((fun q : ℕ => (phaseTime P (q + 1) : ℝ) / (phaseTime P q : ℝ) - 1)
      =O[atTop] (fun q : ℕ => 1 / (q : ℝ))) ∧
    ((fun q : ℕ =>
        (cumScore (game P) (play P) (phaseTime P (q + 1))
          (play P (phaseTime P (q + 1))) : ℝ) /
        (cumScore (game P) (play P) (phaseTime P q) (play P (phaseTime P q)) : ℝ) - 1)
      =O[atTop] (fun q : ℕ => 1 / (q : ℝ))) := by
  have hk := P.order_ge_two
  have hkm1 : k - 1 + 1 = k := by omega
  have htop : k - 1 < k := by omega
  have hL : 0 < countCoeff P (k - 1) := by
    simp only [countCoeff, extendRow, dif_pos htop]
    exact_mod_cast FaithfulGrowth.Clock.leading_total_count_pos P
  have hxi : 0 < scoreCoeff P (k - 1) := by
    simp only [scoreCoeff, extendRow, dif_pos htop]
    exact_mod_cast P.leading_height
  let TP := phaseTimePoly (countCoeff P) (k - 1) P.Q
  let HP := phaseHeightPoly (scoreCoeff P) (k - 1) P.Q
    ((bias P P.b + shift P : ℚ) : ℝ)
  obtain ⟨htdeg, htcoeff⟩ := phaseTimePoly_degree_coeff
    (countCoeff P) (k - 1) P.Q hL.ne'
  obtain ⟨hhdeg, hhcoeff⟩ := phaseHeightPoly_degree_coeff (scoreCoeff P)
    (by omega : 0 < k - 1) P.Q ((bias P P.b + shift P : ℚ) : ℝ) hxi.ne'
  rw [hkm1] at htdeg htcoeff
  have htpos : 0 < TP.leadingCoeff := by
    change 0 < (phaseTimePoly (countCoeff P) (k - 1) P.Q).leadingCoeff
    rw [htcoeff]
    positivity
  have hhpos : 0 < HP.leadingCoeff := by
    change 0 < (phaseHeightPoly (scoreCoeff P) (k - 1) P.Q
      ((bias P P.b + shift P : ℚ) : ℝ)).leadingCoeff
    rw [hhcoeff]
    positivity
  have htform : ∀ q : ℕ, (phaseTime P q : ℝ) = TP.eval (q : ℝ) := by
    intro q
    dsimp [TP]
    rw [phaseTime_table, phaseTimePoly_eval, hkm1]
  have hhform : ∀ q : ℕ,
      (cumScore (game P) (play P) (phaseTime P q) (play P (phaseTime P q)) : ℝ) =
        HP.eval (q : ℝ) := by
    intro q
    dsimp [HP]
    rw [phaseHeight_table, phaseHeightPoly_eval, hkm1]
  constructor
  · simpa only [htform, Nat.cast_add, Nat.cast_one] using
      polynomial_successor_ratio_error TP (by omega : 0 < k) htdeg htpos
  · simpa only [hhform, Nat.cast_add, Nat.cast_one] using
      polynomial_successor_ratio_error HP (by omega : 0 < k - 1) hhdeg hhpos

end Karlin.FaithfulPaperBounds
