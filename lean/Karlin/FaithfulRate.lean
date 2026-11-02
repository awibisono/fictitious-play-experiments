import Karlin.UnrolledTrajectory
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Faithful all-integer asymptotic interpolation

This file proves the analytic step in v15, Lemma `lem:alltime`.  The phase-boundary
asymptotics are explicit inputs; this does not assert that the moving-window clock
construction has already produced them.  The trajectory is fixed throughout.
-/

namespace Karlin.FaithfulRate

open Filter Topology Polynomial
open scoped BigOperators

/-- The last phase entry at or before `t`; before the first phase it is zero. -/
def phaseIndex (T : ℕ → ℕ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun q => T q ≤ t) t

theorem phaseIndex_spec {T : ℕ → ℕ} (hT : StrictMono T) {t : ℕ}
    (ht : T 0 ≤ t) :
    T (phaseIndex T t) ≤ t ∧ t < T (phaseIndex T t + 1) := by
  constructor
  · exact Nat.findGreatest_spec (P := fun q => T q ≤ t) (Nat.zero_le t) ht
  · by_contra h
    have hle : T (phaseIndex T t + 1) ≤ t := by omega
    have hi : phaseIndex T t + 1 ≤ t := (hT.id_le _).trans hle
    have := Nat.le_findGreatest (P := fun q => T q ≤ t) hi hle
    change phaseIndex T t + 1 ≤ phaseIndex T t at this
    omega

theorem phaseIndex_tendsto {T : ℕ → ℕ} (hT : StrictMono T) :
    Tendsto (phaseIndex T) atTop atTop := by
  apply tendsto_atTop.2
  intro q
  filter_upwards [eventually_ge_atTop (T q)] with t ht
  exact Nat.le_findGreatest ((hT.id_le q).trans ht) ht

/-- Shifting the numerator phase by one does not change its leading coefficient. -/
theorem successor_normalized_limit {f : ℕ → ℝ} {d : ℕ} {c : ℝ}
    (hf : Tendsto (fun q : ℕ => f q / (q : ℝ) ^ d) atTop (𝓝 c)) :
    Tendsto (fun q : ℕ => f (q + 1) / (q : ℝ) ^ d) atTop (𝓝 c) := by
  have hratio : Tendsto (fun q : ℕ => ((q : ℝ) + 1) / (q : ℝ)) atTop (𝓝 1) := by
    simpa [add_comm] using tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1
      (d := 1) (by norm_num)
  have h := (hf.comp (tendsto_add_atTop_nat 1)).mul (hratio.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_pow]
  field_simp

/-- Uniform interpolation between adjacent phase entries, for any monotone height.
Both limits are over *all integer times*, not a selected phase subsequence. -/
theorem interpolated_normalized_limits {T : ℕ → ℕ} {H : ℕ → ℝ}
    (hT : StrictMono T) (hH : Monotone H) {k d : ℕ} {a b : ℝ}
    (htime : Tendsto (fun q : ℕ => (T q : ℝ) / (q : ℝ) ^ k) atTop (𝓝 a))
    (hheight : Tendsto (fun q : ℕ => H (T q) / (q : ℝ) ^ d) atTop (𝓝 b)) :
    Tendsto (fun t : ℕ => (t : ℝ) / (phaseIndex T t : ℝ) ^ k) atTop (𝓝 a) ∧
    Tendsto (fun t : ℕ => H t / (phaseIndex T t : ℝ) ^ d) atTop (𝓝 b) := by
  have hq := phaseIndex_tendsto hT
  have he : ∀ᶠ t : ℕ in atTop,
      T (phaseIndex T t) ≤ t ∧ t ≤ T (phaseIndex T t + 1) := by
    filter_upwards [eventually_ge_atTop (T 0)] with t ht
    exact ⟨(phaseIndex_spec hT ht).1, (phaseIndex_spec hT ht).2.le⟩
  constructor
  · apply (htime.comp hq).squeeze' ((successor_normalized_limit htime).comp hq)
    · filter_upwards [he] with t ht
      exact div_le_div_of_nonneg_right (by exact_mod_cast ht.1) (by positivity)
    · filter_upwards [he] with t ht
      exact div_le_div_of_nonneg_right (by exact_mod_cast ht.2) (by positivity)
  · apply (hheight.comp hq).squeeze' ((successor_normalized_limit hheight).comp hq)
    · filter_upwards [he] with t ht
      exact div_le_div_of_nonneg_right (hH ht.1) (by positivity)
    · filter_upwards [he] with t ht
      exact div_le_div_of_nonneg_right (hH ht.2) (by positivity)

/-- The normalized height limit follows from phase limits, with the exact coefficient.
No limit concerning intermediate heights is assumed. -/
theorem all_integer_height_limit {T : ℕ → ℕ} {H : ℕ → ℝ}
    (hT : StrictMono T) (hH : Monotone H) {k d : ℕ} (hk : 0 < k) {a b : ℝ}
    (ha : 0 < a)
    (htime : Tendsto (fun q : ℕ => (T q : ℝ) / (q : ℝ) ^ k) atTop (𝓝 a))
    (hheight : Tendsto (fun q : ℕ => H (T q) / (q : ℝ) ^ d) atTop (𝓝 b)) :
    Tendsto (fun t : ℕ => H t / (t : ℝ) ^ ((d : ℝ) / (k : ℝ)))
      atTop (𝓝 (b / a ^ ((d : ℝ) / (k : ℝ)))) := by
  obtain ⟨ht, hh⟩ := interpolated_normalized_limits hT hH htime hheight
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hexp : (k : ℝ) * ((d : ℝ) / (k : ℝ)) = d := by field_simp
  have hlim := hh.div (ht.rpow_const (Or.inl ha.ne'))
    (Real.rpow_pos_of_pos ha ((d : ℝ) / (k : ℝ))).ne'
  apply hlim.congr'
  filter_upwards [(phaseIndex_tendsto hT).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with t hq ht1
  have hqpos : (0 : ℝ) < phaseIndex T t := by exact_mod_cast hq
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hpow : ((phaseIndex T t : ℝ) ^ k) ^ ((d : ℝ) / (k : ℝ)) =
      (phaseIndex T t : ℝ) ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le, hexp, Real.rpow_natCast]
  change (H t / (phaseIndex T t : ℝ) ^ d) /
    ((t : ℝ) / (phaseIndex T t : ℝ) ^ k) ^ ((d : ℝ) / (k : ℝ)) = _
  rw [Real.div_rpow htpos.le (pow_nonneg hqpos.le k), hpow]
  field_simp

/-- Exact v15 constant for every integer time, before identifying `2 H(t)/t`
with the standard empirical saddle-point gap. -/
theorem all_integer_gap_limit {T : ℕ → ℕ} {H : ℕ → ℝ}
    (hT : StrictMono T) (hH : Monotone H) {k : ℕ} (hk : 0 < k) {a b : ℝ}
    (ha : 0 < a)
    (htime : Tendsto (fun q : ℕ => (T q : ℝ) / (q : ℝ) ^ k) atTop (𝓝 a))
    (hheight : Tendsto (fun q : ℕ => H (T q) / (q : ℝ) ^ (k - 1)) atTop (𝓝 b)) :
    Tendsto (fun t : ℕ => (2 * H t / (t : ℝ)) * (t : ℝ) ^ (1 / (k : ℝ)))
      atTop (𝓝 (2 * b * a ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ)))) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hp : ((k - 1 : ℕ) : ℝ) / (k : ℝ) + 1 / (k : ℝ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    field_simp
    ring
  have hl := (all_integer_height_limit hT hH hk ha htime hheight).const_mul 2
  have hc : 2 * (b / a ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ))) =
      2 * b * a ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ)) := by
    rw [neg_div, Real.rpow_neg ha.le]
    ring
  rw [hc] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hpow : (t : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) *
      (t : ℝ) ^ (1 / (k : ℝ)) = t := by
    rw [← Real.rpow_add htpos, hp, Real.rpow_one]
  have hpowpos : 0 < (t : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) :=
    Real.rpow_pos_of_pos htpos _
  field_simp
  nlinarith [congrArg (fun x : ℝ => H t * x) hpow]

theorem exact_gap_constant_pos {k : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < 2 * b * a ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ)) := by
  exact mul_pos (mul_pos (by norm_num) hb) (Real.rpow_pos_of_pos ha _)

/-- The same strict skew-symmetric FP trajectory supplies both the monotone height
and the standard two-player empirical gap. The inputs are phase-boundary leading
coefficients; no conclusion about an alternative trajectory is substituted. -/
theorem standard_gap_exact_limit {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} {play : ℕ → α} (hM : IsSkewSymmetric M)
    (hplay : IsStrictFPTrajectory M play) {T : ℕ → ℕ} (hT : StrictMono T)
    {k : ℕ} (hk : 0 < k) {a b : ℝ} (ha : 0 < a)
    (htime : Tendsto (fun q : ℕ => (T q : ℝ) / (q : ℝ) ^ k) atTop (𝓝 a))
    (hheight : Tendsto (fun q : ℕ => (cumScore M play (T q) (play (T q)) : ℝ) /
      (q : ℝ) ^ (k - 1)) atTop (𝓝 b)) :
    Tendsto (fun t : ℕ => (standardDualityGap M play play t : ℝ) *
      (t : ℝ) ^ (1 / (k : ℝ)))
      atTop (𝓝 (2 * b * a ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ)))) := by
  have hH : Monotone (fun t => (cumScore M play t (play t) : ℝ)) := by
    intro s t hst
    dsimp only
    exact_mod_cast cumScore_active_mono hM hplay hst
  apply (all_integer_gap_limit hT hH hk ha htime hheight).congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [standardDualityGap_eq_stepDualityGap hM hplay ht]
  simp [stepDualityGap]

/-- A polynomial's leading coefficient is the limit after normalizing by its degree. -/
theorem polynomial_normalized_limit (P : ℝ[X]) (d : ℕ) (hdeg : P.degree = d) :
    Tendsto (fun q : ℕ => P.eval (q : ℝ) / (q : ℝ) ^ d)
      atTop (𝓝 P.leadingCoeff) := by
  have h := P.div_tendsto_leadingCoeff_div_of_degree_eq (Polynomial.X ^ d)
    (by simpa using hdeg)
  simpa using h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)

theorem descPochhammer_degree (d : ℕ) : (descPochhammer ℝ d).degree = d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [descPochhammer_succ_right, Polynomial.degree_mul, ih]
    have hc : (d : ℝ[X]) = Polynomial.C (d : ℝ) := by simp
    rw [hc, Polynomial.degree_X_sub_C]
    simp

/-- The coefficient of `q^d` in the binomial basis is `1/d!`, derived from the
descending Pochhammer polynomial, including `d=0`. -/
theorem binomial_normalized_limit (d : ℕ) :
    Tendsto (fun q : ℕ => (Nat.choose q d : ℝ) / (q : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have hc : (descPochhammer ℝ d).leadingCoeff = 1 := monic_descPochhammer ℝ d
  have h := (polynomial_normalized_limit (descPochhammer ℝ d) d (descPochhammer_degree d)).div_const
    (d.factorial : ℝ)
  simpa [hc, Nat.cast_choose_eq_descPochhammer_div, div_div, mul_comm] using h

/-- Every lower binomial-basis column vanishes after normalization by `q^d`. -/
theorem lower_binomial_normalized_limit {j d : ℕ} (hjd : j < d) :
    Tendsto (fun q : ℕ => (Nat.choose q j : ℝ) / (q : ℝ) ^ d) atTop (𝓝 0) := by
  have hdeg : (descPochhammer ℝ j).degree < (Polynomial.X ^ d : ℝ[X]).degree := by
    simpa [descPochhammer_degree] using hjd
  have h := ((descPochhammer ℝ j).div_tendsto_zero_of_degree_lt (Polynomial.X ^ d) hdeg).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
  have hh := h.div_const (j.factorial : ℝ)
  simpa [Nat.cast_choose_eq_descPochhammer_div, div_div, mul_comm] using hh

/-- A fixed starting phase changes none of the leading coefficients. -/
theorem fixed_shift_normalized_limit {f : ℕ → ℝ} {d : ℕ} {c : ℝ}
    (hf : Tendsto (fun q : ℕ => f q / (q : ℝ) ^ d) atTop (𝓝 c)) (Q : ℕ) :
    Tendsto (fun q : ℕ => f (q + Q) / (q : ℝ) ^ d) atTop (𝓝 c) := by
  induction Q with
  | zero => simpa using hf
  | succ Q ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (successor_normalized_limit (f := fun q => f (q + Q)) ih)

/-- Constant setup, bias, and phase-origin corrections are lower-order terms. -/
theorem constant_normalized_limit (c : ℝ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun q : ℕ => c / (q : ℝ) ^ d) atTop (𝓝 0) := by
  have h := ((tendsto_one_div_atTop_nhds_zero_nat :
    Tendsto (fun q : ℕ => (1 : ℝ) / q) atTop (𝓝 0)).pow d).const_mul c
  simpa [div_pow, zero_pow (Nat.ne_of_gt hd)] using h

/-- Leading coefficient of an arbitrary finite binomial-basis row. -/
theorem binomial_table_normalized_limit (c : ℕ → ℝ) (d : ℕ) :
    Tendsto (fun q : ℕ => (∑ j ∈ Finset.range (d + 1), c j * (Nat.choose q j : ℝ)) /
      (q : ℝ) ^ d) atTop (𝓝 (c d / (d.factorial : ℝ))) := by
  have hl : Tendsto (fun q : ℕ => ∑ j ∈ Finset.range d,
      c j * ((Nat.choose q j : ℝ) / (q : ℝ) ^ d)) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.range d) (fun j hj =>
      (lower_binomial_normalized_limit (Finset.mem_range.mp hj)).const_mul (c j))
    simpa using h
  have hh := hl.add ((binomial_normalized_limit d).const_mul (c d))
  simpa [Finset.sum_range_succ, Finset.sum_div, add_div, mul_div_assoc] using hh

/-- Entry-height table, including the actual fixed bias and setup translation. -/
theorem biased_height_table_normalized_limit (c : ℕ → ℝ) (Q : ℕ) (offset : ℝ)
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun q : ℕ =>
      ((∑ j ∈ Finset.range (d + 1), c j * (Nat.choose (q + Q) j : ℝ)) + offset) /
        (q : ℝ) ^ d) atTop (𝓝 (c d / (d.factorial : ℝ))) := by
  have h := (fixed_shift_normalized_limit (binomial_table_normalized_limit c d) Q).add
    (constant_normalized_limit offset hd)
  simpa [add_div] using h

/-- Integrating a binomial-basis count row raises its degree by one and divides
the last binomial coefficient by the new factorial. -/
theorem integrated_binomial_table_normalized_limit (c : ℕ → ℝ) (d : ℕ) :
    Tendsto (fun q : ℕ =>
      (∑ j ∈ Finset.range (d + 1), c j * (Nat.choose q (j + 1) : ℝ)) /
        (q : ℝ) ^ (d + 1)) atTop (𝓝 (c d / ((d + 1).factorial : ℝ))) := by
  have hl : Tendsto (fun q : ℕ => ∑ j ∈ Finset.range d,
      c j * ((Nat.choose q (j + 1) : ℝ) / (q : ℝ) ^ (d + 1))) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.range d) (fun j hj =>
      (lower_binomial_normalized_limit (Nat.succ_lt_succ (Finset.mem_range.mp hj))).const_mul (c j))
    simpa using h
  have hh := hl.add ((binomial_normalized_limit (d + 1)).const_mul (c d))
  simpa [Finset.sum_range_succ, Finset.sum_div, add_div, mul_div_assoc] using hh

/-- Scalar hockey-stick identity on exactly the moving phase interval `[Q,q+Q)`. -/
theorem binomial_Ico_sum (Q q j : ℕ) :
    (∑ σ ∈ Finset.Ico Q (q + Q), (Nat.choose σ j : ℝ)) =
      (Nat.choose (q + Q) (j + 1) : ℝ) - (Nat.choose Q (j + 1) : ℝ) := by
  have hstep (σ : ℕ) : (Nat.choose σ j : ℝ) =
      (Nat.choose (σ + 1) (j + 1) : ℝ) - (Nat.choose σ (j + 1) : ℝ) := by
    rw [Nat.choose_succ_succ, Nat.cast_add]
    ring
  simp_rw [hstep]
  exact Finset.sum_Ico_sub (fun σ => (Nat.choose σ (j + 1) : ℝ)) (by omega)

/-- The exact cumulative count formula implies the time coefficient `L/k!`.
The starting phase and setup round are fixed before the limit. -/
theorem clock_time_table_normalized_limit (c : ℕ → ℝ) (d Q : ℕ) (setup : ℝ) :
    Tendsto (fun q : ℕ =>
      (setup + ∑ σ ∈ Finset.Ico Q (q + Q),
        ∑ j ∈ Finset.range (d + 1), c j * (Nat.choose σ j : ℝ)) /
      (q : ℝ) ^ (d + 1)) atTop (𝓝 (c d / ((d + 1).factorial : ℝ))) := by
  have h := (fixed_shift_normalized_limit (integrated_binomial_table_normalized_limit c d) Q).add
    (constant_normalized_limit
      (setup - ∑ j ∈ Finset.range (d + 1), c j * (Nat.choose Q (j + 1) : ℝ))
      (Nat.succ_pos d))
  simp only [add_zero] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro q
  simp only [Nat.succ_eq_add_one]
  rw [← add_div, Finset.sum_comm]
  congr 1
  simp_rw [← Finset.mul_sum, binomial_Ico_sum, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- v15's exact constant, expressed directly in terms of the last count and
entry-score coefficients in the binomial basis. -/
noncomputable def paperGapConstant (k : ℕ) (L ξ : ℝ) : ℝ :=
  2 * (ξ / ((k - 1).factorial : ℝ)) *
    (L / (k.factorial : ℝ)) ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ))

/-- The analytic part of v15 Lemma `lem:alltime`, with exact count and height
tables instead of assumed asymptotic limits.  `countCoeff` is the row `1ᵀ C_k`;
`scoreCoeff` is the entry-action row of `R_k`.  `Q`, the bias/translation `offset`,
the game, and its trajectory are all fixed before the universal phase formulas.

This theorem does not construct the clock or certify its phase formulas.  Those
are explicit, substantive obligations for the compatible moving-window lift.
-/
theorem standard_gap_from_phase_tables {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} {play : ℕ → α} (hM : IsSkewSymmetric M)
    (hplay : IsStrictFPTrajectory M play) {T : ℕ → ℕ} (hT : StrictMono T)
    {k : ℕ} (hk : 2 ≤ k) (Q : ℕ) (countCoeff scoreCoeff : ℕ → ℝ) (offset : ℝ)
    (hL : 0 < countCoeff (k - 1)) (hξ : 0 < scoreCoeff (k - 1))
    (htime : ∀ q : ℕ, (T q : ℝ) =
      1 + ∑ σ ∈ Finset.Ico Q (q + Q),
        ∑ j ∈ Finset.range k, countCoeff j * (Nat.choose σ j : ℝ))
    (hheight : ∀ q : ℕ, (cumScore M play (T q) (play (T q)) : ℝ) =
      (∑ j ∈ Finset.range k, scoreCoeff j * (Nat.choose (q + Q) j : ℝ)) + offset) :
    0 < paperGapConstant k (countCoeff (k - 1)) (scoreCoeff (k - 1)) ∧
    Tendsto (fun t : ℕ => (standardDualityGap M play play t : ℝ) * (t : ℝ) ^ (1 / (k : ℝ)))
      atTop (𝓝 (paperGapConstant k (countCoeff (k - 1)) (scoreCoeff (k - 1)))) := by
  have hkm1 : k - 1 + 1 = k := by omega
  have ha : 0 < countCoeff (k - 1) / (k.factorial : ℝ) := by positivity
  have hb : 0 < scoreCoeff (k - 1) / ((k - 1).factorial : ℝ) := by positivity
  refine ⟨exact_gap_constant_pos ha hb, ?_⟩
  apply standard_gap_exact_limit hM hplay hT (by omega) ha
  · have h := clock_time_table_normalized_limit countCoeff (k - 1) Q 1
    simpa only [hkm1, ← htime] using h
  · have h := biased_height_table_normalized_limit scoreCoeff Q offset (by omega : 0 < k - 1)
    simpa only [hkm1, ← hheight] using h

/-- Multiplicative `1+o(1)` formulation of the exact same standard gap rate.
This conversion divides by the proved positive exact constant, not an unknown
or potentially zero leading coefficient. -/
theorem relative_gap_limit_of_normalized_limit {gap : ℕ → ℝ} {k : ℕ} {c : ℝ}
    (hc : 0 < c)
    (hgap : Tendsto (fun t : ℕ => gap t * (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 c)) :
    Tendsto (fun t : ℕ => gap t / (c * (t : ℝ) ^ (-(1 / (k : ℝ))))) atTop (𝓝 1) := by
  have h := hgap.div_const c
  rw [div_self hc.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hpow : (t : ℝ) ^ (1 / (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
  change (gap t * (t : ℝ) ^ (1 / (k : ℝ))) / c = _
  rw [Real.rpow_neg htpos.le]
  field_simp

end Karlin.FaithfulRate
