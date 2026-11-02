import Karlin.FaithfulGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quantitative remainder components for the v15 all-time rate

Successor-phase ratios and monotonicity give uniform bounds at every integer
time. These bounds propagate through the exact gap quotient and the inverse
phase-index conversion to prove both the relative O(t^(-1/k)) error and its
exact normalized limit.
-/

namespace Karlin.FaithfulRateError

open Filter Topology Polynomial Asymptotics
open scoped BigOperators

noncomputable def realCoeffMass (P : ℝ[X]) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, |P.coeff j|

/-- The ordinary polynomial remainder has an explicit coefficient bound. -/
theorem polynomial_remainder_bound (P : ℝ[X]) (d : ℕ) (hdegree : P.natDegree ≤ d)
    (x : ℝ) (hx : 1 ≤ x) :
    |P.eval x - P.coeff d * x ^ d| ≤ realCoeffMass P d * x ^ (d - 1) := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < d + 1), Finset.sum_range_succ]
  simp only [add_sub_cancel_right]
  calc
    |∑ j ∈ Finset.range d, P.coeff j * x ^ j| ≤
        ∑ j ∈ Finset.range d, |P.coeff j * x ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ realCoeffMass P d * x ^ (d - 1) := by
      unfold realCoeffMass
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hjd : j ≤ d - 1 := by have := Finset.mem_range.mp hj; omega
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ x) j)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hjd) (abs_nonneg _)

/-- Explicit `O(1/q)` normalized phase-polynomial error, valid already at q>=1. -/
theorem polynomial_normalized_error (P : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdegree : P.natDegree ≤ d) (x : ℝ) (hx : 1 ≤ x) :
    |P.eval x / x ^ d - P.coeff d| ≤ realCoeffMass P d / x := by
  have hxpos : 0 < x := by linarith
  have hpow : x ^ d = x ^ (d - 1) * x := by
    rw [← pow_succ]
    congr 1
    omega
  have hrew : P.eval x / x ^ d - P.coeff d = (P.eval x - P.coeff d * x ^ d) / x ^ d := by
    field_simp
  rw [hrew, abs_div, abs_of_pos (pow_pos hxpos d)]
  calc
    |P.eval x - P.coeff d * x ^ d| / x ^ d ≤
        (realCoeffMass P d * x ^ (d - 1)) / x ^ d :=
      div_le_div_of_nonneg_right (polynomial_remainder_bound P d hdegree x hx) (by positivity)
    _ = realCoeffMass P d / x := by
      rw [hpow]
      field_simp

/-- Differentiability propagates both leading-coefficient errors through the
exact quotient used by the gap normalization. -/
theorem quotient_error_isBigO {u v e : ℕ → ℝ} {a b p : ℝ} (ha : 0 < a)
    (hu : Tendsto u atTop (𝓝 b)) (hv : Tendsto v atTop (𝓝 a))
    (heu : (fun t => u t - b) =O[atTop] e)
    (hev : (fun t => v t - a) =O[atTop] e) :
    (fun t => 2 * u t / v t ^ p - 2 * b / a ^ p) =O[atTop] e := by
  let G : ℝ × ℝ → ℝ := fun z => 2 * z.1 / z.2 ^ p
  have hG : DifferentiableAt ℝ G (b, a) := by
    have hf : DifferentiableAt ℝ (fun z : ℝ × ℝ => z.1) (b, a) := differentiableAt_fst
    have hs : DifferentiableAt ℝ (fun z : ℝ × ℝ => z.2) (b, a) := differentiableAt_snd
    have hd : DifferentiableAt ℝ (fun z : ℝ × ℝ => z.2 ^ p) (b, a) :=
      hs.rpow_const (Or.inl ha.ne')
    simpa [G, div_eq_mul_inv] using
      ((differentiableAt_const (2 : ℝ)).mul hf).mul (hd.inv (Real.rpow_pos_of_pos ha p).ne')
  have h := hG.isBigO_sub.comp_tendsto (hu.prodMk_nhds hv)
  have he : (fun t => (u t, v t) - (b, a)) =O[atTop] e := by
    simpa using heu.prod_left hev
  simpa [G, Function.comp_def] using h.trans he

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


/-- Monotonicity encloses the entire phase. Dividing by its positive entry
height bounds the within-phase relative error by the successor-phase ratio.
Thus the same asymptotic constant works for every integer within each phase. -/
theorem within_phase_ratio_error {T : ℕ → ℕ} {F : ℕ → ℝ}
    (hT : StrictMono T) (hF : Monotone F)
    (hpos : ∀ᶠ q : ℕ in atTop, 0 < F (T q))
    (hratio : (fun q : ℕ => F (T (q + 1)) / F (T q) - 1)
      =O[atTop] (fun q : ℕ => 1 / (q : ℝ))) :
    (fun t : ℕ => F t / F (T (FaithfulRate.phaseIndex T t)) - 1)
      =O[atTop] (fun t : ℕ => 1 / (FaithfulRate.phaseIndex T t : ℝ)) := by
  have hq := FaithfulRate.phaseIndex_tendsto hT
  apply IsBigO.trans ?_ (hratio.comp_tendsto hq)
  apply IsBigO.of_bound 1
  filter_upwards [hq.eventually hpos, eventually_ge_atTop (T 0)] with t hp ht
  let q := FaithfulRate.phaseIndex T t
  have hbr := FaithfulRate.phaseIndex_spec hT ht
  have hlo : 1 ≤ F t / F (T q) := (le_div_iff₀ hp).mpr (by simpa using hF hbr.1)
  have hhi : F t / F (T q) ≤ F (T (q + 1)) / F (T q) :=
    div_le_div_of_nonneg_right (hF hbr.2.le) hp.le
  have hs : 1 ≤ F (T (q + 1)) / F (T q) := hlo.trans hhi
  change |F t / F (T q) - 1| ≤ 1 * |F (T (q + 1)) / F (T q) - 1|
  simpa only [one_mul,
    abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg (sub_nonneg.mpr hs)] using
      sub_le_sub_right hhi 1

/-- A positive-degree phase polynomial of a monotone sequence has positive
leading coefficient. Positivity is derived, rather than assumed. -/
theorem leadingCoeff_pos_of_monotone_phase {T : ℕ → ℕ} {F : ℕ → ℝ}
    (hT : StrictMono T) (hF : Monotone F) (P : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdegree : P.natDegree = d) (hphase : ∀ q : ℕ, F (T q) = P.eval (q : ℝ)) :
    0 < P.leadingCoeff := by
  have hp : P ≠ 0 := by intro h; simp [h] at hdegree; omega
  have hdeg : P.degree = d := by rw [Polynomial.degree_eq_natDegree hp, hdegree]
  have hlim := FaithfulRate.polynomial_normalized_limit P d hdeg
  have hlow := FaithfulRate.constant_normalized_limit (F (T 0)) hd
  have hc : 0 ≤ P.leadingCoeff := le_of_tendsto_of_tendsto hlow hlim (by
    apply Filter.Eventually.of_forall
    intro q
    dsimp only
    rw [← hphase]
    exact div_le_div_of_nonneg_right (hF (hT.monotone (Nat.zero_le q))) (by positivity))
  exact lt_of_le_of_ne hc (Polynomial.leadingCoeff_ne_zero.mpr hp).symm

/-- Quantitative interpolation through the paper's successor ratios: first
`F(t)/F(T(q(t))) = 1 + O(1/q(t))`, then multiply by the normalized phase value.
All error bounds are uniform over every integer in the phase enclosure. -/
theorem interpolated_polynomial_error {T : ℕ → ℕ} {F : ℕ → ℝ}
    (hT : StrictMono T) (hF : Monotone F) (P : ℝ[X]) {d : ℕ} (hd : 0 < d)
    (hdegree : P.natDegree = d) (hphase : ∀ q : ℕ, F (T q) = P.eval (q : ℝ)) :
    (fun t : ℕ => F t / (FaithfulRate.phaseIndex T t : ℝ) ^ d - P.leadingCoeff)
      =O[atTop] (fun t : ℕ => 1 / (FaithfulRate.phaseIndex T t : ℝ)) := by
  have hc := leadingCoeff_pos_of_monotone_phase hT hF P hd hdegree hphase
  have hp : P ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hc.ne'
  have hdeg : P.degree = d := by rw [Polynomial.degree_eq_natDegree hp, hdegree]
  have hlim := FaithfulRate.polynomial_normalized_limit P d hdeg
  have hpos : ∀ᶠ q : ℕ in atTop, 0 < F (T q) := by
    filter_upwards [hlim.eventually (lt_mem_nhds hc), eventually_ge_atTop 1] with q hq hq1
    rw [hphase]
    exact (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < (q : ℝ) ^ d)).mp hq
  have hratio : (fun q : ℕ => F (T (q + 1)) / F (T q) - 1)
      =O[atTop] (fun q : ℕ => 1 / (q : ℝ)) := by
    simpa only [hphase, Nat.cast_add, Nat.cast_one] using
      polynomial_successor_ratio_error P hd hdegree hc
  have hwithin := within_phase_ratio_error hT hF hpos hratio
  have hq := FaithfulRate.phaseIndex_tendsto hT
  have hboundary : (fun t : ℕ =>
      F (T (FaithfulRate.phaseIndex T t)) / (FaithfulRate.phaseIndex T t : ℝ) ^ d)
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    simpa only [hphase, Function.comp_apply] using (hlim.comp hq).isBigO_one ℝ
  have hboundaryError : (fun t : ℕ =>
      F (T (FaithfulRate.phaseIndex T t)) / (FaithfulRate.phaseIndex T t : ℝ) ^ d -
        P.leadingCoeff) =O[atTop] (fun t : ℕ => 1 / (FaithfulRate.phaseIndex T t : ℝ)) := by
    simpa only [hphase, Function.comp_apply] using
      (polynomial_normalized_isBigO P hd hdegree).comp_tendsto hq
  have hproduct := hwithin.mul hboundary
  simp only [mul_one] at hproduct
  apply (hproduct.add hboundaryError).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hq.eventually hpos, hq.eventually (eventually_ge_atTop 1)] with t hp hqt
  have hqne : (FaithfulRate.phaseIndex T t : ℝ) ^ d ≠ 0 := by positivity
  change (F t / F (T (FaithfulRate.phaseIndex T t)) - 1) *
      (F (T (FaithfulRate.phaseIndex T t)) / (FaithfulRate.phaseIndex T t : ℝ) ^ d) +
      (F (T (FaithfulRate.phaseIndex T t)) / (FaithfulRate.phaseIndex T t : ℝ) ^ d -
        P.leadingCoeff) = _
  field_simp
  ring

/-- The inverse phase index has precisely the time scale needed by the paper's
stronger error estimate. This is derived from t/q(t)^k->a>0. -/
theorem inverse_index_isBigO_time {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 < a)
    (htime : Tendsto (fun t : ℕ => (t : ℝ) / (q t : ℝ) ^ k) atTop (𝓝 a)) :
    (fun t : ℕ => 1 / (q t : ℝ)) =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hlim := htime.rpow_const (p := 1 / (k : ℝ)) (Or.inl ha.ne')
  have hdiv : Tendsto
      ((fun t : ℕ => 1 / (q t : ℝ)) / (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))))
      atTop (𝓝 (a ^ (1 / (k : ℝ)))) := by
    apply hlim.congr'
    filter_upwards [hq.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with t hqt ht
    have hqpos : (0 : ℝ) < q t := by exact_mod_cast hqt
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have hp : ((q t : ℝ) ^ k) ^ (1 / (k : ℝ)) = q t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le]
      have he : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
      rw [he, Real.rpow_one]
    change ((t : ℝ) / (q t : ℝ) ^ k) ^ (1 / (k : ℝ)) =
      (1 / (q t : ℝ)) / (t : ℝ) ^ (-(1 / (k : ℝ)))
    rw [Real.div_rpow htpos.le (pow_nonneg hqpos.le k), hp, Real.rpow_neg htpos.le]
    field_simp
  apply isBigO_of_div_tendsto_nhds _ _ hdiv
  filter_upwards [eventually_ge_atTop 1] with t ht hzero
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  exact ((Real.rpow_pos_of_pos htpos _).ne' hzero).elim

theorem normalized_gap_eq_quotient (H : ℝ) {k t q : ℕ} (hk : 0 < k)
    (ht : 0 < t) (hq : 0 < q) :
    (2 * H / (t : ℝ)) * (t : ℝ) ^ (1 / (k : ℝ)) =
      2 * (H / (q : ℝ) ^ (k - 1)) /
        ((t : ℝ) / (q : ℝ) ^ k) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hexp : (k : ℝ) * (((k - 1 : ℕ) : ℝ) / (k : ℝ)) = (k - 1 : ℕ) := by field_simp
  have hqpow : ((q : ℝ) ^ k) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) = (q : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqpos.le, hexp, Real.rpow_natCast]
  have hp : ((k - 1 : ℕ) : ℝ) / (k : ℝ) + 1 / (k : ℝ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    field_simp
    ring
  have htpow : (t : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) * (t : ℝ) ^ (1 / (k : ℝ)) = t := by
    rw [← Real.rpow_add htpos, hp, Real.rpow_one]
  rw [Real.div_rpow htpos.le (pow_nonneg hqpos.le k), hqpow]
  have hpne := (Real.rpow_pos_of_pos htpos (((k - 1 : ℕ) : ℝ) / (k : ℝ))).ne'
  field_simp
  nlinarith [congrArg (fun x : ℝ => H * x) htpow]

/-- Complete quantitative all-integer interpolation from exact polynomial phase
times and heights. No remainder estimate for intermediate times is assumed. -/
theorem all_integer_polynomial_gap_error {T : ℕ → ℕ} {H : ℕ → ℝ}
    (hT : StrictMono T) (hH : Monotone H) (timePoly heightPoly : ℝ[X])
    {k : ℕ} (hk : 2 ≤ k) (hdegreeT : timePoly.natDegree = k)
    (hdegreeH : heightPoly.natDegree = k - 1) (ha : 0 < timePoly.leadingCoeff)
    (htime : ∀ q : ℕ, (T q : ℝ) = timePoly.eval (q : ℝ))
    (hheight : ∀ q : ℕ, H (T q) = heightPoly.eval (q : ℝ)) :
    (fun t : ℕ => (2 * H t / (t : ℝ)) * (t : ℝ) ^ (1 / (k : ℝ)) -
      2 * heightPoly.leadingCoeff * timePoly.leadingCoeff ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ)))
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  have htmono : Monotone (fun t : ℕ => (t : ℝ)) := by
    intro s t hst
    dsimp only
    exact_mod_cast hst
  have hterror := interpolated_polynomial_error hT htmono timePoly (by omega : 0 < k) hdegreeT htime
  have hherror := interpolated_polynomial_error hT hH heightPoly (by omega : 0 < k - 1) hdegreeH hheight
  have hzero : Tendsto (fun t : ℕ => 1 / (FaithfulRate.phaseIndex T t : ℝ))
      atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat.comp (FaithfulRate.phaseIndex_tendsto hT)
  have htlim : Tendsto (fun t : ℕ => (t : ℝ) / (FaithfulRate.phaseIndex T t : ℝ) ^ k)
      atTop (𝓝 timePoly.leadingCoeff) := by
    simpa only [sub_add_cancel, zero_add] using
      (hterror.trans_tendsto hzero).add_const timePoly.leadingCoeff
  have hhlim : Tendsto (fun t : ℕ => H t / (FaithfulRate.phaseIndex T t : ℝ) ^ (k - 1))
      atTop (𝓝 heightPoly.leadingCoeff) := by
    simpa only [sub_add_cancel, zero_add] using
      (hherror.trans_tendsto hzero).add_const heightPoly.leadingCoeff
  have herror := quotient_error_isBigO (p := ((k - 1 : ℕ) : ℝ) / (k : ℝ))
    ha hhlim htlim hherror hterror
  have hscale := inverse_index_isBigO_time (FaithfulRate.phaseIndex_tendsto hT)
    (by omega : 0 < k) ha htlim
  apply (herror.trans hscale).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [(FaithfulRate.phaseIndex_tendsto hT).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with t hq ht
  have hid := normalized_gap_eq_quotient (H t) (by omega : 0 < k)
    (by omega : 0 < t) (by omega : 0 < FaithfulRate.phaseIndex T t)
  have hc : 2 * heightPoly.leadingCoeff / timePoly.leadingCoeff ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) =
      2 * heightPoly.leadingCoeff * timePoly.leadingCoeff ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ)) := by
    rw [neg_div, Real.rpow_neg ha.le]
    rfl
  change 2 * (H t / (FaithfulRate.phaseIndex T t : ℝ) ^ (k - 1)) /
    ((t : ℝ) / (FaithfulRate.phaseIndex T t : ℝ) ^ k) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) - _ = _
  rw [← hid, hc]

/-- Divide the normalized error by the proved positive exact constant. -/
theorem relative_error_of_normalized_error {gap : ℕ → ℝ} {k : ℕ} {c : ℝ} (hc : 0 < c)
    (herror : (fun t : ℕ => gap t * (t : ℝ) ^ (1 / (k : ℝ)) - c)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ))))) :
    (fun t : ℕ => gap t / (c * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  apply (herror.const_mul_left (1 / c)).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hpne := (Real.rpow_pos_of_pos htpos (1 / (k : ℝ))).ne'
  change (1 / c) * (gap t * (t : ℝ) ^ (1 / (k : ℝ)) - c) = _
  rw [Real.rpow_neg htpos.le]
  field_simp

/-- The paper's stronger relative error estimate for the actual standard
two-player gap, conditional on exact polynomial phase formulas of one trajectory. -/
theorem standard_gap_polynomial_relative_error {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} {play : ℕ → α} (hM : IsSkewSymmetric M)
    (hplay : IsStrictFPTrajectory M play) {T : ℕ → ℕ} (hT : StrictMono T)
    (timePoly heightPoly : ℝ[X]) {k : ℕ} (hk : 2 ≤ k)
    (hdegreeT : timePoly.natDegree = k) (hdegreeH : heightPoly.natDegree = k - 1)
    (ha : 0 < timePoly.leadingCoeff) (hb : 0 < heightPoly.leadingCoeff)
    (htime : ∀ q : ℕ, (T q : ℝ) = timePoly.eval (q : ℝ))
    (hheight : ∀ q : ℕ, (cumScore M play (T q) (play (T q)) : ℝ) = heightPoly.eval (q : ℝ)) :
    let c := 2 * heightPoly.leadingCoeff * timePoly.leadingCoeff ^ (-((k - 1 : ℕ) : ℝ) / (k : ℝ))
    (fun t : ℕ => (standardDualityGap M play play t : ℝ) /
      (c * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  have hH : Monotone (fun t => (cumScore M play t (play t) : ℝ)) := by
    intro s t hst
    dsimp only
    exact_mod_cast cumScore_active_mono hM hplay hst
  have herror := all_integer_polynomial_gap_error hT hH timePoly heightPoly hk hdegreeT hdegreeH ha htime hheight
  apply relative_error_of_normalized_error (FaithfulRate.exact_gap_constant_pos ha hb)
  apply herror.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [standardDualityGap_eq_stepDualityGap hM hplay ht]
  simp [stepDualityGap]

/-- Real polynomial represented by a finite binomial table row. -/
noncomputable def binomialPoly (c : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C (c j / (j.factorial : ℝ)) * descPochhammer ℝ j

theorem binomialPoly_eval (c : ℕ → ℝ) (d q : ℕ) :
    (binomialPoly c d).eval (q : ℝ) =
      ∑ j ∈ Finset.range (d + 1), c j * (Nat.choose q j : ℝ) := by
  simp only [binomialPoly, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Nat.cast_choose_eq_descPochhammer_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem binomialPoly_natDegree_le (c : ℕ → ℝ) (d : ℕ) : (binomialPoly c d).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hn : (descPochhammer ℝ j).natDegree = j :=
    Polynomial.natDegree_eq_of_degree_eq_some (FaithfulRate.descPochhammer_degree j)
  rw [hn]
  have := Finset.mem_range.mp hj
  omega

theorem binomialPoly_top_coeff (c : ℕ → ℝ) (d : ℕ) :
    (binomialPoly c d).coeff d = c d / (d.factorial : ℝ) := by
  simp only [binomialPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single d]
  · have hn : (descPochhammer ℝ d).natDegree = d :=
      Polynomial.natDegree_eq_of_degree_eq_some (FaithfulRate.descPochhammer_degree d)
    have hm := monic_descPochhammer ℝ d
    have hc : (descPochhammer ℝ d).coeff d = 1 := by
      simpa [Polynomial.Monic, Polynomial.leadingCoeff, hn] using hm
    simp [hc]
  · intro j hj hjd
    have hlt : j < d := by have := Finset.mem_range.mp hj; omega
    have hz : (descPochhammer ℝ j).coeff d = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (by simpa [FaithfulRate.descPochhammer_degree] using hlt)
    simp [hz]
  · simp

theorem binomialPoly_degree_coeff (c : ℕ → ℝ) (d : ℕ) (hc : c d ≠ 0) :
    (binomialPoly c d).natDegree = d ∧ (binomialPoly c d).leadingCoeff = c d / (d.factorial : ℝ) := by
  have hdeg : (binomialPoly c d).natDegree = d := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (binomialPoly_natDegree_le c d)
    rw [binomialPoly_top_coeff]
    exact div_ne_zero hc (by positivity)
  exact ⟨hdeg, by rw [Polynomial.leadingCoeff, hdeg, binomialPoly_top_coeff]⟩

noncomputable def shiftedPoly (P : ℝ[X]) (Q : ℕ) (offset : ℝ) : ℝ[X] :=
  P.comp (Polynomial.X + Polynomial.C (Q : ℝ)) + Polynomial.C offset

theorem shiftedPoly_degree (P : ℝ[X]) (Q : ℕ) (offset : ℝ) :
    (shiftedPoly P Q offset).natDegree = P.natDegree := by
  rw [shiftedPoly, Polynomial.natDegree_add_C, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_add_C, mul_one]

theorem shiftedPoly_leadingCoeff (P : ℝ[X]) (Q : ℕ) (offset : ℝ) (hd : 0 < P.natDegree) :
    (shiftedPoly P Q offset).leadingCoeff = P.leadingCoeff := by
  have hs : (P.comp (Polynomial.X + Polynomial.C (Q : ℝ))).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  rw [shiftedPoly, Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
    Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), add_zero, Polynomial.coeff_natDegree]
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; norm_num),
    Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

/-- Discrete antiderivative of a binomial row: zero constant column and each
count coefficient shifted up by one binomial index. -/
def integralCoeff (c : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else c (j - 1)

theorem integral_binomialPoly_eval (c : ℕ → ℝ) (d q : ℕ) :
    (binomialPoly (integralCoeff c) (d + 1)).eval (q : ℝ) =
      ∑ j ∈ Finset.range (d + 1), c j * (Nat.choose q (j + 1) : ℝ) := by
  rw [binomialPoly_eval, Finset.sum_range_succ']
  simp [integralCoeff]

noncomputable def phaseTimePoly (c : ℕ → ℝ) (d Q : ℕ) : ℝ[X] :=
  shiftedPoly (binomialPoly (integralCoeff c) (d + 1)) Q
    (1 - ∑ j ∈ Finset.range (d + 1), c j * (Nat.choose Q (j + 1) : ℝ))

noncomputable def phaseHeightPoly (c : ℕ → ℝ) (d Q : ℕ) (offset : ℝ) : ℝ[X] :=
  shiftedPoly (binomialPoly c d) Q offset

theorem phaseTimePoly_eval (c : ℕ → ℝ) (d Q q : ℕ) :
    (phaseTimePoly c d Q).eval (q : ℝ) =
      1 + ∑ σ ∈ Finset.Ico Q (q + Q),
        ∑ j ∈ Finset.range (d + 1), c j * (Nat.choose σ j : ℝ) := by
  simp only [phaseTimePoly, shiftedPoly, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.cast_add, integral_binomialPoly_eval, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FaithfulRate.binomial_Ico_sum, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

theorem phaseHeightPoly_eval (c : ℕ → ℝ) (d Q q : ℕ) (offset : ℝ) :
    (phaseHeightPoly c d Q offset).eval (q : ℝ) =
      (∑ j ∈ Finset.range (d + 1), c j * (Nat.choose (q + Q) j : ℝ)) + offset := by
  simp only [phaseHeightPoly, shiftedPoly, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.cast_add, binomialPoly_eval]

theorem phaseTimePoly_degree_coeff (c : ℕ → ℝ) (d Q : ℕ) (hc : c d ≠ 0) :
    (phaseTimePoly c d Q).natDegree = d + 1 ∧
      (phaseTimePoly c d Q).leadingCoeff = c d / ((d + 1).factorial : ℝ) := by
  have hi : integralCoeff c (d + 1) ≠ 0 := by simpa [integralCoeff] using hc
  obtain ⟨hdeg, hcoeff⟩ := binomialPoly_degree_coeff (integralCoeff c) (d + 1) hi
  constructor
  · rw [phaseTimePoly, shiftedPoly_degree, hdeg]
  · rw [phaseTimePoly, shiftedPoly_leadingCoeff _ _ _ (by omega), hcoeff]
    simp [integralCoeff]

theorem phaseHeightPoly_degree_coeff (c : ℕ → ℝ) {d : ℕ} (hd : 0 < d)
    (Q : ℕ) (offset : ℝ) (hc : c d ≠ 0) :
    (phaseHeightPoly c d Q offset).natDegree = d ∧
      (phaseHeightPoly c d Q offset).leadingCoeff = c d / (d.factorial : ℝ) := by
  obtain ⟨hdeg, hcoeff⟩ := binomialPoly_degree_coeff c d hc
  constructor
  · rw [phaseHeightPoly, shiftedPoly_degree, hdeg]
  · rw [phaseHeightPoly, shiftedPoly_leadingCoeff _ _ _ (by omega), hcoeff]

/-- The v15 stronger relative remainder estimate, with exactly the same explicit
binomial phase-table inputs as `FaithfulRate.standard_gap_from_phase_tables`.
No polynomial, phase-limit, or intermediate-time error claim is assumed here. -/
theorem standard_gap_from_phase_tables_relative_error {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} {play : ℕ → α} (hM : IsSkewSymmetric M)
    (hplay : IsStrictFPTrajectory M play) {T : ℕ → ℕ} (hT : StrictMono T)
    {k : ℕ} (hk : 2 ≤ k) (Q : ℕ) (countCoeff scoreCoeff : ℕ → ℝ) (offset : ℝ)
    (hL : 0 < countCoeff (k - 1)) (hξ : 0 < scoreCoeff (k - 1))
    (htime : ∀ q : ℕ, (T q : ℝ) =
      1 + ∑ σ ∈ Finset.Ico Q (q + Q),
        ∑ j ∈ Finset.range k, countCoeff j * (Nat.choose σ j : ℝ))
    (hheight : ∀ q : ℕ, (cumScore M play (T q) (play (T q)) : ℝ) =
      (∑ j ∈ Finset.range k, scoreCoeff j * (Nat.choose (q + Q) j : ℝ)) + offset) :
    let c := FaithfulRate.paperGapConstant k (countCoeff (k - 1)) (scoreCoeff (k - 1))
    (fun t : ℕ => (standardDualityGap M play play t : ℝ) /
      (c * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  let TP := phaseTimePoly countCoeff (k - 1) Q
  let HP := phaseHeightPoly scoreCoeff (k - 1) Q offset
  have hkm1 : k - 1 + 1 = k := by omega
  obtain ⟨htdeg, htcoeff⟩ := phaseTimePoly_degree_coeff countCoeff (k - 1) Q hL.ne'
  obtain ⟨hhdeg, hhcoeff⟩ := phaseHeightPoly_degree_coeff scoreCoeff
    (by omega : 0 < k - 1) Q offset hξ.ne'
  rw [hkm1] at htdeg htcoeff
  have htpos : 0 < TP.leadingCoeff := by
    change 0 < (phaseTimePoly countCoeff (k - 1) Q).leadingCoeff
    rw [htcoeff]
    positivity
  have hhpos : 0 < HP.leadingCoeff := by
    change 0 < (phaseHeightPoly scoreCoeff (k - 1) Q offset).leadingCoeff
    rw [hhcoeff]
    positivity
  have htform : ∀ q : ℕ, (T q : ℝ) = TP.eval (q : ℝ) := by
    intro q
    dsimp [TP]
    rw [htime, phaseTimePoly_eval, hkm1]
  have hhform : ∀ q : ℕ, (cumScore M play (T q) (play (T q)) : ℝ) = HP.eval (q : ℝ) := by
    intro q
    dsimp [HP]
    rw [hheight, phaseHeightPoly_eval, hkm1]
  have h := standard_gap_polynomial_relative_error hM hplay hT TP HP hk htdeg hhdeg htpos hhpos htform hhform
  simpa only [TP, HP, htcoeff, hhcoeff, FaithfulRate.paperGapConstant] using h

/-- The quantitative error implies the exact normalized limit using the same
constant. This makes the ratio interpolation an essential dependency of the
actual exact-limit branch as well as the relative-error branch. -/
theorem normalized_limit_of_relative_error {gap : ℕ → ℝ} {k : ℕ} {c : ℝ}
    (hk : 0 < k) (hc : 0 < c)
    (herror : (fun t : ℕ => gap t / (c * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ))))) :
    Tendsto (fun t : ℕ => gap t * (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 c) := by
  have hzero : Tendsto (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < 1 / (k : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have h := ((herror.trans_tendsto hzero).const_mul c).add_const c
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hpne := (Real.rpow_pos_of_pos htpos (1 / (k : ℝ))).ne'
  rw [Real.rpow_neg htpos.le]
  field_simp
  ring

/-- The actual all-integer exact gap limit, derived through the neighboring
phase ratios and their uniform within-phase relative-error estimates. -/
theorem standard_gap_from_phase_tables_exact_limit {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    {M : Matrix α α ℚ} {play : ℕ → α} (hM : IsSkewSymmetric M)
    (hplay : IsStrictFPTrajectory M play) {T : ℕ → ℕ} (hT : StrictMono T)
    {k : ℕ} (hk : 2 ≤ k) (Q : ℕ) (countCoeff scoreCoeff : ℕ → ℝ) (offset : ℝ)
    (hL : 0 < countCoeff (k - 1)) (hξ : 0 < scoreCoeff (k - 1))
    (htime : ∀ q : ℕ, (T q : ℝ) =
      1 + ∑ σ ∈ Finset.Ico Q (q + Q),
        ∑ j ∈ Finset.range k, countCoeff j * (Nat.choose σ j : ℝ))
    (hheight : ∀ q : ℕ, (cumScore M play (T q) (play (T q)) : ℝ) =
      (∑ j ∈ Finset.range k, scoreCoeff j * (Nat.choose (q + Q) j : ℝ)) + offset) :
    0 < FaithfulRate.paperGapConstant k (countCoeff (k - 1)) (scoreCoeff (k - 1)) ∧
    Tendsto (fun t : ℕ => (standardDualityGap M play play t : ℝ) * (t : ℝ) ^ (1 / (k : ℝ)))
      atTop (𝓝 (FaithfulRate.paperGapConstant k (countCoeff (k - 1)) (scoreCoeff (k - 1)))) := by
  have ha : 0 < countCoeff (k - 1) / (k.factorial : ℝ) := by positivity
  have hb : 0 < scoreCoeff (k - 1) / ((k - 1).factorial : ℝ) := by positivity
  have hc := FaithfulRate.exact_gap_constant_pos (k := k) ha hb
  refine ⟨hc, normalized_limit_of_relative_error (by omega : 0 < k) hc ?_⟩
  exact standard_gap_from_phase_tables_relative_error hM hplay hT hk Q
    countCoeff scoreCoeff offset hL hξ htime hheight

end Karlin.FaithfulRateError
