import Karlin.FaithfulClock
import Karlin.FaithfulRate

/-!
# Growth estimates derived from the v15 clock interface

The last count column is proved nonnegative from eventual actual word counts.
Full column rank then forces its total to be positive. No sign hypothesis is
added to the lower count coefficients or to the clock counter.
-/

namespace Karlin.FaithfulGrowth

open Filter Topology Polynomial
open scoped BigOperators

theorem fin_binomial_normalized_limit {k : ℕ} (hk : 0 < k) (c : Fin k → ℚ) :
    Tendsto (fun q : ℕ =>
      ((∑ j : Fin k, c j * (Nat.choose q j.val : ℚ) : ℚ) : ℝ) / (q : ℝ) ^ (k - 1))
      atTop (𝓝 ((c ⟨k - 1, by omega⟩ : ℝ) / ((k - 1).factorial : ℝ))) := by
  let last : Fin k := ⟨k - 1, by omega⟩
  have hterm (j : Fin k) :
      Tendsto (fun q : ℕ => (c j : ℝ) * ((Nat.choose q j.val : ℝ) / (q : ℝ) ^ (k - 1)))
        atTop (𝓝 (if j = last then (c last : ℝ) / ((k - 1).factorial : ℝ) else 0)) := by
    by_cases hj : j = last
    · subst j
      simpa [last] using (FaithfulRate.binomial_normalized_limit (k - 1)).const_mul (c last : ℝ)
    · have hjlt : j.val < k - 1 := by
        have hjne : j.val ≠ k - 1 := by
          intro h
          apply hj
          exact Fin.ext h
        omega
      simpa [hj] using (FaithfulRate.lower_binomial_normalized_limit hjlt).const_mul (c j : ℝ)
  have h := tendsto_finset_sum Finset.univ (fun j _ => hterm j)
  simpa [last, Finset.sum_div, mul_div_assoc] using h

namespace Clock

variable {k : ℕ} (P : FaithfulClock.Clock k)

def topIndex : Fin k := ⟨k - 1, by have := P.order_ge_two; omega⟩

theorem leading_count_nonneg (i : Fin P.m) : 0 ≤ P.countTable i (topIndex P) := by
  have hlim := fin_binomial_normalized_limit (by have := P.order_ge_two; omega : 0 < k)
    (P.countTable i)
  have he : ∀ᶠ q : ℕ in atTop,
      0 ≤ ((∑ j : Fin k, P.countTable i j * (Nat.choose q j.val : ℚ) : ℚ) : ℝ) /
        (q : ℝ) ^ (k - 1) := by
    filter_upwards [eventually_ge_atTop P.Q] with q hq
    apply div_nonneg
    · exact_mod_cast P.count_nonneg q hq i
    · positivity
  have hc : 0 ≤ (P.countTable i (topIndex P) : ℝ) / ((k - 1).factorial : ℝ) :=
    ge_of_tendsto hlim he
  have hf : (0 : ℝ) < ((k - 1).factorial : ℝ) := by positivity
  have hc' : 0 ≤ (P.countTable i (topIndex P) : ℝ) := by
    simpa using (le_div_iff₀ hf).mp hc
  exact_mod_cast hc'

/-- Full column rank rules out a zero final count column. Combined with
eventual actual nonnegative counts this proves the required positive total. -/
theorem leading_total_count_pos : 0 < ∑ i : Fin P.m, P.countTable i (topIndex P) := by
  have hn (i : Fin P.m) : 0 ≤ P.countTable i (topIndex P) := leading_count_nonneg P i
  have hs : 0 ≤ ∑ i : Fin P.m, P.countTable i (topIndex P) := Finset.sum_nonneg (fun i _ => hn i)
  by_contra hpos
  have hz : ∑ i : Fin P.m, P.countTable i (topIndex P) = 0 := by linarith
  have hcol : ∀ i : Fin P.m, P.countTable i (topIndex P) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz i (Finset.mem_univ i)
  have hkernel : (FaithfulClock.ratCount P.C).mulVec (Pi.single (topIndex P) (1 : ℚ)) =
      (FaithfulClock.ratCount P.C).mulVec 0 := by
    ext i
    simpa [Matrix.mulVec_single_one, FaithfulClock.Clock.countTable, FaithfulClock.ratCount] using hcol i
  have hinj := P.full_column_rank hkernel
  have hval := congrFun hinj (topIndex P)
  simp at hval

end Clock

/-- Rational falling-factorial polynomial used in the mathematical proof. -/
noncomputable def fallingPoly : ℕ → ℚ[X]
  | 0 => 1
  | n + 1 => fallingPoly n * (Polynomial.X - Polynomial.C (n : ℚ))

theorem fallingPoly_eq_descPochhammer (n : ℕ) : fallingPoly n = descPochhammer ℚ n := by
  induction n with
  | zero => simp [fallingPoly]
  | succ n ih => simp [fallingPoly, ih, descPochhammer_succ_right]

/-- Ordinary rational polynomial for a row of the binomial table. -/
noncomputable def rowPoly {k : ℕ} (c : Fin k → ℚ) : ℚ[X] :=
  ∑ j : Fin k, Polynomial.C (c j / (j.val.factorial : ℚ)) * fallingPoly j.val

theorem rowPoly_eval_nat {k : ℕ} (c : Fin k → ℚ) (q : ℕ) :
    (rowPoly c).eval (q : ℚ) = ∑ j : Fin k, c j * (Nat.choose q j.val : ℚ) := by
  simp only [rowPoly, fallingPoly_eq_descPochhammer, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    Nat.cast_choose_eq_descPochhammer_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rat_descPochhammer_degree (d : ℕ) : (descPochhammer ℚ d).degree = d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [descPochhammer_succ_right, Polynomial.degree_mul, ih]
    have hc : (d : ℚ[X]) = Polynomial.C (d : ℚ) := by simp
    rw [hc, Polynomial.degree_X_sub_C]
    simp

theorem rowPoly_natDegree_le {k : ℕ} (c : Fin k → ℚ) : (rowPoly c).natDegree ≤ k - 1 := by
  unfold rowPoly
  simp_rw [fallingPoly_eq_descPochhammer]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have hn : (descPochhammer ℚ j.val).natDegree = j.val :=
    Polynomial.natDegree_eq_of_degree_eq_some (rat_descPochhammer_degree j.val)
  rw [hn]
  omega

theorem rowPoly_top_coeff {k : ℕ} (hk : 0 < k) (c : Fin k → ℚ) :
    (rowPoly c).coeff (k - 1) = c ⟨k - 1, by omega⟩ / ((k - 1).factorial : ℚ) := by
  simp only [rowPoly, fallingPoly_eq_descPochhammer, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · have hn : (descPochhammer ℚ (k - 1)).natDegree = k - 1 :=
      Polynomial.natDegree_eq_of_degree_eq_some (rat_descPochhammer_degree (k - 1))
    have hm := monic_descPochhammer ℚ (k - 1)
    have hc : (descPochhammer ℚ (k - 1)).coeff (k - 1) = 1 := by
      simpa [Polynomial.Monic, Polynomial.leadingCoeff, hn] using hm
    simp [hc]
  · intro j _ hj
    have hjlt : j.val < k - 1 := by
      have hjne : j.val ≠ k - 1 := by
        intro h
        exact hj (Fin.ext h)
      omega
    have hz : (descPochhammer ℚ j.val).coeff (k - 1) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (by simpa [rat_descPochhammer_degree] using hjlt)
    simp [hz]
  · simp

/-- Finite rational coefficient bound; no choice of an asymptotic witness. -/
def coeffMass (P : ℚ[X]) (n : ℕ) : ℚ := ∑ j ∈ Finset.range n, |P.coeff j|

theorem coeffMass_nonneg (P : ℚ[X]) (n : ℕ) : 0 ≤ coeffMass P n := by
  exact Finset.sum_nonneg (fun j _ => abs_nonneg _)

theorem polynomial_upper_bound (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d)
    (x : ℚ) (hx : 1 ≤ x) : P.eval x ≤ coeffMass P (d + 1) * x ^ d := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < d + 1)]
  unfold coeffMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  calc
    P.coeff j * x ^ j ≤ |P.coeff j| * x ^ j :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith) _)
    _ ≤ |P.coeff j| * x ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hjd) (abs_nonneg _)

theorem polynomial_lower_bound (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d)
    (x : ℚ) (hx : 1 ≤ x) :
    P.coeff d * x ^ d - coeffMass P d * x ^ (d - 1) ≤ P.eval x := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < d + 1), Finset.sum_range_succ]
  have hl : -(coeffMass P d * x ^ (d - 1)) ≤
      ∑ j ∈ Finset.range d, P.coeff j * x ^ j := by
    unfold coeffMass
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hjd : j ≤ d - 1 := by have := Finset.mem_range.mp hj; omega
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx hjd) (abs_nonneg (P.coeff j))
    have hc := mul_le_mul_of_nonneg_right (neg_abs_le (P.coeff j))
      (pow_nonneg (by linarith : 0 ≤ x) j)
    linarith
  linarith

/-- Entirely explicit rational-coefficient threshold for `G(x) ≤ eps P(x)`.
It depends on `eps` only through the final quotient; there is no additive error. -/
def dominationThreshold (P G : ℚ[X]) (d : ℕ) (eps : ℚ) : ℕ :=
  max 1 (max ⌈2 * coeffMass P d / P.coeff d⌉₊
    ⌈2 * coeffMass G d / (eps * P.coeff d)⌉₊)

theorem polynomial_domination (P G : ℚ[X]) {d : ℕ} (hd : 0 < d)
    (hP : P.natDegree ≤ d) (hG : G.natDegree ≤ d - 1) (hL : 0 < P.coeff d)
    {eps : ℚ} (heps : 0 < eps) {q : ℕ} (hq : dominationThreshold P G d eps ≤ q) :
    G.eval (q : ℚ) ≤ eps * P.eval (q : ℚ) := by
  have hq1 : (1 : ℚ) ≤ q := by
    exact_mod_cast (le_trans (le_max_left 1 _) hq)
  have hBnat : ⌈2 * coeffMass P d / P.coeff d⌉₊ ≤ q :=
    (le_trans (le_max_left _ _) (le_max_right 1 _)).trans hq
  have hDnat : ⌈2 * coeffMass G d / (eps * P.coeff d)⌉₊ ≤ q :=
    (le_trans (le_max_right _ _) (le_max_right 1 _)).trans hq
  have hB : 2 * coeffMass P d ≤ (q : ℚ) * P.coeff d := by
    apply (div_le_iff₀ hL).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast hBnat)
  have hD : 2 * coeffMass G d ≤ (q : ℚ) * (eps * P.coeff d) := by
    apply (div_le_iff₀ (mul_pos heps hL)).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast hDnat)
  have hpow : (q : ℚ) ^ d = (q : ℚ) ^ (d - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow0 : 0 ≤ (q : ℚ) ^ (d - 1) := by positivity
  have hl := polynomial_lower_bound P d hP q hq1
  have hu := polynomial_upper_bound G (d - 1) hG q hq1
  have hds : d - 1 + 1 = d := by omega
  rw [hds] at hu
  have hBmul := mul_le_mul_of_nonneg_right hB hpow0
  have hDmul := mul_le_mul_of_nonneg_right hD hpow0
  have hhalflower : P.coeff d * (q : ℚ) ^ d / 2 ≤ P.eval (q : ℚ) := by
    rw [hpow] at hl ⊢
    nlinarith [hBmul]
  have hhalf := mul_le_mul_of_nonneg_left hhalflower heps.le
  rw [hpow] at hhalf
  nlinarith [hDmul]

theorem rowPoly_natDegree_le_of_vanishing {k d : ℕ} (c : Fin k → ℚ)
    (hc : ∀ j : Fin k, d < j.val → c j = 0) : (rowPoly c).natDegree ≤ d := by
  unfold rowPoly
  simp_rw [fallingPoly_eq_descPochhammer]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  by_cases hj : j.val ≤ d
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    have hn : (descPochhammer ℚ j.val).natDegree = j.val :=
      Polynomial.natDegree_eq_of_degree_eq_some (rat_descPochhammer_degree j.val)
    simpa [hn] using hj
  · simp [hc j (by omega : d < j.val)]

/-- Executable rational coefficients of `X(X-1)...(X-n+1)`. -/
def fallingCoeff : ℕ → ℕ → ℚ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, 0 => -(n : ℚ) * fallingCoeff n 0
  | n + 1, j + 1 => fallingCoeff n j - (n : ℚ) * fallingCoeff n (j + 1)

theorem fallingCoeff_eq (n j : ℕ) : fallingCoeff n j = (fallingPoly n).coeff j := by
  induction n generalizing j with
  | zero => simp [fallingCoeff, fallingPoly, Polynomial.coeff_one]
  | succ n ih =>
    cases j with
    | zero => simp [fallingCoeff, fallingPoly, mul_sub, ih]; ring
    | succ j => simp [fallingCoeff, fallingPoly, mul_sub, Polynomial.coeff_mul_X, ih]; ring

/-- Executable conversion from binomial to ordinary rational coefficients. -/
def rowCoeff {k : ℕ} (c : Fin k → ℚ) (n : ℕ) : ℚ :=
  ∑ j : Fin k, (c j / (j.val.factorial : ℚ)) * fallingCoeff j.val n

theorem rowCoeff_eq {k : ℕ} (c : Fin k → ℚ) (n : ℕ) : rowCoeff c n = (rowPoly c).coeff n := by
  simp [rowCoeff, rowPoly, fallingCoeff_eq, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]

def rowCoeffMass {k : ℕ} (c : Fin k → ℚ) (d : ℕ) : ℚ :=
  ∑ j ∈ Finset.range d, |rowCoeff c j|

/-- Executable threshold using only finite rational arithmetic, factorials,
absolute values, and natural ceilings of rational quotients. -/
def rowDominationThreshold {k : ℕ} (c g : Fin k → ℚ) (d : ℕ) (eps : ℚ) : ℕ :=
  max 1 (max ⌈2 * rowCoeffMass c d / rowCoeff c d⌉₊
    ⌈2 * rowCoeffMass g d / (eps * rowCoeff c d)⌉₊)

theorem rowDominationThreshold_eq {k : ℕ} (c g : Fin k → ℚ) (d : ℕ) (eps : ℚ) :
    rowDominationThreshold c g d eps = dominationThreshold (rowPoly c) (rowPoly g) d eps := by
  simp only [rowDominationThreshold, dominationThreshold, rowCoeffMass, coeffMass, rowCoeff_eq]

namespace Clock

variable {k : ℕ} (P : FaithfulClock.Clock k)

def totalCountCoeff (j : Fin k) : ℚ := ∑ i : Fin P.m, P.countTable i j

def heightGainCoeff (j : Fin k) : ℚ := (P.R * N_mat k) P.b j

noncomputable def lengthPoly : ℚ[X] := rowPoly (totalCountCoeff P)

noncomputable def heightGainPoly : ℚ[X] := rowPoly (heightGainCoeff P)

theorem lengthPoly_eval (q : ℕ) (hq : P.Q ≤ q) :
    (lengthPoly P).eval (q : ℚ) = ((P.word q).length : ℚ) := by
  rw [lengthPoly, rowPoly_eval_nat, list_length_eq_sum_wordCountVec, P.counts q hq]
  simp only [totalCountCoeff, Matrix.mulVec, dotProduct, binomBasis,
    FaithfulClock.Clock.countTable, FaithfulClock.ratCount, Finset.sum_mul]
  exact Finset.sum_comm

theorem lengthPoly_top_pos : 0 < (lengthPoly P).coeff (k - 1) := by
  rw [lengthPoly, rowPoly_top_coeff (by have := P.order_ge_two; omega)]
  exact div_pos (leading_total_count_pos P) (by positivity)

theorem heightGainCoeff_top : heightGainCoeff P (topIndex P) = 0 := by
  unfold heightGainCoeff
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val ≠ (k - 1) + 1 := by
    have := i.isLt
    have := P.order_ge_two
    omega
  simp [N_mat, topIndex, hi]

theorem heightGainPoly_degree : (heightGainPoly P).natDegree ≤ k - 2 := by
  apply rowPoly_natDegree_le_of_vanishing
  intro j hj
  have hjeq : j = topIndex P := by
    apply Fin.ext
    have := j.isLt
    have := P.order_ge_two
    simp only [topIndex]
    omega
  rw [hjeq]
  exact heightGainCoeff_top P

theorem heightGainPoly_eval (q : ℕ) (hq : P.Q ≤ q) :
    (heightGainPoly P).eval (q : ℚ) =
      FaithfulClock.height P.b (P.entry (q + 1)) - FaithfulClock.height P.b (P.entry q) := by
  rw [P.entry_height (q + 1) (by omega), P.entry_height q hq]
  rw [heightGainPoly, rowPoly_eval_nat]
  have h := congrFun (congrArg P.R.mulVec (binomBasis_succ_sub k q)) P.b
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec] at h
  simpa [heightGainCoeff, FaithfulClock.Clock.entry, Matrix.mulVec, dotProduct, binomBasis] using h.symm

/-- Explicit whole-phase threshold, computed from the fixed rational count and
score tables and `eps`. The clock's additive suffix constant is absent. -/
def wholePhaseThreshold (eps : ℚ) : ℕ :=
  max P.Q (rowDominationThreshold (totalCountCoeff P) (heightGainCoeff P) (k - 1) eps)

theorem whole_phase_gain_le {eps : ℚ} (heps : 0 < eps) {q : ℕ}
    (hq : wholePhaseThreshold P eps ≤ q) :
    FaithfulClock.height P.b (P.entry (q + 1)) - FaithfulClock.height P.b (P.entry q) ≤
      eps * ((P.word q).length : ℚ) := by
  have hQ : P.Q ≤ q := (le_max_left _ _).trans hq
  have hbound : dominationThreshold (lengthPoly P) (heightGainPoly P) (k - 1) eps ≤ q := by
    rw [lengthPoly, heightGainPoly, ← rowDominationThreshold_eq]
    exact (le_max_right _ _).trans hq
  have hdom := polynomial_domination (lengthPoly P) (heightGainPoly P)
    (by have := P.order_ge_two; omega : 0 < k - 1)
    (rowPoly_natDegree_le (totalCountCoeff P))
    (by simpa only [Nat.sub_sub] using heightGainPoly_degree P)
    (lengthPoly_top_pos P) heps hbound
  rwa [heightGainPoly_eval P q hQ, lengthPoly_eval P q hQ] at hdom

/-- One effective onset for partial-phase and whole-phase suffix estimates. -/
def bundleThreshold (eps : ℚ) : ℕ := max (P.threshold eps) (wholePhaseThreshold P eps)

/-- Arbitrary consecutive compatible windows inherit the exact same additive
suffix constant. Only the current partial phase charges `P.Arem`. -/
theorem consecutive_suffix {eps : ℚ} (heps : 0 < eps) (a n r : ℕ)
    (ha : bundleThreshold P eps ≤ a)
    (hr : r ≤ (FaithfulWindow.consecutiveWord P.word a n).length) :
    FaithfulClock.height P.b (P.entry (a + n)) -
      FaithfulClock.height P.b (wordScore P.A (P.entry a)
        ((FaithfulWindow.consecutiveWord P.word a n).take r)) ≤
      eps * ((FaithfulWindow.consecutiveWord P.word a n).length - r : ℕ) + P.Arem := by
  have honset : P.Q ≤ bundleThreshold P eps :=
    (P.threshold_onset eps heps).trans (le_max_left _ _)
  apply FaithfulWindow.consecutiveWord_suffix P.A P.word P.entry
    (FaithfulClock.height P.b) (bundleThreshold P eps) eps P.Arem P.remainder_nonneg
    (fun q hq => P.phase_transition q (honset.trans hq))
    (fun q hq => P.suffix eps heps q ((le_max_left _ _).trans hq))
    (fun q hq => whole_phase_gain_le P heps ((le_max_right _ _).trans hq)) a ha n r hr

/-- Literal v15 dyadic moving window `[tau*q,2*tau*q)`, with one common
threshold and the parent's unchanged additive constant. -/
theorem dyadic_suffix {eps : ℚ} (heps : 0 < eps) (tau q r : ℕ)
    (hq : bundleThreshold P eps ≤ tau * q)
    (hr : r ≤ (FaithfulWindow.dyadicWord P.word tau q).length) :
    FaithfulClock.height P.b (P.entry (2 * tau * q)) -
      FaithfulClock.height P.b (wordScore P.A (P.entry (tau * q))
        ((FaithfulWindow.dyadicWord P.word tau q).take r)) ≤
      eps * ((FaithfulWindow.dyadicWord P.word tau q).length - r : ℕ) + P.Arem := by
  have h := consecutive_suffix P heps (tau * q) (tau * q) r hq hr
  have he : tau * q + tau * q = 2 * tau * q := by ring
  simpa [FaithfulWindow.dyadicWord, he] using h

end Clock

end Karlin.FaithfulGrowth
