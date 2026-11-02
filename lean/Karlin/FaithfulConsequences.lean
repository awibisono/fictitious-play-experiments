import Karlin.FaithfulMain
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Positive payoff normalization and rate consequences for the actual v15
family. These corollaries do not identify the family with the separate numeric
appendix examples or certify the simulation files. -/
namespace Karlin.FaithfulConsequences
open scoped BigOperators
open Filter Topology Asymptotics

def scale {α : Type*} (c : ℚ) (M : Matrix α α ℚ) : Matrix α α ℚ :=
  fun i j => c * M i j

theorem scale_skew {α : Type*} (c : ℚ) {M : Matrix α α ℚ}
    (hM : IsSkewSymmetric M) : IsSkewSymmetric (scale c M) := by
  intro i j
  simp [scale, hM i j]

theorem cumScore_scale {α : Type*} (c : ℚ) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : α) :
    cumScore (scale c M) a t i = c * cumScore M a t i := by
  simp [cumScore, scale, Finset.mul_sum]

theorem strict_scale_iff {α : Type*} {c : ℚ} (hc : 0 < c)
    (M : Matrix α α ℚ) (a : ℕ → α) :
    IsStrictFPTrajectory (scale c M) a ↔ IsStrictFPTrajectory M a := by
  simp only [IsStrictFPTrajectory, cumScore_scale, mul_lt_mul_iff_right₀ hc]

theorem rowCumPayoff_scale {α : Type*} (c : ℚ) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : α) :
    rowCumPayoff (scale c M) a t i = c * rowCumPayoff M a t i := by
  simp [rowCumPayoff, scale, Finset.mul_sum]

theorem colCumLoss_scale {α : Type*} (c : ℚ) (M : Matrix α α ℚ)
    (a : ℕ → α) (t : ℕ) (i : α) :
    colCumLoss (scale c M) a t i = c * colCumLoss M a t i := by
  simp [colCumLoss, scale, Finset.mul_sum]

theorem strictTwoPlayer_scale_iff {α : Type*} {c : ℚ} (hc : 0 < c)
    (M : Matrix α α ℚ) (row col : ℕ → α) :
    IsStrictTwoPlayerFPTrajectory (scale c M) row col ↔
      IsStrictTwoPlayerFPTrajectory M row col := by
  simp only [IsStrictTwoPlayerFPTrajectory, rowCumPayoff_scale, colCumLoss_scale,
    mul_lt_mul_iff_right₀ hc]

theorem weakTwoPlayer_scale_iff {α : Type*} {c : ℚ} (hc : 0 < c)
    (M : Matrix α α ℚ) (row col : ℕ → α) :
    IsWeakTwoPlayerFPTrajectory (scale c M) row col ↔
      IsWeakTwoPlayerFPTrajectory M row col := by
  simp only [IsWeakTwoPlayerFPTrajectory, rowCumPayoff_scale, colCumLoss_scale,
    mul_le_mul_iff_right₀ hc]

/-- Standard max-minus-min gap scales for any two empirical strategies,
including time zero; no strictness or skewness is needed. -/
theorem standardGap_scale {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {c : ℚ} (hc : 0 ≤ c) (M : Matrix α α ℚ) (row col : ℕ → α) (t : ℕ) :
    standardDualityGap (scale c M) row col t = c * standardDualityGap M row col t := by
  have hr (i : α) : empiricalRowPayoff (scale c M) col t i =
      c * empiricalRowPayoff M col t i := by
    simp [empiricalRowPayoff, scale, Finset.mul_sum, mul_assoc]
  have hh (i : α) : empiricalColPayoff (scale c M) row t i =
      c * empiricalColPayoff M row t i := by
    simp [empiricalColPayoff, scale, Finset.mul_sum, mul_left_comm]
  have hm : Monotone (fun x : ℚ => c*x) := fun _ _ h => mul_le_mul_of_nonneg_left h hc
  have hs := Finset.comp_sup'_eq_sup'_comp
    (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty)
    (f := empiricalRowPayoff M col t) (fun x : ℚ => c*x) (fun x y => hm.map_sup x y)
  have hi := Finset.comp_inf'_eq_inf'_comp
    (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty)
    (f := empiricalColPayoff M row t) (fun x : ℚ => c*x) (fun x y => hm.map_inf x y)
  simp only [Function.comp_def] at hs hi
  simp only [standardDualityGap, hr, hh, ← hs, ← hi, mul_sub]

def maxEntry {α : Type*} [Fintype α] [Nonempty α] (M : Matrix α α ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : α × α => |M p.1 p.2|)

theorem abs_entry_le_max {α : Type*} [Fintype α] [Nonempty α]
    (M : Matrix α α ℚ) (i j : α) : |M i j| ≤ maxEntry M :=
  Finset.le_sup' (fun p : α × α => |M p.1 p.2|) (Finset.mem_univ (i,j))

theorem maxEntry_pos_of_nonzero {α : Type*} [Fintype α] [Nonempty α]
    (M : Matrix α α ℚ) (h : ∃ i j, M i j ≠ 0) : 0 < maxEntry M := by
  obtain ⟨i,j,hij⟩ := h
  exact (abs_pos.mpr hij).trans_le (abs_entry_le_max M i j)

def normalize {α : Type*} [Fintype α] [Nonempty α] (M : Matrix α α ℚ) : Matrix α α ℚ :=
  scale (1 / maxEntry M) M

theorem normalized_entry_bound {α : Type*} [Fintype α] [Nonempty α]
    (M : Matrix α α ℚ) (hM : 0 < maxEntry M) (i j : α) :
    -1 ≤ normalize M i j ∧ normalize M i j ≤ 1 := by
  have ha := abs_entry_le_max M i j
  have hab : |normalize M i j| ≤ 1 := by
    simp only [normalize, scale, abs_mul, abs_div, abs_one, abs_of_pos hM]
    rw [one_div_mul_eq_div]
    exact (div_le_one hM).mpr ha
  exact abs_le.mp hab

open FaithfulMain

theorem family_matrix_nonzero (k : ℕ) (hk : 2 ≤ k) :
    ∃ i j, matrix k hk i j ≠ 0 := by
  by_contra! hz
  have hm : 0 < (clock k hk).m := (clock k hk).b.isLt |> Nat.zero_lt_of_lt
  let one : Fin ((clock k hk).m+1) := ⟨1, by omega⟩
  have ho : one ≠ 0 := by intro h; have := congrArg Fin.val h; simp [one] at this
  obtain ⟨j,hj⟩ : ∃ j : Fin ((clock k hk).m+1), j ≠ trajectory k hk 1 := by
    by_cases h : trajectory k hk 1 = 0
    · exact ⟨one, by simpa [h] using ho⟩
    · exact ⟨0, Ne.symm h⟩
  have hs := strict k hk 1 (by omega) j hj
  simp [cumScore, hz] at hs

theorem family_maxEntry_pos (k : ℕ) (hk : 2 ≤ k) : 0 < maxEntry (matrix k hk) :=
  maxEntry_pos_of_nonzero _ (family_matrix_nonzero k hk)

noncomputable def normalizedMatrix (k : ℕ) (hk : 2 ≤ k) := normalize (matrix k hk)

noncomputable def normalizedConstant (k : ℕ) (hk : 2 ≤ k) : ℝ :=
  constant k hk / (maxEntry (matrix k hk) : ℝ)

theorem normalized_skew (k : ℕ) (hk : 2 ≤ k) : IsSkewSymmetric (normalizedMatrix k hk) :=
  scale_skew _ (skew k hk)

theorem normalized_entries (k : ℕ) (hk : 2 ≤ k)
    (i j : Fin ((clock k hk).m+1)) :
    -1 ≤ normalizedMatrix k hk i j ∧ normalizedMatrix k hk i j ≤ 1 :=
  normalized_entry_bound _ (family_maxEntry_pos k hk) i j

theorem normalized_strict (k : ℕ) (hk : 2 ≤ k) :
    IsStrictFPTrajectory (normalizedMatrix k hk) (trajectory k hk) :=
  (strict_scale_iff (one_div_pos.mpr (family_maxEntry_pos k hk)) _ _).mpr (strict k hk)

theorem normalized_strict_simultaneous (k : ℕ) (hk : 2 ≤ k) :
    IsStrictTwoPlayerFPTrajectory (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) :=
  (strictTwoPlayer_scale_iff (one_div_pos.mpr (family_maxEntry_pos k hk)) _ _ _).mpr
    (strict_simultaneous k hk)

theorem normalized_unique (k : ℕ) (hk : 2 ≤ k)
    (row col : ℕ → Fin ((clock k hk).m+1))
    (hw : IsWeakTwoPlayerFPTrajectory (normalizedMatrix k hk) row col)
    (hr : row 0 = 0) (hc : col 0 = 0) (t : ℕ) :
    row t = trajectory k hk t ∧ col t = trajectory k hk t :=
  unique_from_common_setup k hk row col
    ((weakTwoPlayer_scale_iff (one_div_pos.mpr (family_maxEntry_pos k hk)) _ _ _).mp hw)
    hr hc t

theorem normalized_gap (k : ℕ) (hk : 2 ≤ k) (t : ℕ) :
    standardDualityGap (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) t =
      standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t /
        maxEntry (matrix k hk) := by
  exact (standardGap_scale (one_div_pos.mpr (family_maxEntry_pos k hk)).le _ _ _ _).trans
    (one_div_mul_eq_div _ _)

theorem normalized_exact_gap (k : ℕ) (hk : 2 ≤ k) :
    0 < normalizedConstant k hk ∧
    Tendsto (fun t : ℕ =>
      (standardDualityGap (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) *
        (t : ℝ) ^ (1/(k : ℝ))) atTop (𝓝 (normalizedConstant k hk)) := by
  have hM : (0 : ℝ) < (maxEntry (matrix k hk) : ℝ) := by
    exact_mod_cast family_maxEntry_pos k hk
  refine ⟨div_pos (exact_gap k hk).1 hM, ?_⟩
  have hh := (exact_gap k hk).2.div_const (maxEntry (matrix k hk) : ℝ)
  simpa only [normalized_gap, Rat.cast_div, div_mul_eq_mul_div, normalizedConstant] using hh

theorem normalized_relative_error (k : ℕ) (hk : 2 ≤ k) :
    (fun t : ℕ =>
      (standardDualityGap (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) /
        (normalizedConstant k hk * (t : ℝ) ^ (-(1/(k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1/(k : ℝ)))) := by
  have hM : (maxEntry (matrix k hk) : ℝ) ≠ 0 := by
    exact_mod_cast (family_maxEntry_pos k hk).ne'
  have he (t : ℕ) :
      (standardDualityGap (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) /
        (normalizedConstant k hk * (t : ℝ) ^ (-(1/(k : ℝ)))) =
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) /
        (constant k hk * (t : ℝ) ^ (-(1/(k : ℝ)))) := by
    rw [normalized_gap, Rat.cast_div, normalizedConstant, div_mul_eq_mul_div,
      div_div_div_cancel_right₀ hM]
  simpa only [he] using relative_error k hk

theorem normalized_all_integer_theta (k : ℕ) (hk : 2 ≤ k) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      (normalizedConstant k hk/2) * (t:ℝ)^(-(1/(k:ℝ))) ≤
        (standardDualityGap (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) ∧
      (standardDualityGap (normalizedMatrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) ≤
        (2*normalizedConstant k hk) * (t:ℝ)^(-(1/(k:ℝ))) := by
  have hM : (0:ℝ) < (maxEntry (matrix k hk) : ℝ) := by
    exact_mod_cast family_maxEntry_pos k hk
  obtain ⟨T,hT,ht⟩ := all_integer_theta k hk
  refine ⟨T,hT,fun t htT => ?_⟩
  obtain ⟨hlo,hhi⟩ := ht t htT
  rw [normalized_gap, Rat.cast_div]
  constructor
  · convert div_le_div_of_nonneg_right hlo hM.le using 1
    simp only [normalizedConstant]
    ring
  · convert div_le_div_of_nonneg_right hhi hM.le using 1
    simp only [normalizedConstant]
    ring

/-- Rational kth-power form of the prefactor, exactly as displayed in Appendix
A.2. The factorial normalization is that of the binomial basis. -/
theorem paperGapConstant_power (k : ℕ) (hk : 2 ≤ k) (L xi : ℝ) (hL : 0 < L) :
    (FaithfulRate.paperGapConstant k L xi)^k =
      (2:ℝ)^k * (k:ℝ)^(k-1) * xi^k /
        (((k-1).factorial:ℝ) * L^(k-1)) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hfpos : (0:ℝ) < (k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hgpos : (0:ℝ) < ((k-1).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_pos (k-1)
  have hbase : 0 < L/(k.factorial:ℝ) := div_pos hL hfpos
  have he : (-((k-1:ℕ):ℝ)/(k:ℝ)) * (k:ℝ) = -((k-1:ℕ):ℝ) :=
    div_mul_cancel₀ _ hkpos.ne'
  have hp : ((L/(k.factorial:ℝ))^(-((k-1:ℕ):ℝ)/(k:ℝ)))^k =
      (k.factorial:ℝ)^(k-1) / L^(k-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le, he,
      Real.rpow_neg hbase.le, Real.rpow_natCast, div_pow, inv_div]
  have hn : k-1+1=k := by omega
  have hfac : (k.factorial:ℝ) = (k:ℝ)*((k-1).factorial:ℝ) := by
    have hh := Nat.factorial_succ (k-1)
    rw [hn] at hh
    exact_mod_cast hh
  have hfpow : ((k-1).factorial:ℝ)^k =
      ((k-1).factorial:ℝ)^(k-1) * ((k-1).factorial:ℝ) := by
    calc
      _ = ((k-1).factorial:ℝ)^(k-1+1) := congrArg (fun n => ((k-1).factorial:ℝ)^n) hn.symm
      _ = _ := pow_succ _ _
  unfold FaithfulRate.paperGapConstant
  rw [mul_pow, mul_pow, div_pow, hp, hfac, mul_pow, hfpow]
  field_simp

theorem family_constant_power (k : ℕ) (hk : 2 ≤ k) :
    (constant k hk)^k =
      (2:ℝ)^k * (k:ℝ)^(k-1) * (FaithfulRealization.scoreCoeff (clock k hk) (k-1))^k /
        (((k-1).factorial:ℝ) * (FaithfulRealization.countCoeff (clock k hk) (k-1))^(k-1)) := by
  have htop : k-1<k := by omega
  have hL : 0 < FaithfulRealization.countCoeff (clock k hk) (k-1) := by
    simp only [FaithfulRealization.countCoeff, FaithfulRealization.extendRow, dif_pos htop]
    exact_mod_cast FaithfulGrowth.Clock.leading_total_count_pos (clock k hk)
  exact paperGapConstant_power k hk _ _ hL

noncomputable def leadingCount (k : ℕ) (hk : 2 ≤ k) : ℚ :=
  ∑ i : Fin ((clock k hk).m), (clock k hk).countTable i ⟨k-1, by omega⟩

noncomputable def leadingHeight (k : ℕ) (hk : 2 ≤ k) : ℚ :=
  (clock k hk).R (clock k hk).b ⟨k-1, by omega⟩

theorem leadingCount_pos (k : ℕ) (hk : 2 ≤ k) : 0 < leadingCount k hk :=
  FaithfulGrowth.Clock.leading_total_count_pos (clock k hk)

theorem leadingHeight_pos (k : ℕ) (hk : 2 ≤ k) : 0 < leadingHeight k hk :=
  (clock k hk).leading_height

/-- In particular the kth power of the exact constant is a positive rational
expression in the literal count and height tables. -/
theorem family_constant_power_rational (k : ℕ) (hk : 2 ≤ k) :
    (constant k hk)^k =
      (((2:ℚ)^k * (k:ℚ)^(k-1) * (leadingHeight k hk)^k /
        (((k-1).factorial:ℚ) * (leadingCount k hk)^(k-1)) : ℚ) : ℝ) := by
  have htop : k-1<k := by omega
  have hh := family_constant_power k hk
  simpa only [FaithfulRealization.countCoeff, FaithfulRealization.scoreCoeff,
    FaithfulRealization.extendRow, dif_pos htop, leadingCount, leadingHeight,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using hh

theorem normalized_constant_power (k : ℕ) (hk : 2 ≤ k) :
    (normalizedConstant k hk)^k =
      (((2:ℚ)^k * (k:ℚ)^(k-1) * (leadingHeight k hk)^k /
        (((k-1).factorial:ℚ) * (leadingCount k hk)^(k-1) *
          (maxEntry (matrix k hk))^k) : ℚ) : ℝ) := by
  rw [normalizedConstant, div_pow, family_constant_power_rational]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow]
  rw [div_div]

/-- A positive exact power-law limit rules out every strictly faster big-O
rate, even when its implicit constant depends on the game and initialization. -/
theorem not_faster_rate {g : ℕ → ℝ} {c r gamma : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun t : ℕ => g t * (t:ℝ)^r) atTop (𝓝 c))
    (hgamma : r < gamma) : ¬ g =O[atTop] (fun t : ℕ => (t:ℝ)^(-gamma)) := by
  intro ho
  have hm := IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-gamma) r (r-gamma)
    ho (isBigO_refl (fun t : ℕ => (t:ℝ)^r) atTop) (by linarith)
  have hz : Tendsto (fun t : ℕ => (t:ℝ)^(r-gamma)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hgamma)).comp tendsto_natCast_atTop_atTop
  exact hc.ne' (tendsto_nhds_unique hlim (hm.trans_tendsto hz))

theorem family_not_faster (k : ℕ) (hk : 2 ≤ k) (gamma : ℝ)
    (hgamma : 1/(k:ℝ) < gamma) :
    ¬ (fun t : ℕ => (standardDualityGap (matrix k hk) (trajectory k hk)
        (trajectory k hk) t : ℝ)) =O[atTop] (fun t : ℕ => (t:ℝ)^(-gamma)) :=
  not_faster_rate (exact_gap k hk).1 (exact_gap k hk).2 hgamma

theorem normalized_not_faster (k : ℕ) (hk : 2 ≤ k) (gamma : ℝ)
    (hgamma : 1/(k:ℝ) < gamma) :
    ¬ (fun t : ℕ => (standardDualityGap (normalizedMatrix k hk) (trajectory k hk)
        (trajectory k hk) t : ℝ)) =O[atTop] (fun t : ℕ => (t:ℝ)^(-gamma)) :=
  not_faster_rate (normalized_exact_gap k hk).1 (normalized_exact_gap k hk).2 hgamma

theorem exists_order_slower_than (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ k : ℕ, 2 ≤ k ∧ 1/(k:ℝ) < gamma := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 2 (1/gamma))
  have hk2 : (2:ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hn : 2 ≤ k := by exact_mod_cast hk2.le
  have hkpos : (0:ℝ) < k := by linarith
  have hkg : 1/gamma < (k:ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  refine ⟨k,hn,(div_lt_iff₀ hkpos).mpr ?_⟩
  simpa only [mul_comm] using (div_lt_iff₀ hgamma).mp hkg

/-- The no-universal-exponent corollary, already on rational games normalized
to [-1,1], with the same prescribed action 0 and strict simultaneous responses. -/
theorem no_universal_polynomial_exponent :
    ¬ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ (m : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ) (a : ℕ → Fin (m+1)),
        IsSkewSymmetric M → (∀ i j, -1 ≤ M i j ∧ M i j ≤ 1) → a 0 = 0 →
        IsStrictTwoPlayerFPTrajectory M a a →
        (fun t : ℕ => (standardDualityGap M a a t : ℝ))
          =O[atTop] (fun t : ℕ => (t:ℝ)^(-gamma)) := by
  rintro ⟨gamma,hgamma,huniv⟩
  obtain ⟨k,hk,hkg⟩ := exists_order_slower_than gamma hgamma
  exact normalized_not_faster k hk gamma hkg
    (huniv (clock k hk).m (normalizedMatrix k hk) (trajectory k hk)
      (normalized_skew k hk) (normalized_entries k hk) (common_initial_action k hk)
      (normalized_strict_simultaneous k hk))

end Karlin.FaithfulConsequences
