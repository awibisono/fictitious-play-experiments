import Karlin.FaithfulSevenData

/-! The seven-action seed's remaining-height estimate. Pure-run spacing charges
the additive constant once, including prefixes at every run boundary. -/
namespace Karlin.FaithfulSevenSuffix
open scoped BigOperators
open FaithfulClock FaithfulWindow

/-- A valid pure run can gain at most one at its final switching instant when
all payoff entries are at most one. Its height is constant before that instant. -/
theorem pure_run_suffix {m rnk : ℕ} (b a : Fin m)
    (M : Matrix (Fin m) (Fin m) ℚ) (hM : IsSkewSymmetric M)
    (hbound : ∀ i j, M i j ≤ 1) (rank : Fin m → Fin rnk)
    (s : Fin m → ℚ) (L : ℕ)
    (hv : IsValidPriorityWord M s rank (List.replicate L a)) (r : ℕ) (hr : r ≤ L) :
    height b (wordScore M s (List.replicate L a)) -
      height b (wordScore M s ((List.replicate L a).take r)) ≤ 1 := by
  rcases lt_or_eq_of_le hr with hr | rfl
  · have hL : 0 < L := by omega
    have hdom (u : ℕ) (hu : u < L) (i : Fin m) :
        s i + M i a * (u : ℚ) ≤ s a := by
      have hh := (hv u (by simpa using hu) i).1
      simpa [List.take_replicate, Nat.min_eq_left hu.le, wordScore_replicate,
        skew_diag_zero hM a] using hh
    have hp : height b (wordScore M s ((List.replicate L a).take r)) = s a := by
      rw [List.take_replicate, Nat.min_eq_left hr.le]
      have hh := height_eq b (wordScore M s (List.replicate r a)) a (fun i => by
        simpa [wordScore_replicate, skew_diag_zero hM a] using hdom r hr i)
      simpa [wordScore_replicate, skew_diag_zero hM a] using hh
    have he : height b (wordScore M s (List.replicate L a)) ≤ s a + 1 := by
      apply Finset.sup'_le
      intro i _
      rw [wordScore_replicate]
      have hh := hdom (L - 1) (by omega) i
      have hc : ((L - 1 : ℕ) : ℚ) = (L : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hc] at hh
      linarith [hbound i a]
    rw [hp]
    linarith
  · simp

/-- Finite version of the moving-window suffix sum. Only the runs that are
actually included need validity and gain estimates. -/
theorem finite_suffix {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ)
    (W : ℕ → List (Fin m)) (s : ℕ → Fin m → ℚ)
    (H : (Fin m → ℚ) → ℚ) (eps Arem : ℚ) (hArem : 0 ≤ Arem)
    (n : ℕ)
    (hscore : ∀ j, j ≤ n → wordScore M (s 0) (consecutiveWord W 0 j) = s j)
    (hlocal : ∀ j, j < n → ∀ r, r ≤ (W j).length →
      H (s (j+1)) - H (wordScore M (s j) ((W j).take r)) ≤
        eps * ((W j).length - r : ℕ) + Arem)
    (hwhole : ∀ j, j < n → H (s (j+1)) - H (s j) ≤ eps * (W j).length)
    (r : ℕ) (hr : r ≤ (consecutiveWord W 0 n).length) :
    H (s n) - H (wordScore M (s 0) ((consecutiveWord W 0 n).take r)) ≤
      eps * ((consecutiveWord W 0 n).length - r : ℕ) + Arem := by
  induction n with
  | zero =>
      have hr0 : r = 0 := by simpa [consecutiveWord] using hr
      simpa [hr0, consecutiveWord, wordScore_nil] using hArem
  | succ n ih =>
      have hsn : ∀ j, j ≤ n → wordScore M (s 0) (consecutiveWord W 0 j) = s j :=
        fun j hj => hscore j (by omega)
      have hln := fun j (hj : j < n) => hlocal j (by omega)
      have hwn := fun j (hj : j < n) => hwhole j (by omega)
      change r ≤ (consecutiveWord W 0 n ++ W (0+n)).length at hr
      simp only [zero_add] at hr
      by_cases hsmall : r ≤ (consecutiveWord W 0 n).length
      · have hprev := ih hsn hln hwn hsmall
        have hlast := hwhole n (by omega)
        have hlen : (consecutiveWord W 0 (n+1)).length - r =
            ((consecutiveWord W 0 n).length - r) + (W n).length := by
          simp only [consecutiveWord, zero_add, List.length_append]
          omega
        change H (s (n+1)) -
          H (wordScore M (s 0) ((consecutiveWord W 0 n ++ W (0+n)).take r)) ≤ _
        rw [zero_add, List.take_append_of_le_length hsmall, hlen, Nat.cast_add]
        linarith
      · have hle : (consecutiveWord W 0 n).length ≤ r := by omega
        have hu : r - (consecutiveWord W 0 n).length ≤ (W n).length := by
          rw [List.length_append] at hr
          omega
        have hp := hlocal n (by omega) (r - (consecutiveWord W 0 n).length) hu
        have hlen : (consecutiveWord W 0 (n+1)).length - r =
            (W n).length - (r - (consecutiveWord W 0 n).length) := by
          simp only [consecutiveWord, zero_add, List.length_append]
          omega
        change H (s (n+1)) -
          H (wordScore M (s 0) ((consecutiveWord W 0 n ++ W (0+n)).take r)) ≤ _
        rw [zero_add, List.take_append, List.take_of_length_le hle, wordScore_append,
          hscore n (by omega), hlen]
        exact hp

theorem seven_payoff_le_one (i j : Fin 6) : M_seven i j ≤ 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [M_seven]

theorem seven_run_spacing (p v : ℕ) : 126 * (p+20) + 61 ≤ sevenPhaseLen p v := by
  unfold sevenPhaseLen
  split
  · split <;> dsimp only <;> omega
  · split
    · omega
    · split <;> omega

/-- An executable rational threshold, selected after the fixed remainder 1. -/
def threshold (eps : ℚ) : ℕ := max 20 ⌈1 / eps⌉₊

theorem threshold_onset (eps : ℚ) : 20 ≤ threshold eps := le_max_left _ _

theorem threshold_spacing (eps : ℚ) (heps : 0 < eps) (q : ℕ)
    (hq : threshold eps ≤ q) : 1 ≤ eps * (126 * (q : ℚ) + 61) := by
  have hc : 1 / eps ≤ (q : ℚ) :=
    (Nat.le_ceil (1 / eps)).trans (by exact_mod_cast (le_max_right 20 ⌈1/eps⌉₊).trans hq)
  have hm := (div_le_iff₀ heps).mp hc
  have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  nlinarith

open FaithfulSevenData

theorem phase_suffix (eps : ℚ) (heps : 0 < eps) (p : ℕ)
    (hspacing : 1 ≤ eps * (126 * ((p : ℚ)+20) + 61)) (r : ℕ)
    (hr : r ≤ (phaseWord p).length) :
    height (0 : Fin 6) (V_seven ((p : ℚ)+20+1)) -
      height (0 : Fin 6)
        (wordScore M_seven (V_seven ((p : ℚ)+20)) ((phaseWord p).take r)) ≤
      eps * ((phaseWord p).length - r : ℕ) + 1 := by
  have hlocal (v : ℕ) (hv : v < sevenPhaseRunCount p) (u : ℕ)
      (hu : u ≤ (run p v).length) :
      height (0 : Fin 6) (sevenPhaseScore p (v+1)) -
        height (0 : Fin 6) (wordScore M_seven (sevenPhaseScore p v) ((run p v).take u)) ≤ 1 := by
    rw [← run_score p v hv]
    exact pure_run_suffix 0 (sevenPhaseAct p v) M_seven M_seven_skew seven_payoff_le_one
      (Equiv.refl (Fin 6)) (sevenPhaseScore p v) (sevenPhaseLen p v)
      (run_valid p v hv) u (by simpa [run] using hu)
  have hwhole (v : ℕ) (hv : v < sevenPhaseRunCount p) :
      height (0 : Fin 6) (sevenPhaseScore p (v+1)) -
        height (0 : Fin 6) (sevenPhaseScore p v) ≤ eps * (run p v).length := by
    have hl := hlocal v hv 0 (Nat.zero_le _)
    simp only [List.take_zero, wordScore_nil] at hl
    have hs : (126 * ((p : ℚ)+20) + 61) ≤ ((run p v).length : ℚ) := by
      simpa [run] using (show ((126*(p+20)+61 : ℕ) : ℚ) ≤ (sevenPhaseLen p v : ℚ)
        from by exact_mod_cast seven_run_spacing p v)
    exact hl.trans (hspacing.trans (mul_le_mul_of_nonneg_left hs heps.le))
  have hscore (v : ℕ) (hv : v ≤ sevenPhaseRunCount p) :
      wordScore M_seven (sevenPhaseScore p 0) (consecutiveWord (run p) 0 v) =
        sevenPhaseScore p v := by
    rw [phase_start]
    exact runs_score p v hv
  have hh := finite_suffix M_seven (run p) (sevenPhaseScore p) (height (0 : Fin 6))
    eps 1 (by norm_num) (sevenPhaseRunCount p) hscore
    (fun v hv u hu => (hlocal v hv u hu).trans (by
      have hn : 0 ≤ eps * ((run p v).length-u : ℕ) :=
        mul_nonneg heps.le (Nat.cast_nonneg _)
      linarith)) hwhole r hr
  simpa only [phase_start, phase_end, phaseWord, runs] using hh

/-- Condition III on the actual six recurrent actions, with the fixed additive
remainder exactly one. This includes the complete prefix and all run boundaries. -/
theorem seven_suffix (eps : ℚ) (heps : 0 < eps) (q : ℕ)
    (hq : threshold eps ≤ q) (r : ℕ) (hr : r ≤ (sevenWord q).length) :
    height (0 : Fin 6) (R_seven.mulVec (binomBasis 3 (q+1))) -
      height (0 : Fin 6)
        (wordScore M_seven (R_seven.mulVec (binomBasis 3 q)) ((sevenWord q).take r)) ≤
      eps * ((sevenWord q).length-r : ℕ) + 1 := by
  have h20 : 20 ≤ q := (threshold_onset eps).trans hq
  have he : ((q-20 : ℕ) : ℚ)+20 = (q : ℚ) := by
    rw [Nat.cast_sub h20]
    norm_num
  have hs : 1 ≤ eps * (126 * (((q-20 : ℕ) : ℚ)+20)+61) := by
    rw [he]
    exact threshold_spacing eps heps q hq
  have hh := phase_suffix eps heps (q-20) hs r hr
  simpa only [R_eval, sevenWord, he, Nat.cast_add, Nat.cast_one] using hh

/-- The displayed spacing estimate in the retained seven-action note. -/
theorem seven_spacing_suffix (q : ℕ) (hq : 20 ≤ q) (r : ℕ)
    (hr : r ≤ (sevenWord q).length) :
    height (0 : Fin 6) (R_seven.mulVec (binomBasis 3 (q+1))) -
      height (0 : Fin 6)
        (wordScore M_seven (R_seven.mulVec (binomBasis 3 q)) ((sevenWord q).take r)) ≤
      1 + ((sevenWord q).length-r : ℕ) / (126 * (q : ℚ)+61) := by
  have he : ((q-20 : ℕ) : ℚ)+20 = (q : ℚ) := by
    rw [Nat.cast_sub hq]
    norm_num
  have hd : 0 < 126 * (q : ℚ)+61 := by positivity
  have hs : 1 ≤ (1/(126*(q : ℚ)+61)) * (126*(((q-20 : ℕ) : ℚ)+20)+61) := by
    rw [he]
    simp [ne_of_gt hd]
  have hh := phase_suffix (1/(126*(q : ℚ)+61)) (by positivity) (q-20) hs r hr
  simpa only [R_eval, sevenWord, he, Nat.cast_add, Nat.cast_one,
    one_div_mul_eq_div, add_comm] using hh

end Karlin.FaithfulSevenSuffix
