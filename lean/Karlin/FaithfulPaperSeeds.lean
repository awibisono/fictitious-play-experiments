import Karlin.FaithfulSeedAdmissible
import Karlin.FaithfulParameters

/-!
# Literal seed calculations in v15, pages 27–29 and 42–43

These are additional calculations on the existing RPS clock and its actual
admissible data. No matrix, word, scale, or threshold used by the construction
is replaced. `rpsBundleThreshold` is the smaller sufficient bound displayed in
the manuscript; the general construction may continue to use its own bound.
-/

namespace Karlin.FaithfulPaperSeeds

open scoped BigOperators
open FaithfulClock FaithfulSeed FaithfulSeedAdmissible FaithfulWindow

theorem rps_count_minor_det :
    Matrix.det (C2.submatrix (fun i : Fin 2 => i.castLE (by decide)) id) = -3 := by
  decide +kernel

theorem rps_count_positive (q : ℕ) (i : Fin 3) :
    0 < C2.mulVec (binomBasis 2 q) i := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, C2, binomBasis] <;> positivity

theorem rps_first_run_at_least_eight (q : ℕ) (hq : 1 ≤ q) : 8 ≤ 3 * q + 5 := by
  omega

/-- The rising competitor is exactly `2/3` behind at the final proper integer
offset, then exactly `1/3` ahead at the handoff, in each of the three runs. -/
theorem rps_integer_handoffs (q : ℚ) :
    (scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 (3 * q + 4)) 0 -
      scoreVec A_RPS (r2Vec q) (runCount (fun _ => 0) 0 (3 * q + 4)) 1 = 2 / 3) ∧
    (rpsStateAfterRun0 q 1 - rpsStateAfterRun0 q 0 = 1 / 3) ∧
    (scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 (3 * q + 5)) 1 -
      scoreVec A_RPS (rpsStateAfterRun0 q) (runCount (fun _ => 0) 1 (3 * q + 5)) 2 = 2 / 3) ∧
    (rpsStateAfterRun1 q 2 - rpsStateAfterRun1 q 1 = 1 / 3) ∧
    (scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 (3 * q + 6)) 2 -
      scoreVec A_RPS (rpsStateAfterRun1 q) (runCount (fun _ => 0) 2 (3 * q + 6)) 0 = 2 / 3) ∧
    (r2Vec (q + 1) 0 - r2Vec (q + 1) 2 = 1 / 3) := by
  simp only [scoreVec_runCount]
  simp only [show A_RPS 0 0 = 0 from rfl, show A_RPS 1 0 = 1 from rfl,
    show A_RPS 1 1 = 0 from rfl, show A_RPS 2 1 = 1 from rfl,
    show A_RPS 2 2 = 0 from rfl, show A_RPS 0 2 = 1 from rfl,
    scoreVec, mul_zero, Finset.sum_const_zero, add_zero]
  repeat' constructor
  all_goals (simp [r2Vec, rpsStateAfterRun0, rpsStateAfterRun1]; ring)

theorem rps_support_gaps (q : ℚ) :
    ((r2Vec q 0 + A_RPS 0 0 - v_RPS 0) -
      (r2Vec q 1 + A_RPS 1 0 - v_RPS 1) = 3 * q + 8 / 3) ∧
    ((r2Vec q 0 + A_RPS 0 0 - v_RPS 0) -
      (r2Vec q 2 + A_RPS 2 0 - v_RPS 2) = 7 / 3) := by
  constructor <;> simp [r2Vec, A_RPS, v_RPS] <;> ring

private theorem rps_counter_prefix_formula (q r : ℕ) :
    dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).take r)) =
      (min (r - ((3 * q + 5) + (3 * q + 6))) (3 * q + 7) : ℕ) -
        (min (r - (3 * q + 5)) (3 * q + 6) : ℕ) := by
  have htake : (rpsPhaseWord q).take r =
      (List.replicate (3 * q + 5) 0).take r ++
      (List.replicate (3 * q + 6) 1).take (r - (3 * q + 5)) ++
      (List.replicate (3 * q + 7) 2).take (r - ((3 * q + 5) + (3 * q + 6))) := by
    simp only [rpsPhaseWord, List.take_append, List.length_append, List.length_replicate]
  rw [htake]
  simp [dotProduct, Fin.sum_univ_three, v_RPS, wordCountVec,
    List.count_append, List.take_replicate, List.count_replicate]
  ring

private theorem rps_counter_split (q r : ℕ) :
    dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).take r)) +
      dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).drop r)) = 1 := by
  rw [dotCount_take_add_drop]
  rw [wordCountVec_rpsPhaseWord]
  exact clock_endpoint_increment_eq_one (by decide) v_RPS C2 rpsAlgebraicClock.hvC q

/-- The three remaining-counter formulas, with the paper's `σ=q+1`. -/
theorem rps_remaining_run0 (q h : ℕ) (hh : h ≤ 3 * q + 5) :
    dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).drop h)) = 1 := by
  have hp := rps_counter_prefix_formula q h
  have hs := rps_counter_split q h
  have hz : h - (3 * q + 5) = 0 := by omega
  have hz' : h - ((3 * q + 5) + (3 * q + 6)) = 0 := by omega
  simp only [hz, hz', zero_min, Nat.cast_zero, sub_self] at hp
  linarith

theorem rps_remaining_run1 (q h : ℕ) (hh : h ≤ 3 * q + 6) :
    dotProduct v_RPS (wordCountVec ((rpsPhaseWord q).drop (3 * q + 5 + h))) =
      1 + (h : ℚ) := by
  have hp := rps_counter_prefix_formula q (3 * q + 5 + h)
  have hs := rps_counter_split q (3 * q + 5 + h)
  have hz : 3 * q + 5 + h - ((3 * q + 5) + (3 * q + 6)) = 0 := by omega
  simp only [hz, zero_min, Nat.cast_zero, Nat.add_sub_cancel_left,
    min_eq_left hh, zero_sub] at hp
  linarith

theorem rps_remaining_run2 (q h : ℕ) (hh : h ≤ 3 * q + 7) :
    dotProduct v_RPS (wordCountVec
      ((rpsPhaseWord q).drop ((3 * q + 5) + (3 * q + 6) + h))) =
      3 * (q : ℚ) + 7 - h := by
  have hp := rps_counter_prefix_formula q ((3 * q + 5) + (3 * q + 6) + h)
  have hs := rps_counter_split q ((3 * q + 5) + (3 * q + 6) + h)
  have hz : ((3 * q + 5) + (3 * q + 6) + h) - (3 * q + 5) = 3 * q + 6 + h := by omega
  have hl : 3 * q + 6 ≤ 3 * q + 6 + h := by omega
  simp only [Nat.add_sub_cancel_left, min_eq_left hh, hz, min_eq_right hl] at hp
  push_cast at hp
  linarith

/-- A common positive preload changes no RPS payoff scores. -/
theorem rps_positive_preload (q c : ℚ) (hq : 0 ≤ q) (hc : 0 < c) :
    let z : Fin 3 → ℚ := ![c, q + 4 / 3 + c, 2 * q + 3 + c]
    (∀ i, 0 < z i) ∧ A_RPS.mulVec z = fun i => r2Vec q i + 2 / 3 := by
  dsimp only
  constructor
  · intro i
    fin_cases i <;> simp <;> linarith
  · ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, A_RPS, r2Vec] <;> ring

/-- The precise sufficient bundle threshold from page 28. -/
def rpsBundleThreshold (eps : ℚ) : ℕ := max 1 ⌈1 / (9 * eps)⌉₊

theorem rps_whole_phase_gain (eps : ℚ) (heps : 0 < eps) (q : ℕ)
    (hq : rpsBundleThreshold eps ≤ q) :
    height (0 : Fin 3) (R2.mulVec (binomBasis 2 (q + 1))) -
      height (0 : Fin 3) (R2.mulVec (binomBasis 2 q)) ≤ eps * (rpsPhaseWord q).length := by
  have hceil : ⌈1 / (9 * eps)⌉₊ ≤ q := (le_max_right _ _).trans hq
  have hdiv : 1 / (9 * eps) ≤ (q : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hmul := (div_le_iff₀ (show 0 < 9 * eps by positivity)).mp hdiv
  rw [rps_height, rps_height]
  have hlen : ((rpsPhaseWord q).length : ℚ) = 9 * (q : ℚ) + 18 := by
    simp [rpsPhaseWord]
    ring
  rw [hlen]
  push_cast
  nlinarith

/-- Every prefix of every consecutive bundle, using the displayed smaller
threshold and charging the additive constant only once. -/
theorem rps_bundle_suffix (eps : ℚ) (heps : 0 < eps) (a n r : ℕ)
    (ha : rpsBundleThreshold eps ≤ a)
    (hr : r ≤ (consecutiveWord rpsPhaseWord a n).length) :
    height (0 : Fin 3) (R2.mulVec (binomBasis 2 (a + n))) -
      height (0 : Fin 3) (wordScore A_RPS (R2.mulVec (binomBasis 2 a))
        ((consecutiveWord rpsPhaseWord a n).take r)) ≤
      eps * ((consecutiveWord rpsPhaseWord a n).length - r : ℕ) + 1 := by
  apply consecutiveWord_suffix A_RPS rpsPhaseWord (fun q => R2.mulVec (binomBasis 2 q))
    (height (0 : Fin 3)) (rpsBundleThreshold eps) eps 1 (by norm_num)
    (fun q _ => rps_word_transition q)
    (fun q _ r hr => rps_suffix eps heps q r hr)
    (fun q hq => rps_whole_phase_gain eps heps q hq) a ha n r hr

/-- In a two-action skew game the score difference depends only on elapsed
time, regardless of the chosen action sequence. -/
theorem two_action_difference (a : ℚ) (s : Fin 2 → ℚ) (W : List (Fin 2)) :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![0, -a; a, 0]
    wordScore A s W 1 - wordScore A s W 0 = s 1 - s 0 + a * W.length := by
  have hlen := list_length_eq_sum_wordCountVec W
  simp only [Fin.sum_univ_two] at hlen
  dsimp only
  simp only [wordScore, scoreVec, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hlen]
  ring

/-- Thus nonzero skew payoff gives strictly monotone score difference in time;
in particular a strict winner cannot switch back to its earlier action. -/
theorem two_action_difference_strictMono (a : ℚ) (ha : 0 < a) (s : Fin 2 → ℚ)
    (W : ℕ → List (Fin 2)) (hW : ∀ t, (W t).length = t) :
    StrictMono (fun t => wordScore !![0, -a; a, 0] s (W t) 1 -
      wordScore !![0, -a; a, 0] s (W t) 0) := by
  intro t u htu
  simp only [two_action_difference, hW]
  have htu' : (t : ℚ) < u := by exact_mod_cast htu
  linarith [mul_lt_mul_of_pos_left htu' ha]

theorem two_action_difference_strictAnti (a : ℚ) (ha : a < 0) (s : Fin 2 → ℚ)
    (W : ℕ → List (Fin 2)) (hW : ∀ t, (W t).length = t) :
    StrictAnti (fun t => wordScore !![0, -a; a, 0] s (W t) 1 -
      wordScore !![0, -a; a, 0] s (W t) 0) := by
  intro t u htu
  simp only [two_action_difference, hW]
  have htu' : (t : ℚ) < u := by exact_mod_cast htu
  linarith [mul_lt_mul_of_neg_left htu' ha]

/-- With positive `a`, once action 1 is a maximizing action it is the unique
maximizing action at every later time. This forbids a second switch. -/
theorem two_action_positive_no_return (a : ℚ) (ha : 0 < a) (s : Fin 2 → ℚ)
    (W : ℕ → List (Fin 2)) (hW : ∀ t, (W t).length = t) (b : ℕ → Fin 2)
    (hbest : ∀ t i, wordScore !![0, -a; a, 0] s (W t) i ≤
      wordScore !![0, -a; a, 0] s (W t) (b t))
    (t u : ℕ) (htu : t < u) (ht : b t = 1) : b u = 1 := by
  have hg := two_action_difference_strictMono a ha s W hW htu
  have hb := hbest t 0
  rw [ht] at hb
  by_contra hu
  have hu0 : b u = 0 := by
    have h : ∀ i : Fin 2, i ≠ 1 → i = 0 := by decide
    exact h _ hu
  have hu' := hbest u 1
  rw [hu0] at hu'
  linarith

/-- With negative `a`, the direction of the only possible switch is reversed. -/
theorem two_action_negative_no_return (a : ℚ) (ha : a < 0) (s : Fin 2 → ℚ)
    (W : ℕ → List (Fin 2)) (hW : ∀ t, (W t).length = t) (b : ℕ → Fin 2)
    (hbest : ∀ t i, wordScore !![0, -a; a, 0] s (W t) i ≤
      wordScore !![0, -a; a, 0] s (W t) (b t))
    (t u : ℕ) (htu : t < u) (ht : b t = 0) : b u = 0 := by
  have hg := two_action_difference_strictAnti a ha s W hW htu
  have hb := hbest t 1
  rw [ht] at hb
  by_contra hu
  have hu1 : b u = 1 := by
    have h : ∀ i : Fin 2, i ≠ 0 → i = 1 := by decide
    exact h _ hu
  have hu' := hbest u 0
  rw [hu1] at hu'
  linarith

/-- The strict winner cannot alternate `0,1,0` or `1,0,1` at three ordered
times, for any two-action skew payoff, including the zero matrix. -/
theorem two_action_no_strict_alternation (a : ℚ) (s : Fin 2 → ℚ)
    (W : ℕ → List (Fin 2)) (hW : ∀ t, (W t).length = t)
    (t u v : ℕ) (htu : t < u) (huv : u < v) :
    let d := fun n => wordScore !![0, -a; a, 0] s (W n) 1 -
      wordScore !![0, -a; a, 0] s (W n) 0
    ¬ ((d t < 0 ∧ 0 < d u ∧ d v < 0) ∨ (0 < d t ∧ d u < 0 ∧ 0 < d v)) := by
  dsimp only
  simp only [two_action_difference, hW]
  have htu' : (t : ℚ) ≤ u := by exact_mod_cast htu.le
  have huv' : (u : ℚ) ≤ v := by exact_mod_cast huv.le
  rcases le_total 0 a with ha | ha
  · have ht := mul_le_mul_of_nonneg_left htu' ha
    have hu := mul_le_mul_of_nonneg_left huv' ha
    rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith
  · have ht := mul_le_mul_of_nonpos_left htu' ha
    have hu := mul_le_mul_of_nonpos_left huv' ha
    rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> linarith

theorem two_action_zero_constant (s : Fin 2 → ℚ) (W : List (Fin 2)) :
    wordScore (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) s W = s := by
  ext i
  fin_cases i <;> simp [wordScore, scoreVec, Fin.sum_univ_two]

open FaithfulParameters FaithfulParameters.AdmissibleParameters
open FaithfulGain FaithfulGain.AdmissibleGain

theorem rps_reference_height : rpsAdmissible.referenceHeight = ![4, 3 / 2, 1] :=
  reference_height

theorem rps_least_denominator : lam rpsAdmissible = 2 := by
  unfold lam
  rw [rps_reference_height]
  decide +kernel

theorem rps_least_denominator_minimal (n : ℕ) (hn : 1 ≤ n)
    (hclear : ∀ j, ∃ z : ℤ, (z : ℚ) = (n : ℚ) * rpsAdmissible.referenceHeight j) :
    2 ≤ n := by
  rw [← rps_least_denominator]
  exact lam_minimal rpsAdmissible n hn hclear

theorem rps_baseline_counts : baselineCounts rpsAdmissible (lam rpsAdmissible) =
    ![48, 18, 12] := by
  rw [rps_least_denominator]
  unfold baselineCounts
  rw [rps_reference_height]
  ext j
  fin_cases j <;> norm_num

theorem rps_reference_residual : referenceResidual rpsAdmissible = D0tX_rps := by
  change (FaithfulTables.D rpsClock 1 (1 / 2) (FaithfulAdmissible.baseline rpsClock) 0).transpose *
    FaithfulTables.X rpsClock 1 - outerProd (fun _ => (0 : ℚ)) _ = _
  rw [actual_reference_summary]
  simp [outerProd]
  rfl

theorem rps_old_totals : oldTotals rpsAdmissible = ![1, 27, 27] := by
  unfold oldTotals
  dsimp [rpsAdmissible, FaithfulTables.X, rpsClock, FaithfulClock.Clock.countTable,
    FaithfulClock.ratCount, C2Integer]
  decide +kernel

/-- The selected gain in the existing construction is exactly equation (44). -/
theorem rps_selected_gain (T : ℕ) :
    selectedGain rpsAdmissible (lam rpsAdmissible) T =
      1 / 2 + 27 / (8 * (T : ℚ) + 18) := by
  unfold selectedGain
  rw [rps_baseline_counts, rps_old_totals, rps_reference_residual,
    Z_binom_concrete_3_2_eq_Z2_rps, Z2_rps_inner_D0tX]
  norm_num [gain, gainShift, FaithfulAdmissible.Admissible.correction, rpsAdmissible]
  have ht : 0 ≤ (T : ℚ) := by positivity
  have h1 : 12 * (T : ℚ) + 27 ≠ 0 := by linarith
  have h2 : 8 * (T : ℚ) + 18 ≠ 0 := by linarith
  field_simp
  ring

theorem rps_gain_forms (T : ℚ) (hT : 0 ≤ T) :
    1 / 2 + 27 / (8 * T + 18) = 2 * (T + 9) / (4 * T + 9) := by
  have hden : 4 * T + 9 ≠ 0 := by linarith
  have hden' : 8 * T + 18 ≠ 0 := by linarith
  field_simp
  ring

theorem rps_gain_lt_one_iff (T : ℚ) (hT : 0 ≤ T) :
    1 / 2 + 27 / (8 * T + 18) < 1 ↔ 9 / 2 < T := by
  rw [rps_gain_forms T hT, div_lt_iff₀ (show 0 < 4 * T + 9 by linarith)]
  constructor <;> intro h <;> linarith

/-- The paper's positive reciprocal-scale correction, with an explicit bound. -/
theorem rps_gain_correction_bound (T : ℚ) (hT : 0 < T) :
    0 < 27 / (8 * T + 18) ∧ 27 / (8 * T + 18) ≤ (27 / 8) / T := by
  constructor
  · positivity
  · apply (div_le_div_iff₀ (show 0 < 8 * T + 18 by positivity) hT).2
    nlinarith

/-- The actual selected gain has the paper's strict range and cancels the
displayed lowest-test obstruction for every integer reset scale at least five. -/
theorem rps_selected_gain_cancellation (T : ℕ) (hT : 5 ≤ T) :
    let c := selectedGain rpsAdmissible (lam rpsAdmissible) T
    0 < c ∧ c < 1 ∧ -81 / 2 + (c - 1 / 2) * (27 + 12 * T) = 0 := by
  rw [rps_selected_gain, rps_gain_forms T (by positivity)]
  exact rps_lowest_test_cancellation (by exact_mod_cast hT)

#print axioms rps_count_minor_det
#print axioms rps_integer_handoffs
#print axioms rps_remaining_run0
#print axioms rps_remaining_run1
#print axioms rps_remaining_run2
#print axioms rps_positive_preload
#print axioms rps_bundle_suffix
#print axioms two_action_difference
#print axioms two_action_positive_no_return
#print axioms two_action_negative_no_return
#print axioms two_action_no_strict_alternation
#print axioms rps_least_denominator_minimal
#print axioms rps_selected_gain_cancellation

end Karlin.FaithfulPaperSeeds
