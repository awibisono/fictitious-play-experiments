import Karlin.FaithfulClock
import Karlin.FaithfulRate
import Karlin.FaithfulRateError
import Karlin.FaithfulGrowth
import Karlin.FaithfulBiasSetup

/-! Canonical zero-count realization of the same word family in a faithful clock.
The clock input has neither strict trajectories nor gap estimates as fields. -/

namespace Karlin.FaithfulRealization

open scoped BigOperators
open Filter Topology
open FaithfulClock

variable {k : ℕ} (P : Clock k)

def phaseWord (p : ℕ) : List (Fin P.m) := P.word (P.Q + p)

def gridDenominator : ℕ := FaithfulBiasSetup.gridDenominator P.A (P.entry P.Q)

def bias (i : Fin P.m) : ℚ :=
  tieRemovalBias (P.m : ℚ) (gridDenominator P : ℚ) ((P.rank i).val : ℚ)

def biasedEntry (p : ℕ) (i : Fin P.m) : ℚ := P.entry (P.Q + p) i + bias P i

theorem phase_length_pos (p : ℕ) : 0 < (phaseWord P p).length :=
  P.word_length_pos _ (by omega)

theorem biased_family :
    (∀ p, IsValidStrictWord P.A (biasedEntry P p) (phaseWord P p)) ∧
    (∀ p, wordScore P.A (biasedEntry P p) (phaseWord P p) = biasedEntry P (p + 1)) := by
  have hp : ∀ p, IsValidPriorityWord P.A (P.entry (P.Q + p)) P.rank (phaseWord P p) :=
    fun p => P.valid _ (by omega)
  have hn : ∀ p, wordScore P.A (P.entry (P.Q + p)) (phaseWord P p) = P.entry (P.Q + (p + 1)) := by
    intro p
    simpa [phaseWord, Nat.add_assoc] using P.phase_transition (P.Q + p) (by omega)
  have hm : 0 < P.m := P.b.pos
  simpa [biasedEntry, bias, gridDenominator] using
    priority_phase_family_bias_strict P.A (fun p => P.entry (P.Q + p))
      P.rank (phaseWord P) hm
      (FaithfulBiasSetup.gridDenominator P.A (P.entry P.Q) : ℚ)
      (by exact_mod_cast FaithfulBiasSetup.gridDenominator_pos P.A (P.entry P.Q))
      (FaithfulBiasSetup.grid_matrix P.A (P.entry P.Q))
      (FaithfulBiasSetup.grid_vector P.A (P.entry P.Q)) hn hp

def shift : ℚ := FaithfulBiasSetup.shift P.b (biasedEntry P 0)

def setupVector (i : Fin P.m) : ℚ := biasedEntry P 0 i + shift P

theorem setupVector_ge_one (i : Fin P.m) : 1 ≤ setupVector P i :=
  FaithfulBiasSetup.one_le_shift P.b (biasedEntry P 0) i

def game : Matrix (Option (Fin P.m)) (Option (Fin P.m)) ℚ := setupMatrix P.A (setupVector P)

def play : ℕ → Option (Fin P.m) := wordPhaseTrajectory (phaseWord P) P.b

def phaseTime : ℕ → ℕ := wordPhaseStartStep (phaseWord P)

theorem initial_action : play P 0 = none := rfl

theorem zero_initial_scores (i : Option (Fin P.m)) :
    cumScore (game P) (play P) 0 i = 0 := by simp [cumScore]

theorem setup_not_replayed {t : ℕ} (ht : 1 ≤ t) : play P t ≠ none := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
  let len := setupFullLen (flatLen (fun p => (phaseWord P p).length) (fun _ _ => 1))
  have hl : ∀ r, 0 < len r := by
    intro r
    simp [len, setupFullLen_flatLen_one]
  have he : 1 + u = runStart len (u + 1) + 0 := by
    rw [runStart_setupFullLen_flatLen_one]
    omega
  unfold play wordPhaseTrajectory
  rw [he, unrollAction_at_offset _ hl (u + 1) 0 (hl _)]
  simp [setupFullAct]

theorem game_skew : IsSkewSymmetric (game P) := setupMatrix_skewSymmetric P.skew _

theorem play_strict : IsStrictFPTrajectory (game P) (play P) := by
  apply word_phase_unroll_isStrictFPTrajectory P.A (setupVector P) (shift P)
    (biasedEntry P) (phaseWord P) P.b (phase_length_pos P)
  · intro i
    exact le_trans (by norm_num) (setupVector_ge_one P i)
  · intro i
    rfl
  · exact (biased_family P).2
  · exact (biased_family P).1
  · intro p v hv
    have hge := wordScore_active_ge_phase_zero P.A P.skew (biasedEntry P) (phaseWord P)
      (phase_length_pos P) (biased_family P).2 (biased_family P).1 p v hv
    have h1 := setupVector_ge_one P ((phaseWord P 0)[0]'(phase_length_pos P 0))
    unfold setupVector at h1
    linarith

theorem simultaneous_strict : IsStrictTwoPlayerFPTrajectory (game P) (play P) (play P) :=
  (isStrictTwoPlayerFPTrajectory_iff_isStrictFPTrajectory (game_skew P) _).2 (play_strict P)

theorem unique_from_common_initial (row col : ℕ → Option (Fin P.m))
    (hw : IsWeakTwoPlayerFPTrajectory (game P) row col)
    (hr : row 0 = play P 0) (hc : col 0 = play P 0) (t : ℕ) :
    row t = play P t ∧ col t = play P t :=
  unique_two_player_fp_trajectory (game_skew P) (play_strict P) hw hr hc t

theorem unique_from_setup (row col : ℕ → Option (Fin P.m))
    (hw : IsWeakTwoPlayerFPTrajectory (game P) row col)
    (hr : row 0 = none) (hc : col 0 = none) (t : ℕ) :
    row t = play P t ∧ col t = play P t := by
  apply unique_from_common_initial P row col hw
  · simpa [initial_action] using hr
  · simpa [initial_action] using hc

theorem action_count : Fintype.card (Option (Fin P.m)) = P.m + 1 := by simp

theorem phaseTime_strictMono : StrictMono (phaseTime P) := by
  apply strictMono_nat_of_lt_succ
  exact wordPhaseStartStep_strictMono (phaseWord P) (phase_length_pos P)

theorem phaseTime_zero : phaseTime P 0 = 1 := rfl

theorem phase_first (p : ℕ) :
    (phaseWord P p)[0]'(phase_length_pos P p) = P.b := by
  obtain ⟨tail, ht⟩ := P.begins_twice (P.Q + p) (by omega)
  simp [phaseWord, ht]

theorem phaseTime_action (p : ℕ) : play P (phaseTime P p) = some P.b := by
  rw [play, phaseTime, wordPhaseTrajectory_at_phase_start (phaseWord P) P.b (phase_length_pos P)]
  simpa [wordPhaseAct, phase_length_pos] using congrArg some (phase_first P p)

theorem phaseTime_score (p : ℕ) (i : Fin P.m) :
    cumScore (game P) (play P) (phaseTime P p) (some i) = biasedEntry P p i + shift P := by
  exact wordPhaseTrajectory_cumScore_at_phase_start P.A (setupVector P) (shift P)
    (biasedEntry P) (phaseWord P) P.b (phase_length_pos P) (fun _ => rfl)
    (biased_family P).2 p i

theorem phaseTime_height (p : ℕ) :
    cumScore (game P) (play P) (phaseTime P p) (play P (phaseTime P p)) =
      P.entry (P.Q + p) P.b + bias P P.b + shift P := by
  rw [phaseTime_action, phaseTime_score]
  rfl

def extendRow (c : Fin k → ℚ) (j : ℕ) : ℝ := if hj : j < k then c ⟨j, hj⟩ else 0

theorem row_sum_eq_range (c : Fin k → ℚ) (q : ℕ) :
    (∑ j : Fin k, (c j : ℝ) * (Nat.choose q j.val : ℝ)) =
      ∑ j ∈ Finset.range k, extendRow c j * (Nat.choose q j : ℝ) := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [extendRow, Finset.mem_range.mp hj]

def countCoeff : ℕ → ℝ := extendRow (fun j => ∑ i : Fin P.m, P.countTable i j)

def scoreCoeff : ℕ → ℝ := extendRow (P.R P.b)

theorem word_length_table (q : ℕ) (hq : P.Q ≤ q) :
    ((P.word q).length : ℝ) =
      ∑ j ∈ Finset.range k, countCoeff P j * (Nat.choose q j : ℝ) := by
  have hqrat : ((P.word q).length : ℚ) =
      ∑ j : Fin k, (∑ i : Fin P.m, P.countTable i j) * (Nat.choose q j.val : ℚ) := by
    rw [list_length_eq_sum_wordCountVec, P.counts q hq]
    simp only [Matrix.mulVec, dotProduct, binomBasis]
    rw [Finset.sum_comm]
    simp [FaithfulClock.Clock.countTable, ratCount, Finset.sum_mul]
  have hr : ((P.word q).length : ℝ) =
      ∑ j : Fin k, ((∑ i : Fin P.m, P.countTable i j : ℚ) : ℝ) * (Nat.choose q j.val : ℝ) := by
    exact_mod_cast hqrat
  rw [hr, row_sum_eq_range]
  rfl

theorem phaseTime_table (q : ℕ) : (phaseTime P q : ℝ) =
    1 + ∑ sigma ∈ Finset.Ico P.Q (q + P.Q),
      ∑ j ∈ Finset.range k, countCoeff P j * (Nat.choose sigma j : ℝ) := by
  simp only [phaseTime, wordPhaseStartStep, runStart, Nat.cast_add, Nat.cast_sum,
    Nat.cast_one, phaseWord]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact word_length_table P (P.Q + p) (by omega)

theorem phaseHeight_table (q : ℕ) :
    (cumScore (game P) (play P) (phaseTime P q) (play P (phaseTime P q)) : ℝ) =
      (∑ j ∈ Finset.range k, scoreCoeff P j * (Nat.choose (q + P.Q) j : ℝ)) +
        ((bias P P.b + shift P : ℚ) : ℝ) := by
  rw [phaseTime_height]
  simp only [FaithfulClock.Clock.entry, Matrix.mulVec, dotProduct, binomBasis]
  push_cast
  rw [row_sum_eq_range]
  simp only [scoreCoeff, Nat.add_comm]
  ring

noncomputable def gapConstant : ℝ :=
  FaithfulRate.paperGapConstant k (countCoeff P (k - 1)) (scoreCoeff P (k - 1))

/-- Exact all-integer asymptotics for the canonical realization of this very clock.
All table and trajectory hypotheses of the analytic bridge are discharged here. -/
theorem exact_gap_limit : 0 < gapConstant P ∧
    Tendsto (fun t : ℕ => (standardDualityGap (game P) (play P) (play P) t : ℝ) *
      (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 (gapConstant P)) := by
  have hk : k - 1 < k := by have := P.order_ge_two; omega
  have hL : 0 < countCoeff P (k - 1) := by
    simp only [countCoeff, extendRow, dif_pos hk]
    exact_mod_cast FaithfulGrowth.Clock.leading_total_count_pos P
  have hxi : 0 < scoreCoeff P (k - 1) := by
    simp only [scoreCoeff, extendRow, dif_pos hk]
    exact_mod_cast P.leading_height
  exact FaithfulRateError.standard_gap_from_phase_tables_exact_limit (game_skew P) (play_strict P)
    (phaseTime_strictMono P) P.order_ge_two P.Q (countCoeff P) (scoreCoeff P)
    ((bias P P.b + shift P : ℚ) : ℝ) hL hxi (phaseTime_table P) (phaseHeight_table P)

theorem relative_gap_limit :
    Tendsto (fun t : ℕ => (standardDualityGap (game P) (play P) (play P) t : ℝ) /
      (gapConstant P * (t : ℝ) ^ (-(1 / (k : ℝ))))) atTop (𝓝 1) :=
  FaithfulRate.relative_gap_limit_of_normalized_limit (exact_gap_limit P).1 (exact_gap_limit P).2

/-- The stronger v15 relative remainder, at every sufficiently large integer time. -/
theorem relative_gap_error :
    (fun t : ℕ => (standardDualityGap (game P) (play P) (play P) t : ℝ) /
      (gapConstant P * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  have hk : k - 1 < k := by have := P.order_ge_two; omega
  have hL : 0 < countCoeff P (k - 1) := by
    simp only [countCoeff, extendRow, dif_pos hk]
    exact_mod_cast FaithfulGrowth.Clock.leading_total_count_pos P
  have hxi : 0 < scoreCoeff P (k - 1) := by
    simp only [scoreCoeff, extendRow, dif_pos hk]
    exact_mod_cast P.leading_height
  exact FaithfulRateError.standard_gap_from_phase_tables_relative_error
    (game_skew P) (play_strict P) (phaseTime_strictMono P) P.order_ge_two P.Q
    (countCoeff P) (scoreCoeff P) ((bias P P.b + shift P : ℚ) : ℝ)
    hL hxi (phaseTime_table P) (phaseHeight_table P)

/-- Explicit two-sided constant bounds for the standard gap at every integer
beyond one onset. Constants depend only on this fixed clock. -/
theorem all_integer_theta : ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
    (gapConstant P / 2) * (t : ℝ) ^ (-(1 / (k : ℝ))) ≤
      (standardDualityGap (game P) (play P) (play P) t : ℝ) ∧
    (standardDualityGap (game P) (play P) (play P) t : ℝ) ≤
      (2 * gapConstant P) * (t : ℝ) ^ (-(1 / (k : ℝ))) := by
  have he := (relative_gap_limit P).eventually
    (Ioo_mem_nhds (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hp : 0 < (t : ℝ) ^ (-(1 / (k : ℝ))) := Real.rpow_pos_of_pos htpos _
  have hd : 0 < gapConstant P * (t : ℝ) ^ (-(1 / (k : ℝ))) :=
    mul_pos (exact_gap_limit P).1 hp
  obtain ⟨hlo, hhi⟩ := hN t ((le_max_left _ _).trans ht)
  have hlo' := (lt_div_iff₀ hd).mp hlo
  have hhi' := (div_lt_iff₀ hd).mp hhi
  constructor <;> nlinarith

theorem standard_gap_normalization {t : ℕ} (ht : 1 ≤ t) :
    standardDualityGap (game P) (play P) (play P) t =
      2 * cumScore (game P) (play P) t (play P t) / (t : ℚ) :=
  standardDualityGap_eq_stepDualityGap (game_skew P) (play_strict P) ht

end Karlin.FaithfulRealization
