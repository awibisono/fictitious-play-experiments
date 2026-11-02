import Karlin.FaithfulFamily
import Karlin.FaithfulLift
import Karlin.FaithfulGameReindex

/-!
# The unconditional v15 family, through the literal one-copy lift

The only induction seed is the explicit admissible RPS clock. Each successor
uses the constructed moving-window, compatibility/gain, reset, rotation, and
admissibility proofs. The construction follows the one-copy lift directly.
The final setup action is labeled 0, and both players' counts start at zero.
-/
namespace Karlin.FaithfulMain
open Filter Topology
open FaithfulClock FaithfulAdmissible FaithfulFamily FaithfulGameReindex

noncomputable def step (k : ℕ) (B : Bundle k) : Bundle (k + 1) :=
  ⟨FaithfulLift.nextClock B.data, FaithfulLift.nextAdmissible B.data⟩

theorem step_dimension (k : ℕ) (B : Bundle k) :
    (step k B).clock.m = B.clock.m + 2*k + 3 := FaithfulLift.nextClock_m B.data

noncomputable def bundle (k : ℕ) (hk : 2 ≤ k) : Bundle k := atOrder step k hk

noncomputable def clock (k : ℕ) (hk : 2 ≤ k) : Clock k := (bundle k hk).clock

noncomputable def admissible (k : ℕ) (hk : 2 ≤ k) : Admissible (clock k hk) :=
  (bundle k hk).data

theorem dimension (k : ℕ) (hk : 2 ≤ k) : (clock k hk).m + 1 = (k+1)^2 - 5 :=
  atOrder_dimension step step_dimension k hk

noncomputable def matrix (k : ℕ) (hk : 2 ≤ k) :
    Matrix (Fin ((clock k hk).m + 1)) (Fin ((clock k hk).m + 1)) ℚ :=
  finGame (FaithfulRealization.game (clock k hk))

noncomputable def trajectory (k : ℕ) (hk : 2 ≤ k) : ℕ → Fin ((clock k hk).m + 1) :=
  finPlay (FaithfulRealization.play (clock k hk))

noncomputable def constant (k : ℕ) (hk : 2 ≤ k) : ℝ :=
  FaithfulRealization.gapConstant (clock k hk)

/-- The prefactor from the leading binomial count and height coefficients. -/
theorem constant_formula (k : ℕ) (hk : 2 ≤ k) :
    constant k hk =
      2 * (FaithfulRealization.scoreCoeff (clock k hk) (k-1) /
        ((k-1).factorial : ℝ)) *
      (FaithfulRealization.countCoeff (clock k hk) (k-1) / (k.factorial : ℝ)) ^
        (-((k-1 : ℕ) : ℝ) / (k : ℝ)) := rfl

theorem skew (k : ℕ) (hk : 2 ≤ k) : IsSkewSymmetric (matrix k hk) :=
  finGame_skew (FaithfulRealization.game_skew (clock k hk))

theorem common_initial_action (k : ℕ) (hk : 2 ≤ k) : trajectory k hk 0 = 0 :=
  finPlay_initial _ (FaithfulRealization.initial_action (clock k hk))

def counts {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℕ :=
  ((Finset.range t).filter (fun s => a s = i)).card

theorem empiricalStrategy_eq_counts {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) :
    empiricalStrategy a t i = (counts a t i : ℚ) / (t : ℚ) := by
  simp [empiricalStrategy, counts, Finset.sum_boole]

theorem zero_initial_counts (k : ℕ) (hk : 2 ≤ k) (i : Fin ((clock k hk).m + 1)) :
    counts (trajectory k hk) 0 i = 0 := by simp [counts]

theorem zero_initial_scores (k : ℕ) (hk : 2 ≤ k) (i : Fin ((clock k hk).m + 1)) :
    cumScore (matrix k hk) (trajectory k hk) 0 i = 0 := by simp [cumScore]

theorem strict (k : ℕ) (hk : 2 ≤ k) :
    IsStrictFPTrajectory (matrix k hk) (trajectory k hk) :=
  (finGame_strict_iff _ _).mpr (FaithfulRealization.play_strict (clock k hk))

theorem strict_simultaneous (k : ℕ) (hk : 2 ≤ k) :
    IsStrictTwoPlayerFPTrajectory (matrix k hk) (trajectory k hk) (trajectory k hk) :=
  (finGame_strictTwoPlayer_iff _ _ _).mpr
    (FaithfulRealization.simultaneous_strict (clock k hk))

theorem unique_from_common_setup (k : ℕ) (hk : 2 ≤ k)
    (row col : ℕ → Fin ((clock k hk).m + 1))
    (hw : IsWeakTwoPlayerFPTrajectory (matrix k hk) row col)
    (hr : row 0 = 0) (hc : col 0 = 0) (t : ℕ) :
    row t = trajectory k hk t ∧ col t = trajectory k hk t := by
  apply unique_two_player_fp_trajectory (skew k hk) (strict k hk) hw
  · exact hr.trans (common_initial_action k hk).symm
  · exact hc.trans (common_initial_action k hk).symm

theorem standard_gap_normalization (k : ℕ) (hk : 2 ≤ k) {t : ℕ} (ht : 1 ≤ t) :
    standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t =
      2 * cumScore (matrix k hk) (trajectory k hk) t (trajectory k hk t) / (t : ℚ) :=
  standardDualityGap_eq_stepDualityGap (skew k hk) (strict k hk) ht

theorem exact_gap (k : ℕ) (hk : 2 ≤ k) : 0 < constant k hk ∧
    Tendsto (fun t : ℕ =>
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) *
        (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 (constant k hk)) := by
  simpa only [matrix, trajectory, finGame_gap] using
    FaithfulRealization.exact_gap_limit (clock k hk)

theorem relative_error (k : ℕ) (hk : 2 ≤ k) :
    (fun t : ℕ =>
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) /
        (constant k hk * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  simpa only [matrix, trajectory, finGame_gap] using
    FaithfulRealization.relative_gap_error (clock k hk)

theorem all_integer_theta (k : ℕ) (hk : 2 ≤ k) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      (constant k hk / 2) * (t : ℝ) ^ (-(1 / (k : ℝ))) ≤
        (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) ∧
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) ≤
        (2 * constant k hk) * (t : ℝ) ^ (-(1 / (k : ℝ))) := by
  simpa only [matrix, trajectory, finGame_gap] using
    FaithfulRealization.all_integer_theta (clock k hk)

/-- v15 Theorem 1.1, together with the exact all-integer asymptotic and its
relative error estimate. There are no Clock, compatibility, parameter,
trajectory, phase-endpoint, or asymptotic premises. The positive action count
is written m+1 to make nonempty extrema explicit in the type. -/
theorem main_theorem (k : ℕ) (hk : 2 ≤ k) :
    ∃ (m : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
      (a : ℕ → Fin (m+1)) (c : ℝ),
      m+1 = (k+1)^2-5 ∧ IsSkewSymmetric M ∧ a 0 = 0 ∧
      (∀ i, counts a 0 i = 0) ∧
      IsStrictTwoPlayerFPTrajectory M a a ∧
      (∀ row col, IsWeakTwoPlayerFPTrajectory M row col → row 0 = 0 → col 0 = 0 →
        ∀ t, row t = a t ∧ col t = a t) ∧
      0 < c ∧
      Tendsto (fun t : ℕ => (standardDualityGap M a a t : ℝ) *
        (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 c) ∧
      ((fun t : ℕ => (standardDualityGap M a a t : ℝ) /
        (c * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
        =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ))))) ∧
      ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
        (c/2) * (t : ℝ) ^ (-(1 / (k : ℝ))) ≤ (standardDualityGap M a a t : ℝ) ∧
        (standardDualityGap M a a t : ℝ) ≤ (2*c) * (t : ℝ) ^ (-(1 / (k : ℝ))) := by
  refine ⟨(clock k hk).m, matrix k hk, trajectory k hk, constant k hk,
    dimension k hk, skew k hk, common_initial_action k hk, zero_initial_counts k hk,
    strict_simultaneous k hk, unique_from_common_setup k hk, (exact_gap k hk).1,
    (exact_gap k hk).2, relative_error k hk, all_integer_theta k hk⟩

#print axioms main_theorem
#print axioms exact_gap
#print axioms relative_error
#print axioms admissible
end Karlin.FaithfulMain
