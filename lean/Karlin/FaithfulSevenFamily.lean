import Karlin.FaithfulSevenAdmissible
import Karlin.FaithfulEffectiveLift

/-!
# The unconditional smaller family from the exact cubic seed

The six recurrent actions of the seven-action note seed order three. Every
successor is the identical FaithfulMain.step used for the v15 RPS family.
The final initializer is action zero, so the total dimension is (k+1)^2-9.
The ordinary definitions below compile using the proved effective lift bridges.
-/
namespace Karlin.FaithfulSevenFamily
open Filter Topology
open FaithfulClock FaithfulAdmissible FaithfulFamily FaithfulGameReindex

def seed : Bundle 3 := ⟨FaithfulSevenSeed.sevenClock, FaithfulSevenAdmissible.sevenAdmissible⟩

/-- A structurally recursive executable family, with the same one-step lift. -/
def iterate : (n : ℕ) → Bundle (n+3)
  | 0 => seed
  | n+1 => FaithfulMain.step (n+3) (iterate n)

theorem iterate_dimension : ∀ n : ℕ, (iterate n).clock.m + 10 = (n+4)^2 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (FaithfulMain.step (n+3) (iterate n)).clock.m + 10 = (n+1+4)^2
    rw [FaithfulMain.step_dimension]
    nlinarith

def bundle (k : ℕ) (hk : 3 ≤ k) : Bundle k :=
  (show k - 3 + 3 = k by omega) ▸ iterate (k-3)

def clock (k : ℕ) (hk : 3 ≤ k) : Clock k := (bundle k hk).clock

def admissible (k : ℕ) (hk : 3 ≤ k) : Admissible (clock k hk) := (bundle k hk).data

theorem dimension (k : ℕ) (hk : 3 ≤ k) : (clock k hk).m + 1 = (k+1)^2 - 9 := by
  have h := iterate_dimension (k-3)
  have he : k - 3 + 3 = k := by omega
  have hn : k - 3 + 4 = k + 1 := by omega
  rw [hn] at h
  change ((he ▸ iterate (k-3)).clock.m) + 1 = _
  rw [transport_dimension]
  omega

@[simp] theorem seed_clock : clock 3 (by decide) = FaithfulSevenSeed.sevenClock := rfl

/-- An executable threshold for the inherited every-prefix suffix bound. -/
def threshold (k : ℕ) (hk : 3 ≤ k) (eps : ℚ) : ℕ := (clock k hk).threshold eps

def word (k : ℕ) (hk : 3 ≤ k) (q : ℕ) : List (Fin (clock k hk).m) := (clock k hk).word q

theorem suffix (k : ℕ) (hk : 3 ≤ k) (eps : ℚ) (heps : 0 < eps)
    (q : ℕ) (hq : threshold k hk eps ≤ q)
    (r : ℕ) (hr : r ≤ (word k hk q).length) :
    let P := clock k hk
    height P.b (P.entry (q+1)) -
      height P.b (wordScore P.A (P.entry q) ((word k hk q).take r)) ≤
        eps * ((word k hk q).length-r : ℕ) + P.Arem :=
  (clock k hk).suffix eps heps q hq r hr

def matrix (k : ℕ) (hk : 3 ≤ k) :
    Matrix (Fin ((clock k hk).m + 1)) (Fin ((clock k hk).m + 1)) ℚ :=
  finGame (FaithfulRealization.game (clock k hk))

def trajectory (k : ℕ) (hk : 3 ≤ k) : ℕ → Fin ((clock k hk).m + 1) :=
  finPlay (FaithfulRealization.play (clock k hk))

noncomputable def constant (k : ℕ) (hk : 3 ≤ k) : ℝ :=
  FaithfulRealization.gapConstant (clock k hk)

/-- The prefactor from the leading binomial count and height coefficients. -/
theorem constant_formula (k : ℕ) (hk : 3 ≤ k) :
    constant k hk =
      2 * (FaithfulRealization.scoreCoeff (clock k hk) (k-1) /
        ((k-1).factorial : ℝ)) *
      (FaithfulRealization.countCoeff (clock k hk) (k-1) / (k.factorial : ℝ)) ^
        (-((k-1 : ℕ) : ℝ) / (k : ℝ)) := rfl

theorem skew (k : ℕ) (hk : 3 ≤ k) : IsSkewSymmetric (matrix k hk) :=
  finGame_skew (FaithfulRealization.game_skew (clock k hk))

theorem common_initial_action (k : ℕ) (hk : 3 ≤ k) : trajectory k hk 0 = 0 :=
  finPlay_initial _ (FaithfulRealization.initial_action (clock k hk))

def counts {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℕ :=
  ((Finset.range t).filter (fun s => a s = i)).card

theorem empiricalStrategy_eq_counts {n : ℕ} (a : ℕ → Fin n) (t : ℕ) (i : Fin n) :
    empiricalStrategy a t i = (counts a t i : ℚ) / (t : ℚ) := by
  simp [empiricalStrategy, counts, Finset.sum_boole]

theorem zero_initial_counts (k : ℕ) (hk : 3 ≤ k) (i : Fin ((clock k hk).m + 1)) :
    counts (trajectory k hk) 0 i = 0 := by simp [counts]

theorem zero_initial_scores (k : ℕ) (hk : 3 ≤ k) (i : Fin ((clock k hk).m + 1)) :
    cumScore (matrix k hk) (trajectory k hk) 0 i = 0 := by simp [cumScore]

theorem strict (k : ℕ) (hk : 3 ≤ k) :
    IsStrictFPTrajectory (matrix k hk) (trajectory k hk) :=
  (finGame_strict_iff _ _).mpr (FaithfulRealization.play_strict (clock k hk))

theorem strict_simultaneous (k : ℕ) (hk : 3 ≤ k) :
    IsStrictTwoPlayerFPTrajectory (matrix k hk) (trajectory k hk) (trajectory k hk) :=
  (finGame_strictTwoPlayer_iff _ _ _).mpr
    (FaithfulRealization.simultaneous_strict (clock k hk))

theorem unique_from_common_setup (k : ℕ) (hk : 3 ≤ k)
    (row col : ℕ → Fin ((clock k hk).m + 1))
    (hw : IsWeakTwoPlayerFPTrajectory (matrix k hk) row col)
    (hr : row 0 = 0) (hc : col 0 = 0) (t : ℕ) :
    row t = trajectory k hk t ∧ col t = trajectory k hk t := by
  apply unique_two_player_fp_trajectory (skew k hk) (strict k hk) hw
  · exact hr.trans (common_initial_action k hk).symm
  · exact hc.trans (common_initial_action k hk).symm

theorem standard_gap_normalization (k : ℕ) (hk : 3 ≤ k) {t : ℕ} (ht : 1 ≤ t) :
    standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t =
      2 * cumScore (matrix k hk) (trajectory k hk) t (trajectory k hk t) / (t : ℚ) :=
  standardDualityGap_eq_stepDualityGap (skew k hk) (strict k hk) ht

theorem exact_gap (k : ℕ) (hk : 3 ≤ k) : 0 < constant k hk ∧
    Tendsto (fun t : ℕ =>
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) *
        (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 (constant k hk)) := by
  simpa only [matrix, trajectory, finGame_gap] using
    FaithfulRealization.exact_gap_limit (clock k hk)

theorem relative_error (k : ℕ) (hk : 3 ≤ k) :
    (fun t : ℕ =>
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) /
        (constant k hk * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) := by
  simpa only [matrix, trajectory, finGame_gap] using
    FaithfulRealization.relative_gap_error (clock k hk)

theorem all_integer_theta (k : ℕ) (hk : 3 ≤ k) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      (constant k hk / 2) * (t : ℝ) ^ (-(1 / (k : ℝ))) ≤
        (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) ∧
      (standardDualityGap (matrix k hk) (trajectory k hk) (trajectory k hk) t : ℝ) ≤
        (2 * constant k hk) * (t : ℝ) ^ (-(1 / (k : ℝ))) := by
  simpa only [matrix, trajectory, finGame_gap] using
    FaithfulRealization.all_integer_theta (clock k hk)

/-- The seven-action note's smaller family, together with the exact all-integer asymptotic and its
relative error estimate. There are no Clock, compatibility, parameter,
trajectory, phase-endpoint, or asymptotic premises. The positive action count
is written m+1 to make nonempty extrema explicit in the type. -/
theorem main_theorem (k : ℕ) (hk : 3 ≤ k) :
    ∃ (m : ℕ) (M : Matrix (Fin (m+1)) (Fin (m+1)) ℚ)
      (a : ℕ → Fin (m+1)) (c : ℝ),
      m+1 = (k+1)^2-9 ∧ IsSkewSymmetric M ∧ a 0 = 0 ∧
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
end Karlin.FaithfulSevenFamily
