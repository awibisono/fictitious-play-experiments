import Karlin.FaithfulRealization

/-! Realization from every allowed fixed initial phase, as quantified in v15. -/
namespace Karlin.FaithfulClock.Clock

variable {k : ℕ}

def withOnset (P : Clock k) (Q : ℕ) (hQ : P.Q ≤ Q) : Clock k :=
  { P with
    Q := Q
    onset_pos := P.onset_pos.trans hQ
    threshold := fun eps => max Q (P.threshold eps)
    threshold_onset := fun _ _ => le_max_left _ _
    valid := fun q hq => P.valid q (hQ.trans hq)
    counts := fun q hq => P.counts q (hQ.trans hq)
    begins_twice := fun q hq => P.begins_twice q (hQ.trans hq)
    marker := fun q hq => P.marker q (hQ.trans hq)
    support_safe := fun q hq => P.support_safe q (hQ.trans hq)
    suffix := fun eps heps q hq => P.suffix eps heps q ((le_max_right _ _).trans hq) }

@[simp] theorem withOnset_word (P : Clock k) (Q : ℕ) (hQ : P.Q ≤ Q) :
    (withOnset P Q hQ).word = P.word := rfl

@[simp] theorem withOnset_Q (P : Clock k) (Q : ℕ) (hQ : P.Q ≤ Q) :
    (withOnset P Q hQ).Q = Q := rfl

end Karlin.FaithfulClock.Clock

namespace Karlin.FaithfulStartPhase
open Filter Topology FaithfulClock

variable {k : ℕ} (P : Clock k) (Q : ℕ) (hQ : P.Q ≤ Q)

def clock : Clock k := P.withOnset Q hQ

theorem phaseWord_exact (p : ℕ) :
    FaithfulRealization.phaseWord (clock P Q hQ) p = P.word (Q + p) := rfl

theorem constant_independent :
    FaithfulRealization.gapConstant (clock P Q hQ) = FaithfulRealization.gapConstant P := rfl

/-- The least denominator, rank bias and minimum shift are recomputed at this
arbitrary starting phase; no fictitious counts are introduced. -/
theorem realization_at_any_phase :
    IsSkewSymmetric (FaithfulRealization.game (clock P Q hQ)) ∧
    FaithfulRealization.play (clock P Q hQ) 0 = none ∧
    (∀ i, cumScore (FaithfulRealization.game (clock P Q hQ))
      (FaithfulRealization.play (clock P Q hQ)) 0 i = 0) ∧
    IsStrictTwoPlayerFPTrajectory (FaithfulRealization.game (clock P Q hQ))
      (FaithfulRealization.play (clock P Q hQ)) (FaithfulRealization.play (clock P Q hQ)) ∧
    0 < FaithfulRealization.gapConstant P ∧
    Tendsto (fun t : ℕ => (standardDualityGap (FaithfulRealization.game (clock P Q hQ))
      (FaithfulRealization.play (clock P Q hQ))
      (FaithfulRealization.play (clock P Q hQ)) t : ℝ) *
      (t : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 (FaithfulRealization.gapConstant P)) := by
  refine ⟨FaithfulRealization.game_skew _, rfl, FaithfulRealization.zero_initial_scores _,
    FaithfulRealization.simultaneous_strict _, ?_⟩
  exact FaithfulRealization.exact_gap_limit (clock P Q hQ)

theorem relative_error_at_any_phase :
    (fun t : ℕ => (standardDualityGap (FaithfulRealization.game (clock P Q hQ))
      (FaithfulRealization.play (clock P Q hQ)) (FaithfulRealization.play (clock P Q hQ)) t : ℝ) /
      (FaithfulRealization.gapConstant P * (t : ℝ) ^ (-(1 / (k : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (k : ℝ)))) :=
  FaithfulRealization.relative_gap_error (clock P Q hQ)

end Karlin.FaithfulStartPhase
