import Karlin.FaithfulSeedAdmissible
import Karlin.FaithfulRealization

/-! Closed order-two realization. These theorems have no Clock or trajectory
input. They do not assert existence of higher-order faithful clocks. -/
namespace Karlin.FaithfulRPS
open Filter Topology
open FaithfulSeed FaithfulRealization

abbrev matrix := game rpsClock
abbrev trajectory := play rpsClock
noncomputable def constant : ℝ := gapConstant rpsClock

theorem four_actions : Fintype.card (Option (Fin rpsClock.m)) = 4 := by decide

theorem common_initial_action : trajectory 0 = none := rfl

theorem zero_initial_scores (i : Option (Fin rpsClock.m)) :
    cumScore matrix trajectory 0 i = 0 := FaithfulRealization.zero_initial_scores rpsClock i

theorem strict_simultaneous : IsStrictTwoPlayerFPTrajectory matrix trajectory trajectory :=
  simultaneous_strict rpsClock

theorem unique_from_common_setup (row col : ℕ → Option (Fin rpsClock.m))
    (hw : IsWeakTwoPlayerFPTrajectory matrix row col)
    (hr : row 0 = none) (hc : col 0 = none) (t : ℕ) :
    row t = trajectory t ∧ col t = trajectory t := unique_from_setup rpsClock row col hw hr hc t

/-- Full closed all-integer limit, not merely positivity of its coefficient. -/
theorem exact_gap : 0 < constant ∧
    Tendsto (fun t : ℕ => (standardDualityGap matrix trajectory trajectory t : ℝ) *
      (t : ℝ) ^ (1 / (2 : ℝ))) atTop (𝓝 constant) := exact_gap_limit rpsClock

theorem relative_error :
    (fun t : ℕ => (standardDualityGap matrix trajectory trajectory t : ℝ) /
      (constant * (t : ℝ) ^ (-(1 / (2 : ℝ)))) - 1)
      =O[atTop] (fun t : ℕ => (t : ℝ) ^ (-(1 / (2 : ℝ)))) := relative_gap_error rpsClock

#print axioms exact_gap
#print axioms relative_error
#print axioms strict_simultaneous
end Karlin.FaithfulRPS
