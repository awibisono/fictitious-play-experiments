import Karlin.FaithfulRPS
import Karlin.FaithfulGameReindex
import Karlin.FaithfulConsequences

/-! Exact identification of the displayed order-two appendix matrix. -/
namespace Karlin.FaithfulAppendixRPS
open Filter Topology

def matrix : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, -313/36, -1, -299/36;
     313/36, 0, -1, 1;
     1, 1, 0, -1;
     299/36, -1, 1, 0]

theorem exact_matrix :
    FaithfulGameReindex.finGame FaithfulRPS.matrix = matrix := by
  decide +kernel

def trajectory : ℕ → Fin 4 := FaithfulGameReindex.finPlay FaithfulRPS.trajectory

theorem strict_simultaneous : IsStrictTwoPlayerFPTrajectory matrix trajectory trajectory := by
  rw [← exact_matrix]
  exact (FaithfulGameReindex.finGame_strictTwoPlayer_iff _ _ _).mpr
    FaithfulRPS.strict_simultaneous

theorem initial_setup : trajectory 0 = 0 := rfl

theorem exact_gap : 0 < FaithfulRPS.constant ∧
    Tendsto (fun t : ℕ => (standardDualityGap matrix trajectory trajectory t : ℝ) *
      (t : ℝ) ^ (1 / (2 : ℝ))) atTop (𝓝 FaithfulRPS.constant) := by
  simpa only [← exact_matrix, trajectory, FaithfulGameReindex.finGame_gap] using
    FaithfulRPS.exact_gap

theorem max_entry_bound (i j : Fin 4) : |matrix i j| ≤ 313/36 := by
  fin_cases i <;> fin_cases j <;> norm_num [matrix]

theorem max_entry_attained : |matrix 1 0| = 313/36 := by norm_num [matrix]

theorem shift_exact : FaithfulRealization.shift FaithfulSeed.rpsClock = 239/36 := by
  decide +kernel

theorem gridDenominator_exact :
    FaithfulRealization.gridDenominator FaithfulSeed.rpsClock = 3 := by decide +kernel

theorem constant_square : FaithfulRPS.constant ^ 2 = 8/9 := by
  have hL : FaithfulRealization.countCoeff FaithfulSeed.rpsClock 1 = 9 := by
    dsimp [FaithfulRealization.countCoeff, FaithfulRealization.extendRow,
      FaithfulClock.Clock.countTable, FaithfulSeed.rpsClock]
    have h : (∑ i : Fin 3, (FaithfulSeed.C2Integer i 1 : ℚ)) = 9 := by decide +kernel
    exact_mod_cast h
  have hxi : FaithfulRealization.scoreCoeff FaithfulSeed.rpsClock 1 = 1 := by
    dsimp [FaithfulRealization.scoreCoeff, FaithfulRealization.extendRow,
      FaithfulSeed.rpsClock, R2]
    norm_num
  unfold FaithfulRPS.constant FaithfulRealization.gapConstant
  rw [show 2 - 1 = 1 by omega, hL, hxi]
  rw [FaithfulConsequences.paperGapConstant_power 2 (by omega) 9 1 (by norm_num)]
  norm_num

theorem constant_exact : FaithfulRPS.constant = 2 * Real.sqrt 2 / 3 := by
  have hp := FaithfulRPS.exact_gap.1
  have hs := constant_square
  have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem normalized_constant_exact :
    FaithfulRPS.constant / (313/36) = 24 * Real.sqrt 2 / 313 := by
  rw [constant_exact]
  ring

end Karlin.FaithfulAppendixRPS
