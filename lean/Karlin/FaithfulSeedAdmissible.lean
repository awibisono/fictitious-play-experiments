import Karlin.FaithfulAdmissible
import Karlin.FaithfulSeed
/-! The concrete additional data of v15 Proposition 6.1, on the literal seed.
All matrix equalities are checked by kernel reduction; no native_decide is used.
-/
namespace Karlin.FaithfulSeedAdmissible
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
open Karlin Karlin.FaithfulAdmissible Karlin.FaithfulTables Karlin.FaithfulSeed
theorem reference_height : zeta (rpsClock.R rpsClock.b) 1 (1/2) (baseline rpsClock) = ![4, 3/2, 1] := by
  dsimp [baseline, rpsClock]
  unfold zeta antiderivative increment R2 E_2tau_mat E_tau_mat T_mat N_mat e0_row
  decide +kernel
theorem actual_reference_summary : (D rpsClock 1 (1/2) (baseline rpsClock) 0).transpose * X rpsClock 1 = D0tX_rps := by
  dsimp [D, S, oldGame, X, FaithfulClock.Clock.countTable, FaithfulClock.ratCount, baseline, rpsClock, C2Integer]
  decide +kernel
theorem actual_reference_cone : Matrix.vecMul (oldWeight rpsClock (fun _ => 2/27) (1/2)) (X rpsClock 1) =
    zeta (rpsClock.R rpsClock.b) 1 (1/2) (baseline rpsClock) +
    Matrix.vecMul (zeta (rpsClock.R rpsClock.b) 1 (1/2) (baseline rpsClock)) (B_mat 3) := by
  dsimp [oldWeight, baseline, rpsClock, X, FaithfulClock.Clock.countTable, FaithfulClock.ratCount, C2Integer]
  decide +kernel

/-- The paper's tau=1, cref=1/2, zero correction and three weights 2/27. -/
def rpsAdmissible : Admissible rpsClock where
  tau := 1
  tau_pos := by decide
  cref := 1/2
  cref_pos := by norm_num
  cref_lt_one := by norm_num
  ellStar := fun _ => 0
  aP := fun _ => 2/27
  weights_pos := by intro i; norm_num
  higher_tests := by
    intro h hlow hhigh heven
    obtain ⟨n, hn⟩ := heven
    have hh : h = 4 := by omega
    have hzero := prop_6_1_rps_seed_admissible.2.2.2
    rw [hh, actual_reference_summary]
    have hz : outerProd (fun _ : Fin 3 => ((0 : ℤ) : ℚ))
        (psi (rpsClock.R rpsClock.b) 1 (1/2) (baseline rpsClock)) = 0 := by
      ext i j
      simp [outerProd]
    rw [hz, sub_zero]
    exact hzero
  cone := actual_reference_cone

#print axioms rpsAdmissible
#print axioms actual_reference_summary
end Karlin.FaithfulSeedAdmissible
