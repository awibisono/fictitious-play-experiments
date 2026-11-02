import Karlin.FaithfulLift
import Karlin.FaithfulRealization
import Karlin.FaithfulMain

/-! Ordinary leading coefficients and polynomial remainder statements for the
literal clocks, moving parent bundles, and actual synthesized one-copy lift. -/
namespace Karlin.FaithfulGrowthRecurrences
open scoped BigOperators
open Filter Topology Asymptotics Polynomial
set_option maxHeartbeats 1200000
open FaithfulClock FaithfulGrowth FaithfulRateError

/-- Ordinary leading coefficient of a binomial row. -/
def leading {w : ℕ} (hw : 0 < w) (c : Fin w → ℚ) : ℚ :=
  c ⟨w-1, by omega⟩ / ((w-1).factorial : ℚ)

noncomputable def realRowPoly {w : ℕ} (c : Fin w → ℚ) : ℝ[X] :=
  binomialPoly (FaithfulRealization.extendRow c) (w-1)

theorem realRowPoly_eval {w : ℕ} (hw : 0 < w) (c : Fin w → ℚ) (q : ℕ) :
    (realRowPoly c).eval (q:ℝ) = (dotProduct c (binomBasis w q) : ℚ) := by
  rw [realRowPoly,binomialPoly_eval,show w-1+1=w by omega,
    ←FaithfulRealization.row_sum_eq_range]
  simp [dotProduct,binomBasis]

theorem row_expansion {w : ℕ} (hw : 0 < w) (c : Fin w → ℚ) :
    (fun q : ℕ => ((dotProduct c (binomBasis w q):ℚ):ℝ) -
      (leading hw c : ℝ)*(q:ℝ)^(w-1)) =O[atTop] (fun q : ℕ => (q:ℝ)^(w-2)) := by
  have ht : (realRowPoly c).coeff (w-1) = (leading hw c : ℝ) := by
    rw [realRowPoly,binomialPoly_top_coeff]
    simp [leading,FaithfulRealization.extendRow,show w-1<w by omega]
  apply IsBigO.of_bound (realCoeffMass (realRowPoly c) (w-1))
  filter_upwards [eventually_ge_atTop (1:ℕ)] with q hq
  have hb := polynomial_remainder_bound (realRowPoly c) (w-1)
    (binomialPoly_natDegree_le _ _) (q:ℝ) (by exact_mod_cast hq)
  rw [realRowPoly_eval hw,ht] at hb
  have he : w-1-1=w-2 := by omega
  simpa [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) (w-2)),he] using hb

variable {k : ℕ} (P : Clock k)

def lengthLeading : ℚ := leading (by have := P.order_ge_two; omega)
  (FaithfulGrowth.Clock.totalCountCoeff P)

def heightLeading : ℚ := leading (by have := P.order_ge_two; omega) (P.R P.b)

theorem lengthLeading_pos : 0 < lengthLeading P := by
  exact div_pos (FaithfulGrowth.Clock.leading_total_count_pos P) (by positivity)

theorem heightLeading_pos : 0 < heightLeading P := by
  exact div_pos P.leading_height (by positivity)

theorem phase_length_expansion :
    (fun q : ℕ => ((P.word q).length:ℝ)-(lengthLeading P:ℝ)*(q:ℝ)^(k-1))
      =O[atTop] (fun q : ℕ => (q:ℝ)^(k-2)) := by
  have hh := row_expansion (by have := P.order_ge_two; omega : 0<k)
    (FaithfulGrowth.Clock.totalCountCoeff P)
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop P.Q] with q hq
  have hc := FaithfulGrowth.Clock.lengthPoly_eval P q hq
  rw [FaithfulGrowth.Clock.lengthPoly,rowPoly_eval_nat] at hc
  have hc' : dotProduct (FaithfulGrowth.Clock.totalCountCoeff P) (binomBasis k q) =
      ((P.word q).length:ℚ) := hc
  rw [hc']
  rfl

theorem phase_height_expansion :
    (fun q : ℕ => (height P.b (P.entry q):ℝ)-(heightLeading P:ℝ)*(q:ℝ)^(k-1))
      =O[atTop] (fun q : ℕ => (q:ℝ)^(k-2)) := by
  have hh := row_expansion (by have := P.order_ge_two; omega : 0<k) (P.R P.b)
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop P.Q] with q hq
  rw [P.entry_height q hq]
  rfl

theorem factorial_step (P : Clock k) : (k.factorial : ℚ) = (k:ℚ)*((k-1).factorial:ℚ) := by
  have hk := P.order_ge_two
  have he : k=k-1+1 := by omega
  conv_lhs => rw [he,Nat.factorial_succ]
  push_cast
  congr 1
  exact_mod_cast (by omega : k-1+1=k)

def bundleLeading (tau : ℕ) : ℚ :=
  lengthLeading P * (tau:ℚ)^k * ((2:ℚ)^k-1) / k

def liftHeightLeading (tau : ℕ) : ℚ :=
  heightLeading P * (tau:ℚ)^(k-1) * ((2:ℚ)^(k-1)-1) / k

theorem bundle_row_leading (tau : ℕ) :
    leading (Nat.succ_pos k)
      (Matrix.vecMul (FaithfulGrowth.Clock.totalCountCoeff P) (F_tau_mat k tau)) =
      bundleLeading P tau := by
  unfold leading bundleLeading lengthLeading
  change Matrix.vecMul (FaithfulGrowth.Clock.totalCountCoeff P) (F_tau_mat k tau) (Fin.last k) / (k.factorial:ℚ) = _
  rw [FaithfulNextTables.vecMul_F_last (by have := P.order_ge_two; omega)]
  rw [factorial_step P]
  simp only [leading]
  ring

theorem zeta_row_leading (tau : ℕ) (c H : ℚ) :
    leading (Nat.succ_pos k) (FaithfulTables.zeta (P.R P.b) tau c H) =
      liftHeightLeading P tau := by
  unfold leading liftHeightLeading heightLeading
  change FaithfulTables.zeta (P.R P.b) tau c H (Fin.last k) / (k.factorial:ℚ) = _
  rw [FaithfulTables.zeta_leading P.order_ge_two]
  rw [factorial_step P]
  simp only [leading]
  ring

theorem canonical_height_expansion (tau : ℕ) (c H : ℚ) :
    (fun q : ℕ => ((dotProduct (FaithfulTables.zeta (P.R P.b) tau c H)
      (binomBasis (k+1) q):ℚ):ℝ) - (liftHeightLeading P tau:ℝ)*(q:ℝ)^k)
      =O[atTop] (fun q : ℕ => (q:ℝ)^(k-1)) := by
  have hh := row_expansion (Nat.succ_pos k) (FaithfulTables.zeta (P.R P.b) tau c H)
  simpa only [Nat.add_sub_cancel,zeta_row_leading] using hh


theorem bundle_length_table (tau q : ℕ) (hq : P.Q ≤ tau*q) :
    dotProduct (Matrix.vecMul (FaithfulGrowth.Clock.totalCountCoeff P) (F_tau_mat k tau))
      (binomBasis (k+1) q) = ((FaithfulWindow.dyadicWord P.word tau q).length:ℚ) := by
  rw [←Matrix.dotProduct_mulVec,list_length_eq_sum_wordCountVec]
  rw [FaithfulWindow.dyadicWord_count_table P.countTable P.word P.Q P.counts tau q hq,
    ←Matrix.mulVec_mulVec]
  simp only [FaithfulGrowth.Clock.totalCountCoeff,dotProduct,Matrix.mulVec,Finset.sum_mul]
  exact Finset.sum_comm

theorem bundle_length_expansion (tau : ℕ) (htau : 0 < tau) :
    (fun q : ℕ => ((FaithfulWindow.dyadicWord P.word tau q).length:ℝ) -
      (bundleLeading P tau:ℝ)*(q:ℝ)^k) =O[atTop] (fun q : ℕ => (q:ℝ)^(k-1)) := by
  have hh := row_expansion (Nat.succ_pos k)
    (Matrix.vecMul (FaithfulGrowth.Clock.totalCountCoeff P) (F_tau_mat k tau))
  simp only [bundle_row_leading] at hh
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop P.Q] with q hq
  rw [bundle_length_table P tau q (hq.trans (Nat.le_mul_of_pos_left q htau))]
  rfl

theorem bundle_sum_length (tau q : ℕ) :
    (FaithfulWindow.dyadicWord P.word tau q).length =
      ∑ s ∈ Finset.Ico (tau*q) (2*tau*q), (P.word s).length := by
  rw [FaithfulWindow.dyadicWord,FaithfulWindow.consecutiveWord_length,
    Finset.sum_Ico_eq_sum_range]
  have he : 2*tau*q=tau*q+tau*q := by ring
  rw [he,Nat.add_sub_cancel_left]

theorem bundle_sum_expansion (tau : ℕ) (htau : 0 < tau) :
    (fun q : ℕ => ((∑ s ∈ Finset.Ico (tau*q) (2*tau*q), (P.word s).length):ℝ) -
      (bundleLeading P tau:ℝ)*(q:ℝ)^k) =O[atTop] (fun q : ℕ => (q:ℝ)^(k-1)) := by
  simpa only [bundle_sum_length,Nat.cast_sum] using bundle_length_expansion P tau htau

theorem bundleLeading_pos (tau : ℕ) (htau : 0 < tau) : 0 < bundleLeading P tau := by
  have hk : 0 < k := by have := P.order_ge_two; omega
  have hp : (1:ℚ) < 2^k := one_lt_pow₀ (by norm_num) (by omega)
  exact div_pos (mul_pos (mul_pos (lengthLeading_pos P) (pow_pos (by exact_mod_cast htau) k))
    (by linarith)) (by exact_mod_cast hk)

theorem liftHeightLeading_pos (tau : ℕ) (htau : 0 < tau) : 0 < liftHeightLeading P tau := by
  have hk : 0 < k := by have := P.order_ge_two; omega
  have hp : (1:ℚ) < 2^(k-1) := one_lt_pow₀ (by norm_num) (by have := P.order_ge_two; omega)
  exact div_pos (mul_pos (mul_pos (heightLeading_pos P) (pow_pos (by exact_mod_cast htau) (k-1)))
    (by linarith)) (by exact_mod_cast hk)

theorem sum_rows {α β : Type*} [Fintype α] [Fintype β] {w : ℕ}
    (e : α ≃ β) (M : Matrix α (Fin w) ℚ) (j : Fin w) :
    (∑ i : β, FaithfulReindex.rows e M i j) = ∑ i : α, M i j :=
  Equiv.sum_comp e.symm (fun i => M i j)

theorem shifted_last {α : Type*} (M : Matrix α (Fin (k+1)) ℚ) (i : α) :
    (M*T_mat (k+1)) i (Fin.last k)=M i (Fin.last k) := by
  rw [T_mat,Matrix.mul_add,Matrix.mul_one,Matrix.add_apply,mul_N_mat_apply]
  simp

theorem nextCounts_last {o r : Type*} [Fintype o] [Fintype r]
    (X : Matrix o (Fin (k+1)) ℚ) (M : Matrix r (Fin (k+1)) ℚ) :
    (∑ i : o ⊕ r, FaithfulNextTables.nextCounts X M i (Fin.last k)) =
      (∑ i : o, X i (Fin.last k))+(∑ i : r, M i (Fin.last k)) := by
  simp [FaithfulNextTables.nextCounts,Fintype.sum_sum_type,shifted_last]

theorem X_sum_last (tau : ℕ) :
    (∑ i : FaithfulTables.OldAct P, FaithfulTables.X P tau i (Fin.last k)) =
      FaithfulGrowth.Clock.totalCountCoeff P ⟨k-1,by have := P.order_ge_two; omega⟩ *
        ((tau:ℚ)^k*((2:ℚ)^k-1)) := by
  have hk : 0<k := by have := P.order_ge_two; omega
  simp only [FaithfulTables.X,Fintype.sum_sum_type,Matrix.fromRows_apply_inl,Matrix.fromRows_apply_inr]
  have he (i : Fin P.m) : (P.countTable * F_tau_mat k tau) i (Fin.last k) =
      P.countTable i ⟨k-1,by omega⟩*((tau:ℚ)^k*((2:ℚ)^k-1)) :=
    FaithfulNextTables.vecMul_F_last hk (P.countTable i) tau
  simp only [he]
  simp [e0_row,Nat.ne_of_gt hk,FaithfulGrowth.Clock.totalCountCoeff,Finset.sum_mul]

variable {P} (A : FaithfulAdmissible.Admissible P)

/-- The actual integer reset table at the synthesized scales, before relabeling. -/
noncomputable def actualResetTable :=
  FaithfulParameters.AdmissibleParameters.resetTable A (FaithfulController.firstScale A)
    (FaithfulController.secondScale A (FaithfulController.firstScale A))

theorem nextClock_count_table : (FaithfulLift.nextClock A).countTable =
    FaithfulReindex.rows (FaithfulLift.actionEquiv (P:=P))
      (FaithfulLift.originalCounts A (FaithfulController.firstScale A)
        (FaithfulController.secondScale A (FaithfulController.firstScale A))) := by
  change FaithfulReindex.rows finSumFinEquiv
    (fun i j => (FaithfulNextClock.Lift.nextCountInt A _ _ i j:ℚ)) = _
  rw [FaithfulNextClock.Lift.nextCountInt_cast,FaithfulLift.normalized_count_table]
  rfl

theorem next_height_recurrence : heightLeading (FaithfulLift.nextClock A) =
    heightLeading P*(A.tau:ℚ)^(k-1)*((2:ℚ)^(k-1)-1)/k := by
  have he : (FaithfulLift.nextClock A).R (FaithfulLift.nextClock A).b =
      FaithfulNextClock.Lift.zeta A (FaithfulController.firstScale A) := by
    simp only [FaithfulLift.nextClock,FaithfulNextClockAssembly.nextClock_R,
      FaithfulNextClockAssembly.nextClock_b]
    funext j
    rw [FaithfulReindex.rows_apply,Equiv.symm_apply_apply]
    exact congrFun (FaithfulNextClock.Lift.score_reset_zero A _ _) j
  unfold heightLeading
  rw [he]
  exact zeta_row_leading P A.tau _ _

theorem next_count_top : FaithfulGrowth.Clock.totalCountCoeff (FaithfulLift.nextClock A)
    (Fin.last k) =
      FaithfulGrowth.Clock.totalCountCoeff P ⟨k-1,by have := P.order_ge_two; omega⟩ *
        ((A.tau:ℚ)^k*((2:ℚ)^k-1)) +
      ∑ i : Fin (k+1) ⊕ Fin (k+1), ((actualResetTable A i (Fin.last k):ℤ):ℚ) := by
  unfold FaithfulGrowth.Clock.totalCountCoeff
  rw [nextClock_count_table,sum_rows,FaithfulLift.originalCounts,nextCounts_last,X_sum_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he := congrFun (congrFun (FaithfulParameters.AdmissibleParameters.resetTable_cast A
    (FaithfulController.firstScale A)
    (FaithfulController.secondScale A (FaithfulController.firstScale A))) i) (Fin.last k)
  exact he.symm

theorem next_length_recurrence : lengthLeading (FaithfulLift.nextClock A) =
    lengthLeading P*(A.tau:ℚ)^k*((2:ℚ)^k-1)/k +
      (∑ i : Fin (k+1) ⊕ Fin (k+1), ((actualResetTable A i (Fin.last k):ℤ):ℚ))/(k.factorial:ℚ) := by
  change FaithfulGrowth.Clock.totalCountCoeff (FaithfulLift.nextClock A) (Fin.last k) /
    (k.factorial:ℚ) = _
  rw [next_count_top,add_div]
  congr 1
  unfold lengthLeading leading
  rw [factorial_step P]
  ring


theorem actual_reset_leading_pos (i : Fin (k+1) ⊕ Fin (k+1)) :
    0 < actualResetTable A i (Fin.last k) := by
  have hv := FaithfulController.chosen_valid A
  have he := congrFun (congrFun (FaithfulParameters.AdmissibleParameters.resetTable_cast A
    (FaithfulController.firstScale A)
    (FaithfulController.secondScale A (FaithfulController.firstScale A))) i) (Fin.last k)
  change (actualResetTable A i (Fin.last k):ℚ) = _ at he
  have hp : (0:ℚ) < actualResetTable A i (Fin.last k) := by
    rw [he]
    cases i with
    | inl i => exact (hv.reset_leading i).1
    | inr i => exact (hv.reset_leading i).2
  exact_mod_cast hp

theorem next_length_positive : 0 < lengthLeading (FaithfulLift.nextClock A) :=
  lengthLeading_pos (FaithfulLift.nextClock A)

/-- The same recurrence on the actual RPS-started recursive family. -/
theorem family_clock_successor (k : ℕ) (hk : 2 ≤ k) :
    FaithfulMain.clock (k+1) (by omega) =
      FaithfulLift.nextClock (FaithfulMain.admissible k hk) := by
  obtain ⟨n, rfl⟩ : ∃ n, k=n+2 := ⟨k-2,by omega⟩
  rfl

theorem family_height_recurrence (k : ℕ) (hk : 2 ≤ k) :
    heightLeading (FaithfulMain.clock (k+1) (by omega)) =
      heightLeading (FaithfulMain.clock k hk)*(FaithfulMain.admissible k hk).tau^(k-1)*
        ((2:ℚ)^(k-1)-1)/k := by
  rw [family_clock_successor]
  exact next_height_recurrence (FaithfulMain.admissible k hk)

theorem family_length_recurrence (k : ℕ) (hk : 2 ≤ k) :
    lengthLeading (FaithfulMain.clock (k+1) (by omega)) =
      lengthLeading (FaithfulMain.clock k hk)*(FaithfulMain.admissible k hk).tau^k*
        ((2:ℚ)^k-1)/k +
      (∑ i : Fin (k+1) ⊕ Fin (k+1),
        ((actualResetTable (FaithfulMain.admissible k hk) i (Fin.last k):ℤ):ℚ))/(k.factorial:ℚ) := by
  rw [family_clock_successor]
  exact next_length_recurrence (FaithfulMain.admissible k hk)


/-- A fixed real gain changes the canonical height only by a linear term.
This is stronger than the polynomial-only hypothesis in the growth lemma. -/
theorem real_height_solution (P : Clock k) (tau : ℕ) (c : ℝ) (z : ℕ → ℝ)
    (hz : ∀ q : ℕ, z (q+1)-z q =
      (P.entry (2*tau*(q+1)) P.b:ℝ)-(P.entry (tau*(q+1)) P.b:ℝ)+c) (q : ℕ) :
    z q = (FaithfulTables.heightValue P tau 0 0 q:ℝ)+c*q+z 0 := by
  induction q with
  | zero => simp [FaithfulTables.heightValue_zero]
  | succ q ih =>
      have hc := FaithfulTables.heightValue_step P tau q 0 0
      have hcR : (FaithfulTables.heightValue P tau 0 0 (q+1):ℝ)-
          (FaithfulTables.heightValue P tau 0 0 q:ℝ) =
          (P.entry (2*tau*(q+1)) P.b:ℝ)-(P.entry (tau*(q+1)) P.b:ℝ) := by
        exact_mod_cast (by simpa only [add_zero] using hc)
      push_cast
      linarith [hz q]

theorem linear_remainder (P : Clock k) (c H : ℝ) :
    (fun q : ℕ => c*(q:ℝ)+H) =O[atTop] (fun q : ℕ => (q:ℝ)^(k-1)) := by
  apply IsBigO.of_bound (|c|+|H|)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with q hq
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hp : (q:ℝ) ≤ (q:ℝ)^(k-1) := by
    simpa using pow_le_pow_right₀ hqR (by have := P.order_ge_two; omega : 1 ≤ k-1)
  have h1 : (1:ℝ) ≤ (q:ℝ)^(k-1) := one_le_pow₀ hqR
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq0 (k-1))]
  calc
    |c*(q:ℝ)+H| ≤ |c*(q:ℝ)|+|H| := abs_add_le _ _
    _ = |c| * (q:ℝ)+|H| := by rw [abs_mul,abs_of_nonneg hq0]
    _ ≤ (|c|+|H|) * (q:ℝ)^(k-1) := by
      nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg c),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg H)]

/-- The height-growth statement for any real-valued solution, with arbitrary
fixed real gain. No upper bound on the polynomial degree is presumed. -/
theorem general_height_expansion (P : Clock k) (tau : ℕ) (c : ℝ) (z : ℕ → ℝ)
    (hz : ∀ q : ℕ, z (q+1)-z q =
      (P.entry (2*tau*(q+1)) P.b:ℝ)-(P.entry (tau*(q+1)) P.b:ℝ)+c) :
    (fun q : ℕ => z q-(liftHeightLeading P tau:ℝ)*(q:ℝ)^k)
      =O[atTop] (fun q : ℕ => (q:ℝ)^(k-1)) := by
  have hc := canonical_height_expansion P tau 0 0
  have hl := linear_remainder P c (z 0)
  apply (hc.add hl).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [] with q
  rw [real_height_solution P tau c z hz q]
  dsimp only [FaithfulTables.heightValue]
  ring

/-- In particular, every real polynomial satisfying the manuscript's backward
height equation has the claimed leading growth, for every fixed real c. -/
theorem polynomial_height_expansion (P : Clock k) (tau : ℕ) (c : ℝ) (z : ℝ[X])
    (hz : ∀ q : ℕ, 1 ≤ q → z.eval (q:ℝ)-z.eval ((q:ℝ)-1) =
      (P.entry (2*tau*q) P.b:ℝ)-(P.entry (tau*q) P.b:ℝ)+c) :
    (fun q : ℕ => z.eval (q:ℝ)-(liftHeightLeading P tau:ℝ)*(q:ℝ)^k)
      =O[atTop] (fun q : ℕ => (q:ℝ)^(k-1)) := by
  apply general_height_expansion P tau c (fun q => z.eval (q:ℝ))
  intro q
  have hh := hz (q+1) (by omega)
  simpa using hh

end Karlin.FaithfulGrowthRecurrences
