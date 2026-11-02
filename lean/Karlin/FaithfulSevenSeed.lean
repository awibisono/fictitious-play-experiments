import Karlin.FaithfulSevenMarker
import Karlin.FaithfulSevenSuffix

/-! The actual six-recurrent-action cubic seed for the seven-action family.
Every field is earned on the literal Appendix data, including the signed marker,
all finite prefixes, and one fixed suffix constant before epsilon. -/
namespace Karlin.FaithfulSevenSeed
open scoped BigOperators
open FaithfulClock FaithfulWindow FaithfulSevenData
set_option maxHeartbeats 1600000

theorem count_injective : Function.Injective (fun x : Fin 3 → ℚ => C_seven.mulVec x) := by
  intro x y hxy
  have h0 := congr_fun hxy 0
  have h1 := congr_fun hxy 1
  have h3 := congr_fun hxy 3
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,C_seven] at h0 h1 h3
  funext i
  fin_cases i
  · change x 0 = y 0; linarith
  · change x 1 = y 1; linarith
  · change x 2 = y 2; linarith

theorem clock_equation : M_seven * ratCount CInteger = R_seven * N_mat 3 := by
  rw [ratCount_CInteger,M_seven_mul_C_eq_R_mul_N3]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [N3,N_mat]

theorem counter_equation : Matrix.vecMul v_seven (ratCount CInteger) = e0_row 3 := by
  rw [ratCount_CInteger]
  change (fun j => ∑ i : Fin 6, v_seven i * C_seven i j) = e0_row 3
  rw [v_seven_mul_C]
  ext i
  fin_cases i <;> norm_num [e0_row]


theorem runs_begins (p n : ℕ) (hn : 0 < n) : ∃ tail, runs p n = run p 0 ++ tail := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [runs_succ]
      by_cases hz : n=0
      · subst n
        refine ⟨[], ?_⟩
        simp [runs,consecutiveWord]
      · obtain ⟨tail, ht⟩ := ih (by omega)
        exact ⟨tail++run p n, by rw [ht,List.append_assoc]⟩

theorem begins_twice (q : ℕ) : ∃ tail, sevenWord q = (0:Fin 6)::0::tail := by
  let p := q-20
  have hn : 0 < sevenPhaseRunCount p := by unfold sevenPhaseRunCount; omega
  obtain ⟨tail,ht⟩ := runs_begins p (sevenPhaseRunCount p) hn
  have hr : run p 0 = List.replicate (6*(21*(p+20)+10)+1) (0:Fin 6) := by
    simp [run,sevenPhaseLen,sevenPhaseAct]
  have hl : ∃ L, 6*(21*(p+20)+10)+1 = L+1+1 := by
    exact ⟨6*(21*(p+20)+10)-1, by omega⟩
  obtain ⟨L,hL⟩ := hl
  refine ⟨List.replicate L 0 ++ tail, ?_⟩
  change runs p (sevenPhaseRunCount p) = _
  rw [ht,hr,hL]
  simp only [List.replicate_succ,List.cons_append]

theorem support_safe (q : ℕ) (hq : 20 ≤ q) (i : Fin 6) (hi : v_seven i ≠ 0) :
    R_seven.mulVec (binomBasis 3 q) i + M_seven i 0 - v_seven i <
    R_seven.mulVec (binomBasis 3 q) 0 + M_seven 0 0 - v_seven 0 := by
  rw [R_eval]
  have hqQ : (20:ℚ) ≤ q := by exact_mod_cast hq
  fin_cases i <;> simp_all [v_seven,V_seven,W_seven,Vg_seven,H_seven,s_seven,
    Fin.sum_univ_three,M_seven,G_seven,Q_seven,A_guard,L_seven] <;> nlinarith

/-- The literal order-three recurrent clock on six actions. -/
def sevenClock : Clock 3 where
  order_ge_two := by decide
  m := 6
  A := M_seven
  skew := M_seven_skew
  rank := Equiv.refl (Fin 6)
  R := R_seven
  C := CInteger
  b := 0
  v := v_seven
  Q := 20
  onset_pos := by decide
  word := sevenWord
  delta0 := 3433/1134000
  marker_pos := by norm_num
  Arem := 1
  remainder_nonneg := by norm_num
  threshold := FaithfulSevenSuffix.threshold
  threshold_onset := fun eps _ => FaithfulSevenSuffix.threshold_onset eps
  clock_eq := clock_equation
  full_column_rank := by rw [ratCount_CInteger]; exact count_injective
  leading_height := by norm_num [R_seven]
  valid := seven_valid
  counts := seven_counts
  begins_twice := fun q _ => begins_twice q
  counter_entry := rfl
  counter_table := counter_equation
  marker := seven_marker
  support_safe := support_safe
  suffix := FaithfulSevenSuffix.seven_suffix

@[simp] theorem sevenClock_m : sevenClock.m = 6 := rfl
@[simp] theorem sevenClock_A : sevenClock.A = M_seven := rfl
@[simp] theorem sevenClock_R : sevenClock.R = R_seven := rfl
@[simp] theorem sevenClock_C : sevenClock.C = CInteger := rfl
@[simp] theorem sevenClock_b : sevenClock.b = (0:Fin 6) := rfl
@[simp] theorem sevenClock_v : sevenClock.v = v_seven := rfl
@[simp] theorem sevenClock_Arem : sevenClock.Arem = 1 := rfl

end Karlin.FaithfulSevenSeed
