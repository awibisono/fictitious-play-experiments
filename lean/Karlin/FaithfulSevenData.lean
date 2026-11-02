import Karlin.FaithfulClock
import Karlin.UnrolledTrajectory

/-! Literal recurrent data and finite words for the seven-action cubic seed.
The run certificates below expose the exact run proofs already used by the
unrolled trajectory; no trajectory or final asymptotic theorem is assumed. -/
namespace Karlin.FaithfulSevenData
open scoped BigOperators
open FaithfulClock FaithfulWindow
set_option maxHeartbeats 1600000

def CInteger : Matrix (Fin 6) (Fin 3) ℤ :=
  !![456,2443,2058;468,2457,2058;480,2471,2058;
     12498,-1422,1764;2422,3282,1764;36442,-12594,1764]

theorem ratCount_CInteger : ratCount CInteger = C_seven := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def run (p v : ℕ) : List (Fin 6) :=
  List.replicate (sevenPhaseLen p v) (sevenPhaseAct p v)
def runs (p n : ℕ) : List (Fin 6) := consecutiveWord (run p) 0 n
def phaseWord (p : ℕ) : List (Fin 6) := runs p (sevenPhaseRunCount p)
def sevenWord (q : ℕ) : List (Fin 6) := phaseWord (q-20)

theorem phase_len_pos (p v : ℕ) : 0 < sevenPhaseLen p v := by
  unfold sevenPhaseLen
  split_ifs with h1 h2 h3
  · have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
    rcases hmod with hm | hm | hm <;> simp [hm]
  · positivity
  · positivity
  · positivity

theorem phase_step (p v : ℕ) (hv : v < sevenPhaseRunCount p) :
    sevenPhaseScore p (v + 1) = scoreVec M_seven (sevenPhaseScore p v)
      (runCount (fun _ => 0) (sevenPhaseAct p v) (sevenPhaseLen p v : ℚ)) := by
  unfold sevenPhaseRunCount at hv
  by_cases hcore : v < 21 * p + 438
  · have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
    rcases hmod with hm0 | hm1 | hm2
    · have hv1 : v + 1 < 21 * p + 438 := by omega
      have hdiv : (v + 1) / 3 = v / 3 := by omega
      have hm_next : (v + 1) % 3 = 1 := by omega
      have hact : sevenPhaseAct p v = 0 := by simp [sevenPhaseAct, hcore, hm0]
      have hlen : (sevenPhaseLen p v : ℚ) =
          6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 1 := by
        simp [sevenPhaseLen, hcore, hm0]
      have hs0 : sevenPhaseScore p v =
          stateCoreStart ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hcore, hm0]
      have hs1 : sevenPhaseScore p (v + 1) =
          stateCoreAfterR1 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hv1, hdiv, hm_next]
      rw [hs0, hs1, hact, hlen]
      exact (seven_core_full_transitions ((p : ℚ) + 20)
        ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)).1.symm
    · have hv1 : v + 1 < 21 * p + 438 := by omega
      have hdiv : (v + 1) / 3 = v / 3 := by omega
      have hm_next : (v + 1) % 3 = 2 := by omega
      have hact : sevenPhaseAct p v = 1 := by simp [sevenPhaseAct, hcore, hm1]
      have hlen : (sevenPhaseLen p v : ℚ) =
          6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 3 := by
        simp [sevenPhaseLen, hcore, hm1]
      have hs0 : sevenPhaseScore p v =
          stateCoreAfterR1 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hcore, hm1]
      have hs1 : sevenPhaseScore p (v + 1) =
          stateCoreAfterR2 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hv1, hdiv, hm_next]
      rw [hs0, hs1, hact, hlen]
      exact (seven_core_full_transitions ((p : ℚ) + 20)
        ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)).2.1.symm
    · have hdiv : (v + 1) / 3 = v / 3 + 1 := by omega
      have hm_next : (v + 1) % 3 = 0 := by omega
      have hact : sevenPhaseAct p v = 2 := by simp [sevenPhaseAct, hcore, hm2]
      have hlen : (sevenPhaseLen p v : ℚ) =
          6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 5 := by
        simp [sevenPhaseLen, hcore, hm2]
      have hs0 : sevenPhaseScore p v =
          stateCoreAfterR2 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hcore, hm2]
      rw [hs0, hact, hlen]
      rw [(seven_core_full_transitions ((p : ℚ) + 20)
        ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ)).2.2]
      by_cases hv1 : v + 1 < 21 * p + 438
      · have hs1 : sevenPhaseScore p (v + 1) =
            stateCoreStart ((p : ℚ) + 20)
              ((21 * (p + 20) + 10 + (v + 1) / 3 : ℕ) : ℚ) := by
          simp [sevenPhaseScore, hv1, hm_next]
        rw [hs1, hdiv]
        have hcast : ((21 * (p + 20) + 10 + (v / 3 + 1) : ℕ) : ℚ) =
            ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 1 := by
          push_cast; ring
        rw [hcast]
      · have hv_end : v + 1 = 21 * p + 438 := by omega
        have hdiv_end : v / 3 = 7 * p + 145 := by omega
        have hs1 : sevenPhaseScore p (v + 1) = stateBeforeG1 ((p : ℚ) + 20) := by
          simp [sevenPhaseScore, hv_end]
        rw [hs1, hdiv_end]
        have hcast : ((21 * (p + 20) + 10 + (7 * p + 145) : ℕ) : ℚ) + 1 =
            28 * ((p : ℚ) + 20) + 16 := by
          push_cast; ring
        rw [hcast, stateCoreStart_at_end]
  · have hg : v = 21 * p + 438 ∨ v = 21 * p + 439 ∨ v = 21 * p + 440 := by omega
    rcases hg with hg1 | hg2 | hg3
    · subst hg1
      have hlen : (sevenPhaseLen p (21 * p + 438) : ℚ) = L_seven ((p : ℚ) + 20) 0 := by
        simp [sevenPhaseLen, L_seven]
        ring
      have hs0 : sevenPhaseScore p (21 * p + 438) = stateBeforeG1 ((p : ℚ) + 20) := by
        simp [sevenPhaseScore]
      have hs1 : sevenPhaseScore p (21 * p + 438 + 1) = stateBeforeG2 ((p : ℚ) + 20) := by
        have h1 : ¬ (21 * p + 438 + 1 < 21 * p + 438) := by omega
        have h3 : 21 * p + 438 + 1 = 21 * p + 439 := by omega
        simp [sevenPhaseScore, h1, h3]
      have hact : sevenPhaseAct p (21 * p + 438) = 3 := by simp [sevenPhaseAct]
      rw [hs0, hs1, hact, hlen]
      exact (seven_guard_transitions ((p : ℚ) + 20)).1.symm
    · subst hg2
      have hlen : (sevenPhaseLen p (21 * p + 439) : ℚ) = L_seven ((p : ℚ) + 20) 1 := by
        have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
        simp [sevenPhaseLen, h1, L_seven]
        ring
      have hs0 : sevenPhaseScore p (21 * p + 439) = stateBeforeG2 ((p : ℚ) + 20) := by
        have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
        simp [sevenPhaseScore, h1]
      have hs1 : sevenPhaseScore p (21 * p + 439 + 1) = stateBeforeG3 ((p : ℚ) + 20) := by
        have h1 : ¬ (21 * p + 439 + 1 < 21 * p + 438) := by omega
        have h4 : 21 * p + 439 + 1 = 21 * p + 440 := by omega
        simp [sevenPhaseScore, h1, h4]
      have hact : sevenPhaseAct p (21 * p + 439) = 4 := by
        have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
        simp [sevenPhaseAct, h1]
      rw [hs0, hs1, hact, hlen]
      exact (seven_guard_transitions ((p : ℚ) + 20)).2.1.symm
    · subst hg3
      have hlen : (sevenPhaseLen p (21 * p + 440) : ℚ) = L_seven ((p : ℚ) + 20) 2 := by
        have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
        simp [sevenPhaseLen, h1, L_seven]
        ring
      have hs0 : sevenPhaseScore p (21 * p + 440) = stateBeforeG3 ((p : ℚ) + 20) := by
        have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
        simp [sevenPhaseScore, h1]
      have hs1 : sevenPhaseScore p (21 * p + 440 + 1) =
          V_seven ((p : ℚ) + 20 + 1) := by
        have h1 : ¬ (21 * p + 440 + 1 < 21 * p + 438) := by omega
        simp [sevenPhaseScore, h1]
        congr 1
        ring
      have hact : sevenPhaseAct p (21 * p + 440) = 5 := by
        have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
        simp [sevenPhaseAct, h1]
      rw [hs0, hs1, hact, hlen]
      exact (seven_guard_transitions ((p : ℚ) + 20)).2.2.symm

theorem phase_run_strict (p v : ℕ) (hv : v < sevenPhaseRunCount p)
    (h : ℕ) (hh : h < sevenPhaseLen p v) (j : Fin 6) (hj : j ≠ sevenPhaseAct p v) :
    scoreVec M_seven (sevenPhaseScore p v)
      (runCount (fun _ => 0) (sevenPhaseAct p v) (h : ℚ)) j <
    scoreVec M_seven (sevenPhaseScore p v)
      (runCount (fun _ => 0) (sevenPhaseAct p v) (h : ℚ)) (sevenPhaseAct p v) := by
  unfold sevenPhaseRunCount at hv
  have hk : (20 : ℚ) ≤ (p : ℚ) + 20 := by
    have : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
    linarith
  by_cases hcore : v < 21 * p + 438
  · have hℓ1 : 21 * ((p : ℚ) + 20) + 10 ≤ ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
      have hnat : 21 * (p + 20) + 10 ≤ 21 * (p + 20) + 10 + v / 3 := Nat.le_add_right _ _
      have hrat : ((21 * (p + 20) + 10 : ℕ) : ℚ) ≤ ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        exact_mod_cast hnat
      have hcast : ((21 * (p + 20) + 10 : ℕ) : ℚ) = 21 * ((p : ℚ) + 20) + 10 := by
        push_cast; ring
      linarith
    have hℓ2 : ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) ≤ 28 * ((p : ℚ) + 20) + 15 := by
      have hnat : 21 * (p + 20) + 10 + v / 3 ≤ 28 * (p + 20) + 15 := by omega
      have hrat : ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) ≤ ((28 * (p + 20) + 15 : ℕ) : ℚ) := by
        exact_mod_cast hnat
      have hcast : ((28 * (p + 20) + 15 : ℕ) : ℚ) = 28 * ((p : ℚ) + 20) + 15 := by
        push_cast; ring
      linarith
    have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
    rcases hmod with hm0 | hm1 | hm2
    · have hact : sevenPhaseAct p v = 0 := by simp [sevenPhaseAct, hcore, hm0]
      have hs0 : sevenPhaseScore p v =
          stateCoreStart ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hcore, hm0]
      have hhL : (h : ℚ) ≤ (6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 1) - 1 := by
        simp [sevenPhaseLen, hcore, hm0] at hh
        have hnat : h ≤ 6 * (21 * (p + 20) + 10 + v / 3) := by omega
        have hrat : (h : ℚ) ≤ 6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by exact_mod_cast hnat
        linarith
      rw [hact] at hj ⊢
      rw [hs0]
      have hv0 := seven_core_full_r1_valid hk hℓ1 hℓ2 (Nat.cast_nonneg h) hhL j hj
      linarith
    · have hact : sevenPhaseAct p v = 1 := by simp [sevenPhaseAct, hcore, hm1]
      have hs0 : sevenPhaseScore p v =
          stateCoreAfterR1 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hcore, hm1]
      have hhL : (h : ℚ) ≤ (6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 3) - 1 := by
        simp [sevenPhaseLen, hcore, hm1] at hh
        have hnat : h ≤ 6 * (21 * (p + 20) + 10 + v / 3) + 2 := by omega
        have hrat : (h : ℚ) ≤ 6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 2 := by
          exact_mod_cast hnat
        linarith
      rw [hact] at hj ⊢
      rw [hs0]
      have hv1 := seven_core_full_r2_valid hk hℓ1 hℓ2 (Nat.cast_nonneg h) hhL j hj
      linarith
    · have hact : sevenPhaseAct p v = 2 := by simp [sevenPhaseAct, hcore, hm2]
      have hs0 : sevenPhaseScore p v =
          stateCoreAfterR2 ((p : ℚ) + 20) ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) := by
        simp [sevenPhaseScore, hcore, hm2]
      have hhL : (h : ℚ) ≤ (6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 5) - 1 := by
        simp [sevenPhaseLen, hcore, hm2] at hh
        have hnat : h ≤ 6 * (21 * (p + 20) + 10 + v / 3) + 4 := by omega
        have hrat : (h : ℚ) ≤ 6 * ((21 * (p + 20) + 10 + v / 3 : ℕ) : ℚ) + 4 := by
          exact_mod_cast hnat
        linarith
      rw [hact] at hj ⊢
      rw [hs0]
      have hv2 := seven_core_full_r3_valid hk hℓ1 hℓ2 (Nat.cast_nonneg h) hhL j hj
      linarith
  · have hg : v = 21 * p + 438 ∨ v = 21 * p + 439 ∨ v = 21 * p + 440 := by omega
    rcases hg with hg1 | hg2 | hg3
    · subst hg1
      have hact : sevenPhaseAct p (21 * p + 438) = 3 := by simp [sevenPhaseAct]
      have hs0 : sevenPhaseScore p (21 * p + 438) = stateBeforeG1 ((p : ℚ) + 20) := by
        simp [sevenPhaseScore]
      have hhL : (h : ℚ) ≤ L_seven ((p : ℚ) + 20) 0 - 1 := by
        simp [sevenPhaseLen] at hh
        have hnat : h + 1 ≤ 882 * p ^ 2 + 32976 * p + 319218 := by omega
        have hrat : (h : ℚ) + 1 ≤ 882 * (p : ℚ) ^ 2 + 32976 * (p : ℚ) + 319218 := by
          exact_mod_cast hnat
        have hL : L_seven ((p : ℚ) + 20) 0 =
            882 * (p : ℚ) ^ 2 + 32976 * (p : ℚ) + 319218 := by
          simp [L_seven]; ring
        linarith
      rw [hact] at hj ⊢
      rw [hs0]
      have hvg1 := seven_guard1_run_valid hk (Nat.cast_nonneg h) hhL j hj
      linarith
    · subst hg2
      have h1 : ¬ (21 * p + 439 < 21 * p + 438) := by omega
      have hact : sevenPhaseAct p (21 * p + 439) = 4 := by simp [sevenPhaseAct, h1]
      have hs0 : sevenPhaseScore p (21 * p + 439) = stateBeforeG2 ((p : ℚ) + 20) := by
        simp [sevenPhaseScore, h1]
      have hhL : (h : ℚ) ≤ L_seven ((p : ℚ) + 20) 1 - 1 := by
        simp [sevenPhaseLen, h1] at hh
        have hnat : h + 1 ≤ 882 * p ^ 2 + 37680 * p + 403222 := by omega
        have hrat : (h : ℚ) + 1 ≤ 882 * (p : ℚ) ^ 2 + 37680 * (p : ℚ) + 403222 := by
          exact_mod_cast hnat
        have hL : L_seven ((p : ℚ) + 20) 1 =
            882 * (p : ℚ) ^ 2 + 37680 * (p : ℚ) + 403222 := by
          simp [L_seven]; ring
        linarith
      rw [hact] at hj ⊢
      rw [hs0]
      have hvg2 := seven_guard2_run_valid hk (Nat.cast_nonneg h) hhL j hj
      linarith
    · subst hg3
      have h1 : ¬ (21 * p + 440 < 21 * p + 438) := by omega
      have hact : sevenPhaseAct p (21 * p + 440) = 5 := by simp [sevenPhaseAct, h1]
      have hs0 : sevenPhaseScore p (21 * p + 440) = stateBeforeG3 ((p : ℚ) + 20) := by
        simp [sevenPhaseScore, h1]
      have hhL : (h : ℚ) ≤ L_seven ((p : ℚ) + 20) 2 - 1 := by
        simp [sevenPhaseLen, h1] at hh
        have hnat : h + 1 ≤ 882 * p ^ 2 + 21804 * p + 119722 := by omega
        have hrat : (h : ℚ) + 1 ≤ 882 * (p : ℚ) ^ 2 + 21804 * (p : ℚ) + 119722 := by
          exact_mod_cast hnat
        have hL : L_seven ((p : ℚ) + 20) 2 =
            882 * (p : ℚ) ^ 2 + 21804 * (p : ℚ) + 119722 := by
          simp [L_seven]; ring
        linarith
      rw [hact] at hj ⊢
      rw [hs0]
      have hvg3 := seven_guard3_run_valid hk (Nat.cast_nonneg h) hhL j hj
      linarith


theorem R_eval (q : ℕ) : R_seven.mulVec (binomBasis 3 q) = V_seven q := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, R_seven, binomBasis,
      Nat.cast_choose_two, V_seven, W_seven, Vg_seven, H_seven, s_seven,
      G_seven, Q_seven, A_guard, L_seven] <;> ring

theorem C_eval (q : ℕ) : C_seven.mulVec (binomBasis 3 q) = QL_seven q := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, C_seven, binomBasis,
      Nat.cast_choose_two, QL_seven, Q_seven, L_seven] <;> ring

theorem phase_start (p : ℕ) : sevenPhaseScore p 0 = V_seven ((p : ℚ)+20) := by
  have h : 0 < 21*p+438 := by omega
  simp only [sevenPhaseScore, h, ↓reduceIte, Nat.zero_div, Nat.add_zero]
  convert stateCoreStart_at_begin ((p : ℚ)+20) using 1
  push_cast
  ring

theorem phase_end (p : ℕ) : sevenPhaseScore p (sevenPhaseRunCount p) =
    V_seven ((p : ℚ)+20+1) := by
  have h1 : ¬21*p+441 < 21*p+438 := by omega
  have h2 : 21*p+441 ≠ 21*p+438 := by omega
  have h3 : 21*p+441 ≠ 21*p+439 := by omega
  have h4 : 21*p+441 ≠ 21*p+440 := by omega
  simp [sevenPhaseScore, sevenPhaseRunCount, h1]
  congr 1
  ring

theorem run_score (p v : ℕ) (hv : v < sevenPhaseRunCount p) :
    wordScore M_seven (sevenPhaseScore p v) (run p v) = sevenPhaseScore p (v+1) := by
  rw [phase_step p v hv]
  ext i
  rw [run, wordScore_replicate, scoreVec_runCount]
  simp [scoreVec, mul_comm]

theorem run_valid (p v : ℕ) (hv : v < sevenPhaseRunCount p) :
    IsValidPriorityWord M_seven (sevenPhaseScore p v) (Equiv.refl (Fin 6)) (run p v) := by
  apply isValidPriorityWord_of_isValidStrictWord
  intro h hh j hj
  have hh' : h < sevenPhaseLen p v := by simpa [run] using hh
  have hj' : j ≠ sevenPhaseAct p v := by simpa [run] using hj
  have ht : (run p v).take h = List.replicate h (sevenPhaseAct p v) := by
    simp [run, List.take_replicate, Nat.min_eq_left hh'.le]
  have hg : (run p v)[h] = sevenPhaseAct p v := by simp [run]
  change wordScore M_seven _ _ j < wordScore M_seven _ _ _
  rw [ht, hg, wordScore_replicate, wordScore_replicate]
  have hv' := phase_run_strict p v hv h hh' j hj'
  simp only [scoreVec_runCount] at hv'
  simpa [scoreVec, mul_comm] using hv'

theorem runs_valid_score (p n : ℕ) (hn : n ≤ sevenPhaseRunCount p) :
    IsValidPriorityWord M_seven (V_seven ((p : ℚ)+20)) (Equiv.refl (Fin 6)) (runs p n) ∧
    wordScore M_seven (V_seven ((p : ℚ)+20)) (runs p n) = sevenPhaseScore p n := by
  induction n with
  | zero =>
      constructor
      · intro r hr; simp [runs, consecutiveWord] at hr
      · simpa [runs, consecutiveWord, wordScore_nil] using (phase_start p).symm
  | succ n ih =>
      have hnp : n < sevenPhaseRunCount p := by omega
      have ih' := ih (by omega)
      have he : runs p (n+1) = runs p n ++ run p n := by simp [runs, consecutiveWord]
      rw [he]
      constructor
      · apply (isValidPriorityWord_append _ _ _ _ _).2
        exact ⟨ih'.1, by rw [ih'.2]; exact run_valid p n hnp⟩
      · rw [wordScore_append, ih'.2, run_score p n hnp]

theorem runs_score (p n : ℕ) (hn : n ≤ sevenPhaseRunCount p) :
    wordScore M_seven (V_seven ((p : ℚ)+20)) (runs p n) = sevenPhaseScore p n :=
  (runs_valid_score p n hn).2

theorem seven_valid (q : ℕ) (hq : 20 ≤ q) :
    IsValidPriorityWord M_seven (R_seven.mulVec (binomBasis 3 q))
      (Equiv.refl (Fin 6)) (sevenWord q) := by
  rw [R_eval]
  have he : ((q-20 : ℕ) : ℚ)+20 = (q : ℚ) := by
    rw [Nat.cast_sub hq]
    norm_num
  simpa only [sevenWord, phaseWord, he] using
    (runs_valid_score (q-20) (sevenPhaseRunCount (q-20)) le_rfl).1

end Karlin.FaithfulSevenData
